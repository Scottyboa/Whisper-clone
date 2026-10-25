import { retainedSecondary } from './secondary-sections.mjs?v=20261025-secondary1';
import { SAMPLE_RATE, VAD_RULES, toPCM, wavBlob } from './audio.mjs?v=20261015-clock1';
import { validateTiming } from './wav-timing.mjs?v=20261015-clock1';

// Streaming box resampling follows the averaging used by the pinned live VAD.
// Preserve fractional sample positions across decoder chunks, including 44.1 kHz.
export async function* vadFrames(chunks) {
  const size = VAD_RULES.frameSamples;
  let frame = new Float32Array(size), used = 0, total = 0, sampleRate;
  let weight = 0, sum = 0;
  for await (const chunk of chunks) {
    if (!Number.isFinite(chunk.sampleRate) || chunk.sampleRate < 1000 || chunk.sampleRate > 384000 ||
        !chunk.channelData?.length || chunk.channelData.some(ch => ch.length !== chunk.channelData[0].length))
      throw new Error('The decoded audio format is invalid.');
    sampleRate ??= chunk.sampleRate;
    if (sampleRate !== chunk.sampleRate) throw new Error('The audio sample rate changed.');
    const ratio = sampleRate / SAMPLE_RATE;
    for (let i = 0; i < chunk.channelData[0].length; i++) {
      let value = 0;
      for (const channel of chunk.channelData) value += channel[i] / chunk.channelData.length;
      if (!Number.isFinite(value)) throw new Error('The file contains invalid audio samples.');
      let left = 1;
      while (left > 1e-9) {
        const take = Math.min(left, ratio - weight);
        sum += value * take; weight += take; left -= take;
        if (weight >= ratio - 1e-9) {
          frame[used++] = sum / ratio; total++; weight = 0; sum = 0;
          if (used === size) { yield { frame, valid: size, total, progress: chunk.progress }; frame = new Float32Array(size); used = 0; }
        }
      }
    }
  }
  // Retain the last fractional sample instead of dropping a quiet final word.
  if (weight > 1e-9) {
    frame[used++] = sum / weight; total++;
    if (used === size) { yield { frame, valid: size, total, progress: 1 }; used = 0; }
  }
  if (used) yield { frame, valid: used, total, progress: 1 };
}

export function retainedTiming(timing, ranges, keptSamples) {
  if (!timing) return null;
  const segments = []; let offset = 0, index = 0;
  for (const [start, length] of ranges) {
    const end = start + length;
    while (index < timing.segments.length && timing.segments[index][0] + timing.segments[index][1] <= start) index++;
    for (let i = index; i < timing.segments.length && timing.segments[i][0] < end; i++) {
      const [at, size, epoch] = timing.segments[i], first = Math.max(start, at), count = Math.min(end, at + size) - first;
      if (count > 0) { segments.push([offset, count, epoch + (first - at) / 16]); offset += count; }
    }
  }
  const result = validateTiming({ ...timing, segments }, keptSamples);
  if (!result) throw new Error('Original recording timestamps could not be preserved.');
  return result;
}

export async function trimDecodedAudio({ file, timing, secondary }, chunks, processor, progress = () => {}) {
  const parts = [], ranges = []; let cursor = 0, valid = 0, kept = 0, reported = -1;
  const retain = event => {
    if (event.msg !== 'SPEECH_END' || !event.audio?.length) return;
    const start = cursor - event.audio.length, end = Math.min(cursor, valid), count = end - start;
    if (start < 0 || start < (ranges.at(-1)?.[0] || 0) + (ranges.at(-1)?.[1] || 0)) throw new Error('VAD returned invalid speech boundaries.');
    if (count <= 0) return;
    ranges.push([start, count]); parts.push(toPCM(event.audio.subarray(0, count))); kept += count;
  };
  try {
    for await (const item of vadFrames(chunks)) {
      cursor += item.frame.length; valid = item.total;
      retain(await processor.process(item.frame));
      const percent = Math.floor(item.progress * 100);
      if (percent !== reported) { reported = percent; progress(Math.min(.99, item.progress)); }
    }
    retain(processor.endSegment());
    if (!kept) return { file: null, timing: null, empty: true };
    const map = retainedTiming(timing, ranges, kept);
    const result = new File([wavBlob(parts)], (file.name || 'audio').replace(/\.[^.]*$/, '') + '.wav', { type: 'audio/wav' });
    progress(1);
    return { file: result, timing: map, ...(secondary ? {secondary:retainedSecondary(secondary, ranges, kept)} : {}) };
  } finally { processor.reset(); }
}
