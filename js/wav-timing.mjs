// A private RIFF chunk keeps the original capture timeline with downloaded WAVs.
// It is removed before provider upload; the provider receives ordinary audio.
export const TIMING_CHUNK = 'wctm';
export const MAX_TIMING_BYTES = 2 * 1024 * 1024;
const fourCC = (view, offset) => String.fromCharCode(...new Uint8Array(view.buffer, view.byteOffset + offset, 4));

export function validateTiming(value, samples) {
  if (value?.version !== 1 || value.sampleRate !== 16000 || !Number.isSafeInteger(samples) || samples <= 0 ||
      typeof value.timeZone !== 'string' || !Array.isArray(value.segments) || !value.segments.length || value.segments.length > 50000) return null;
  try { new Intl.DateTimeFormat('en-GB', { timeZone: value.timeZone }).format(0); } catch { return null; }
  let offset = 0, previousTime = -Infinity;
  const segments = [];
  for (const segment of value.segments) {
    if (!Array.isArray(segment) || segment.length !== 3) return null;
    const [start, length, epoch] = segment;
    if (start !== offset || !Number.isSafeInteger(length) || length <= 0 ||
        !Number.isFinite(epoch) || epoch <= 0 || epoch > 8640000000000000 - length / 16 || epoch < previousTime) return null;
    segments.push([start, length, epoch]); offset += length; previousTime = epoch;
    if (offset > samples) return null;
  }
  return offset === samples ? { version: 1, sampleRate: 16000, timeZone: value.timeZone, segments } : null;
}

export function timingChunk(timing, samples) {
  const valid = validateTiming(timing, samples);
  if (!valid) return null;
  const bytes = new TextEncoder().encode(JSON.stringify(valid));
  if (bytes.length > MAX_TIMING_BYTES) return null;
  const result = new Uint8Array(8 + bytes.length + (bytes.length % 2));
  result.set(new TextEncoder().encode(TIMING_CHUNK));
  new DataView(result.buffer).setUint32(4, bytes.length, true); result.set(bytes, 8);
  return result;
}

export function clockAt(timing, milliseconds) {
  if (!timing || !Number.isFinite(milliseconds) || milliseconds < 0) return null;
  const sample = milliseconds * timing.sampleRate / 1000;
  // A token at a join belongs to the next retained segment, not the silence gap.
  let lo = 0, hi = timing.segments.length - 1;
  while (lo <= hi) {
    const mid = (lo + hi) >> 1, [start, length, epoch] = timing.segments[mid];
    if (sample < start) hi = mid - 1;
    else if (sample >= start + length) lo = mid + 1;
    else return epoch + (sample - start) / timing.sampleRate * 1000;
  }
  return null;
}

export function clockLabel(timing, milliseconds) {
  const epoch = clockAt(timing, milliseconds);
  if (epoch == null) return '';
  return new Intl.DateTimeFormat('en-GB', { timeZone: timing.timeZone, hour: '2-digit', minute: '2-digit', second: '2-digit', hourCycle: 'h23' }).format(epoch);
}

export async function prepareAudio(file) {
  const original = { file, timing: null };
  try {
    if (file.size < 12) return original;
    const head = new DataView(await file.slice(0, 12).arrayBuffer());
    if (fourCC(head, 0) !== 'RIFF' || fourCC(head, 8) !== 'WAVE') return original;
    const end = head.getUint32(4, true) + 8;
    if (end !== file.size) return original;
    let offset = 12, format = null, audioBytes = null, encoded = null, timingCount = 0, chunks = 0;
    const keep = [];
    while (offset + 8 <= end && ++chunks <= 4096) {
      const header = new DataView(await file.slice(offset, offset + 8).arrayBuffer());
      const id = fourCC(header, 0), size = header.getUint32(4, true), next = offset + 8 + size + size % 2;
      if (next > end) return original;
      if (id === TIMING_CHUNK) {
        timingCount++;
        if (size <= MAX_TIMING_BYTES) encoded = await file.slice(offset + 8, offset + 8 + size).text();
      } else {
        keep.push(file.slice(offset, next));
        if (id === 'fmt ' && size >= 16) format = new DataView(await file.slice(offset + 8, offset + 24).arrayBuffer());
        if (id === 'data') audioBytes = audioBytes == null ? size : NaN;
      }
      offset = next;
    }
    if (offset !== end || !timingCount) return original;
    // Ignore invalid/unknown timing metadata, while still sending a clean WAV.
    let timing = null;
    if (timingCount === 1 && encoded && format?.getUint16(0, true) === 1 &&
        format.getUint16(2, true) === 1 && format.getUint32(4, true) === 16000 && format.getUint16(14, true) === 16 && audioBytes % 2 === 0) {
      try { timing = validateTiming(JSON.parse(encoded), audioBytes / 2); } catch {}
    }
    const payload = new Blob(keep), prefix = new Uint8Array(await file.slice(0, 12).arrayBuffer());
    new DataView(prefix.buffer).setUint32(4, payload.size + 4, true);
    return { file: new File([prefix, payload], file.name || 'recording.wav', { type: 'audio/wav' }), timing };
  } catch { return original; }
}
