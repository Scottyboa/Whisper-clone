import { wavFormat } from './file-audio.mjs?v=20261023-upload1';

export const AUDIO_ENHANCEMENT = Object.freeze({ highPassHz:70, maxGain:2, peak:10 ** (-3 / 20) });
const CHUNK_BYTES = 131072;

// The same non-resonant Butterworth high-pass as Web Audio's highpass at
// 70 Hz with Q = -3.0103 dB. State persists across every file chunk.
export function createSpeechFilter(rate, channels) {
  const w = 2 * Math.PI * AUDIO_ENHANCEMENT.highPassHz / rate;
  const cos = Math.cos(w), alpha = Math.sin(w) / (2 * Math.SQRT1_2), a0 = 1 + alpha;
  const b0 = (1 + cos) / (2 * a0), b1 = -(1 + cos) / a0, b2 = b0;
  const a1 = -2 * cos / a0, a2 = (1 - alpha) / a0;
  const z1 = new Float64Array(channels), z2 = new Float64Array(channels);
  return (sample, channel) => {
    const value = b0 * sample + z1[channel];
    z1[channel] = b1 * sample - a1 * value + z2[channel];
    z2[channel] = b2 * sample - a2 * value;
    return value;
  };
}

// All app VAD outputs are PCM16 WAV. Process with bounded reads instead of
// decoding hours of audio into an AudioBuffer. Preserve every non-audio byte,
// including original clocks and Secondary rec source ranges.
export async function enhanceAudioFile(file, onStatus = () => {}, {enabled = true, signal} = {}) {
  if (!enabled) return file;
  signal?.throwIfAborted();
  const format = await wavFormat(file);
  if (!format || format.encoding !== 1 || format.bits !== 16)
    throw new Error('Audio enhancement requires a VAD-processed PCM16 WAV. Nothing was uploaded.');
  const {start, size, channels, sampleRate, align} = format;
  const chunkBytes = Math.max(align, Math.floor(CHUNK_BYTES / align) * align);
  const parts = []; let peak = 0, gain = 1;
  for (let pass = 0; pass < 2; pass++) {
    const filter = createSpeechFilter(sampleRate, channels);
    let chunks = 0;
    for (let at = 0; at < size; at += chunkBytes) {
      signal?.throwIfAborted();
      const data = new DataView(await file.slice(start + at, start + Math.min(size, at + chunkBytes)).arrayBuffer());
      const output = pass ? new DataView(new ArrayBuffer(data.byteLength)) : null;
      for (let byte = 0; byte < data.byteLength; byte += 2) {
        const value = filter(data.getInt16(byte, true) / 32768, byte / 2 % channels);
        if (!pass) peak = Math.max(peak, Math.abs(value));
        else {
          const sample = Math.max(-1, Math.min(1, value * gain));
          output.setInt16(byte, Math.round(sample * (sample < 0 ? 32768 : 32767)), true);
        }
      }
      if (output) parts.push(new Blob([output.buffer]));
      onStatus(`Enhancing audio… ${Math.floor((pass + (at + data.byteLength) / size) * 50)}%`);
      // Yield to recording commands, painting and page-close cancellation.
      if (++chunks % 8 === 0) await new Promise(resolve => setTimeout(resolve, 0));
    }
    if (!pass) gain = peak ? Math.min(AUDIO_ENHANCEMENT.maxGain, AUDIO_ENHANCEMENT.peak / peak) : 1;
  }
  signal?.throwIfAborted();
  onStatus('Audio enhancement complete');
  return new File([file.slice(0, start), ...parts, file.slice(start + size)], file.name || 'audio.wav',
    {type:'audio/wav',lastModified:file.lastModified ?? Date.now()});
}
