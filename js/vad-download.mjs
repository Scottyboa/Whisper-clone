import { attachSecondary } from './secondary-sections.mjs?v=20261025-secondary1';
import { timingChunk } from './wav-timing.mjs?v=20261015-clock1';

// Manual VAD returns a clean provider WAV plus its separately composed clock
// map. Keep that map in downloaded WAVs so reimport can still label clock times.
export async function vadDownloadFile({ file, timing, secondary }) {
  const name = (file.name || 'audio.wav').replace(/\.[^.]*$/, '') + '-VAD.wav';
  if (!timing) {
    const result = new File([file], name, {type:'audio/wav'});
    return secondary ? attachSecondary(result, secondary) : result;
  }
  const header = new Uint8Array(await file.slice(0, 44).arrayBuffer());
  const view = new DataView(header.buffer);
  const id = at => new TextDecoder().decode(header.subarray(at, at + 4));
  if (header.length !== 44 || id(0) !== 'RIFF' || id(8) !== 'WAVE' || id(12) !== 'fmt ' ||
      view.getUint32(16, true) !== 16 || view.getUint16(20, true) !== 1 ||
      view.getUint16(22, true) !== 1 || view.getUint32(24, true) !== 16000 ||
      view.getUint16(34, true) !== 16 || id(36) !== 'data' ||
      view.getUint32(40, true) !== file.size - 44 || view.getUint32(4, true) !== file.size - 8)
    throw new Error('The VAD WAV could not be read.');
  const metadata = timingChunk(timing, (file.size - 44) / 2);
  if (!metadata) throw new Error('Original recording timestamps could not be saved.');
  const size = file.size + metadata.length;
  if (size - 8 > 0xffffffff) throw new Error('The processed audio is too large for a WAV file.');
  view.setUint32(4, size - 8, true);
  // Blob slices avoid copying a long recording into a second PCM buffer.
  const result = new File([header, file.slice(44), metadata], name, {type:'audio/wav'});
  return secondary ? attachSecondary(result, secondary, (file.size - 44) / 2) : result;
}
