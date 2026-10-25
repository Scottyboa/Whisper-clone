import { createManualVADSession } from './manual-vad.mjs?v=20261025-secondary2';
import { wavBlob } from './audio.mjs?v=20261015-clock1';
import { sortSecondaryFiles, validateSecondary, secondaryNames, attachSecondary } from './secondary-sections.mjs?v=20261025-secondary2';

export async function mergeSecondaryRecordings(files, onStatus = () => {}, createSession = createManualVADSession) {
  const items = sortSecondaryFiles(files), parts = [], ranges = [];
  const session = createSession(); let samples = 0;
  try {
    for (const [index, {file}] of items.entries()) {
      const result = await session.prepare(file, text => onStatus(`Secondary rec ${index + 1}/${items.length} · ${file.name} · ${text}`));
      if (result.empty) continue;
      // The shared VAD emits only clean, canonical mono 16 kHz, 16-bit WAVs.
      const header = new Uint8Array(await result.file.slice(0, 44).arrayBuffer());
      const view = new DataView(header.buffer);
      if (header.length !== 44 || new TextDecoder().decode(header.subarray(36, 40)) !== 'data' ||
          view.getUint32(40, true) !== result.file.size - 44 || (result.file.size - 44) % 2 !== 0)
        throw new Error(`VAD returned unreadable audio for ${file.name}.`);
      const count = (result.file.size - 44) / 2;
      if (!count) continue;
      if ((samples + count) * 2 > 0xffffffff - 36) throw new Error('The merged audio is too large for a WAV file. Choose fewer files.');
      ranges.push([samples, count, index]); samples += count;
      // Reuse Blob slices rather than allocating all source PCM in one array.
      parts.push(result.file.slice(44));
    }
    if (!samples) return {empty:true};
    const secondary = validateSecondary({version:2,sampleRate:16000,sources:items.map(item => item.source),ranges}, samples);
    const names = secondaryNames(secondary);
    const header = new Uint8Array(await wavBlob([]).arrayBuffer()), view = new DataView(header.buffer);
    view.setUint32(4, 36 + samples * 2, true); view.setUint32(40, samples * 2, true);
    const clean = new File([header, ...parts], names.wav, {type:'audio/wav'});
    const file = await attachSecondary(clean, secondary);
    onStatus(`Secondary rec · ${items.length} files processed · merged WAV ready`);
    return {file, secondary};
  } finally { session.close(); }
}
