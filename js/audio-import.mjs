import { prepareAudio as prepareWav } from './wav-timing.mjs?v=20261015-clock1';
import { runFlacTask } from './flac-tasks.mjs?v=20261017-flac2';

export async function prepareAudio(file, progress = () => {}) {
  try {
    if (file.size >= 4 && new TextDecoder().decode(await file.slice(0, 4).arrayBuffer()) === 'fLaC') {
      return await runFlacTask('prepare', file, progress);
    }
  } catch (error) {
    // A worker failure must not silently turn a compact import into a costly
    // full-duration upload. Malformed/ordinary files are handled inside the parser.
    if (typeof Worker !== 'undefined') throw error;
  }
  return prepareWav(file);
}
