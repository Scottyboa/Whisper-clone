import { encodeTimelineFlac, prepareTimelineFlac } from './timeline-flac.mjs?v=20261017-flac2';

const active = new Map();
export function runFlacTask(action, input, onProgress = () => {}) {
  if (typeof Worker === 'undefined') return action === 'encode' ? encodeTimelineFlac(input, onProgress) : prepareTimelineFlac(input, onProgress);
  return new Promise((resolve, reject) => {
    const worker = new Worker(new URL('./flac-worker.mjs?v=20261017-flac2', import.meta.url), { type: 'module' });
    const finish = (error, result) => {
      active.delete(worker); worker.terminate();
      if (error) reject(error); else resolve(result);
    };
    active.set(worker, () => finish(new Error('Audio processing cancelled.')));
    worker.onerror = () => finish(new Error('Audio processing worker failed.'));
    worker.onmessageerror = () => finish(new Error('Audio processing response could not be read.'));
    worker.onmessage = ({ data }) => {
      if (typeof data.progress === 'number') onProgress(data.progress);
      else finish(data.error ? new Error(data.error) : null, data.result);
    };
    try { worker.postMessage({ action, input }); } catch (error) { finish(error); }
  });
}
export function cancelFlacTasks() { for (const cancel of [...active.values()]) cancel(); }
