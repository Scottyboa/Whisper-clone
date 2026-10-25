import { prepareAudio } from './audio-import.mjs?v=20261025-secondary1';

const active = new Map();
async function decodeNative(file) {
  const Context = globalThis.OfflineAudioContext || globalThis.webkitOfflineAudioContext;
  if (!Context) throw new Error('This browser cannot decode this audio format. Use WAV or FLAC.');
  const context = new Context(1, 1, 16000);
  let buffer;
  try { buffer = await context.decodeAudioData(await file.arrayBuffer()); }
  catch { throw new Error('This audio file could not be decoded. Nothing was uploaded.'); }
  return { sampleRate: buffer.sampleRate,
    channelData: Array.from({ length: buffer.numberOfChannels }, (_, i) => buffer.getChannelData(i).slice()) };
}

function createVADRunner() {
  if (typeof Worker === 'undefined') throw new Error('Audio preparation requires a browser with Web Worker support.');
  const worker = new Worker(new URL('./manual-vad-worker.mjs?v=20261025-secondary1', import.meta.url), {type:'module'});
  let pending = null, closed = false;
  const finish = (error, result) => {
    const job = pending; pending = null;
    if (job) error ? job.reject(error) : job.resolve(result);
  };
  const close = (error = new Error('Audio preparation cancelled.')) => {
    if (closed) return; closed = true; active.delete(worker); worker.terminate(); finish(error);
  };
  active.set(worker, close);
  worker.onerror = () => close(new Error('The VAD worker could not run. Nothing was uploaded.'));
  worker.onmessageerror = () => close(new Error('The VAD result could not be read. Nothing was uploaded.'));
  worker.onmessage = async ({data}) => {
    const job = pending;
    if (!job || closed) return;
    if (data.decodeNative) {
      try {
        const nativeAudio = await decodeNative(job.prepared.file);
        if (!closed && pending === job) worker.postMessage({nativeAudio}, nativeAudio.channelData.map(channel => channel.buffer));
      } catch (error) { finish(error); }
    } else if (typeof data.progress === 'number') job.progress(data.progress);
    else finish(data.error ? new Error(data.error) : null, data.result);
  };
  return {
    run(prepared, progress) {
      if (closed) return Promise.reject(new Error('Audio preparation cancelled.'));
      if (pending) return Promise.reject(new Error('Audio preparation is already running.'));
      return new Promise((resolve, reject) => {
        pending = {prepared, progress, resolve, reject};
        try { worker.postMessage({prepared}); } catch (error) { finish(error); }
      });
    }, close,
  };
}
async function runVAD(prepared, progress) {
  const runner = createVADRunner();
  try { return await runner.run(prepared, progress); }
  finally { runner.close(); }
}
// A batch loads one model, resets inference state between source files, and
// releases the worker on success, failure or page close.
export function createManualVADSession() {
  const runner = createVADRunner();
  return {prepare:(file, status) => prepareManualAudio(file, status, runner.run), close:runner.close};
}

export async function prepareManualAudio(file, onStatus = () => {}, run = runVAD) {
  onStatus('Reading recording metadata…');
  const prepared = await prepareAudio(file, value => onStatus(`Reading recording metadata… ${Math.round(value * 100)}%`));
  if (prepared.empty) return prepared;
  onStatus('Loading speech detector…');
  const result = await run(prepared, value => onStatus(`Detecting speech… ${Math.round(value * 100)}%`));
  if (!result?.empty && (!result?.file || result.file.type !== 'audio/wav')) throw new Error('VAD did not produce readable audio. Nothing was uploaded.');
  return result;
}

export function cancelManualVAD() { for (const cancel of [...active.values()]) cancel(); }
