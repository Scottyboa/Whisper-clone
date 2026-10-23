import { prepareAudio } from './audio-import.mjs?v=20261017-flac2';

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

function runVAD(prepared, progress) {
  if (typeof Worker === 'undefined') throw new Error('Audio preparation requires a browser with Web Worker support.');
  return new Promise((resolve, reject) => {
    const worker = new Worker(new URL('./manual-vad-worker.mjs?v=20261023-upload1', import.meta.url), { type: 'module' });
    let finished = false;
    const finish = (error, result) => {
      if (finished) return; finished = true; active.delete(worker); worker.terminate();
      error ? reject(error) : resolve(result);
    };
    active.set(worker, () => finish(new Error('Audio preparation cancelled.')));
    worker.onerror = () => finish(new Error('The VAD worker could not run. Nothing was uploaded.'));
    worker.onmessageerror = () => finish(new Error('The VAD result could not be read. Nothing was uploaded.'));
    worker.onmessage = async ({ data }) => {
      if (data.decodeNative) {
        try {
          const nativeAudio = await decodeNative(prepared.file);
          if (!finished) worker.postMessage({ nativeAudio }, nativeAudio.channelData.map(channel => channel.buffer));
        } catch (error) { finish(error); }
      } else if (typeof data.progress === 'number') progress(data.progress);
      else finish(data.error ? new Error(data.error) : null, data.result);
    };
    try { worker.postMessage({ prepared }); } catch (error) { finish(error); }
  });
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
