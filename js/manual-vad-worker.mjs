import { VAD_RULES } from './audio.mjs?v=20261015-clock1';
import { decodeFileChunks, decodedChunks } from './file-audio.mjs?v=20261023-upload1';
import { trimDecodedAudio } from './file-vad.mjs?v=20261023-upload1';

let nativeResolve, nativeReject;
self.onmessage = async ({ data }) => {
  if (data.nativeAudio || data.nativeError) {
    if (data.nativeError) nativeReject?.(new Error(data.nativeError));
    else nativeResolve?.(data.nativeAudio);
    return;
  }
  try {
    await import('../vendor/ort/ort.min.js');
    await import('../vendor/vad/bundle.min.js');
    const model = await self.vad.NonRealTimeVAD.new({ ...VAD_RULES,
      modelURL: new URL('../vendor/vad/silero_vad_legacy.onnx', import.meta.url).href,
      ortConfig: ort => {
        ort.env.wasm.wasmPaths = new URL('../vendor/ort/', import.meta.url).href;
        ort.env.wasm.numThreads = 1;
      },
    });
    const decodeOther = () => new Promise((resolve, reject) => {
      nativeResolve = resolve; nativeReject = reject; self.postMessage({ decodeNative: true });
    });
    const chunks = decodeFileChunks(data.prepared.file, {
      flacDecoder: async () => {
        const { FLACDecoder } = await import('../vendor/flac/flac-decoder.min.mjs');
        const decoder = new FLACDecoder(); await decoder.ready; return decoder;
      },
      decodeOther,
    });
    const progress = value => self.postMessage({ progress: value });
    let result;
    try { result = await trimDecodedAudio(data.prepared, chunks, model.frameProcessor, progress); }
    catch (error) {
      // Bound native fallback allocations on unusual FLACs. Long files keep the
      // streaming path or fail before upload; a decoder failure never sends raw audio.
      if (!error.nativeExpected || error.nativeExpected > 32000000) throw error;
      const native = await decodeOther();
      if (native.sampleRate !== 16000 || native.channelData.some(ch => Math.abs(ch.length - error.nativeExpected) > 1)) throw error;
      model.frameProcessor.resume();
      result = await trimDecodedAudio(data.prepared, decodedChunks(native), model.frameProcessor, progress);
    }
    self.postMessage({ result });
  } catch (error) { self.postMessage({ error: error.message || 'Audio preparation failed.' }); }
};
