import { CaptureTiming } from './capture-timing.mjs?v=20261015-clock1';

// Adapter for the pinned vad-web 0.0.22 API. No fixed sleep is used to
// infer completion: capture acknowledges its last frame, then inference
// drains in order, then pause emits the final speech segment.
export async function createDrainableSonioxVAD(factory, options) {
  let disposed = false, monitoring = true, frameEpoch = NaN;
  const timing = new CaptureTiming(), frameTimes = new WeakMap();
  const guarded = { ...options };
  for (const name of ['onSpeechStart', 'onSpeechEnd', 'onVADMisfire', 'onFrameProcessed']) {
    guarded[name] = (...args) => { if (!disposed) return options[name]?.(...args); };
  }
  guarded.onFrameProcessed = (probs, frame) => {
    if (disposed) return;
    timing.add(frame.length, frameEpoch);
    return options.onFrameProcessed?.(probs, frame);
  };
  guarded.onSpeechEnd = audio => {
    if (!disposed) return options.onSpeechEnd?.(audio, timing.speech(audio.length));
  };
  const mic = await factory.new(guarded);
  // Anchor AudioContext time once. Inference and delayed UI callbacks cannot
  // move the original capture timestamp of a frame.
  const audioEpoch = (options.captureNow || Date.now)() - mic.audioContext.currentTime * 1000;
  const node = mic.audioNodeVAD;
  let tail = Promise.resolve();
  let frameError = null;
  let drainPromise = null;
  const originalDestroy = mic.destroy.bind(mic);
  mic.destroy = () => { disposed = true; return originalDestroy(); };
  const observeInput = frame => {
    if (!disposed && monitoring) options.onInputFrame?.(frame);
  };

  try {
    if (!node?.processFrame || !node.frameProcessor || !mic.audioContext) {
      throw new Error('Unsupported Silero VAD version; safe pause cannot be installed.');
    }
    const processFrame = node.processFrame.bind(node);
    node.processFrame = (frame, capturedAt = frameTimes.get(frame)) => {
      const work = tail.then(async () => {
        if (disposed) return;
        frameEpoch = capturedAt;
        await processFrame(frame);
        timing.retain(node.frameProcessor.audioBuffer?.length || 0);
      });
      // Observe failures immediately, without unhandled promise rejections.
      tail = work.catch(error => { frameError ||= error; });
      return tail;
    };

    let stopCapture;
    const oldNode = node.audioNode;
    if (oldNode?.port) {
      await mic.audioContext.audioWorklet.addModule(
        new URL('./soniox-vad-worklet.js?v=20261015-clock1', import.meta.url).href
      );
      const capture = new AudioWorkletNode(mic.audioContext, 'soniox-batch-capture', {
        processorOptions: { frameSamples: node.frameProcessor.options.frameSamples },
      });
      let acknowledge;
      let rejectCapture;
      const acknowledged = new Promise((resolve, reject) => {
        acknowledge = resolve;
        rejectCapture = reject;
      });
      // A processor error before Pause must also be observed immediately.
      acknowledged.catch(() => {});
      capture.onprocessorerror = () => rejectCapture(new Error('Audio capture processor failed.'));
      capture.port.onmessage = ({ data }) => {
        if (disposed) return;
        if (data?.message === 'AUDIO_FRAME') {
          const frame = new Float32Array(data.data);
          // Observe delivery before the inference queue. Delayed VAD results
          // must never make old sound look like newly arriving sound.
          observeInput(frame);
          node.processFrame(frame, Number.isFinite(data.audioTime) ? audioEpoch + data.audioTime * 1000 : NaN);
        }
        else if (data?.message === 'SONIOX_DRAINED') acknowledge();
      };
      mic.sourceNode.disconnect();
      oldNode.port.onmessage = null;
      oldNode.port.postMessage({ message: 'SPEECH_STOP' });
      oldNode.disconnect();
      node.audioNode = capture;
      mic.sourceNode.connect(capture);
      stopCapture = async () => {
        capture.port.postMessage({ message: 'SONIOX_DRAIN' });
        await acknowledged; // FIFO: every pre-drain audio message is now queued.
      };
    } else {
      // ScriptProcessor fallback: wait for the *whole* resampling callback,
      // including frames it schedules after awaiting earlier inference.
      const callback = oldNode?.onaudioprocess;
      if (typeof callback !== 'function') throw new Error('Unsupported VAD audio capture.');
      const callbacks = new Set();
      let inputEpoch = NaN, bufferedEpoch = NaN;
      const resampler = node.resampler;
      if (resampler) {
        const resample = resampler.process.bind(resampler);
        resampler.process = input => {
          const buffered = resampler.inputBuffer.length;
          const first = buffered && Number.isFinite(bufferedEpoch) ? bufferedEpoch : inputEpoch;
          const frames = resample(input);
          const rate = resampler.options.nativeSampleRate;
          let consumed = 0;
          for (const frame of frames) {
            const epoch = consumed < buffered ? first + consumed / rate * 1000 : inputEpoch + (consumed - buffered) / rate * 1000;
            frameTimes.set(frame, epoch);
            consumed += Math.ceil(frame.length * rate / 16000);
          }
          bufferedEpoch = consumed < buffered ? first + consumed / rate * 1000 : inputEpoch + (consumed - buffered) / rate * 1000;
          return frames;
        };
      }
      oldNode.onaudioprocess = event => {
        observeInput(event.inputBuffer.getChannelData(0));
        // ScriptProcessor can skip a busy callback. Timestamp each input buffer
        // independently so a skipped buffer does not shift the remaining audio.
        inputEpoch = audioEpoch + (mic.audioContext.currentTime - event.inputBuffer.duration) * 1000;
        const work = Promise.resolve(callback(event));
        callbacks.add(work);
        work.then(() => callbacks.delete(work), error => {
          frameError ||= error;
          callbacks.delete(work);
        });
      };
      stopCapture = async () => {
        await mic.audioContext.suspend();
        oldNode.onaudioprocess = null;
        await Promise.all([...callbacks]);
        const resampler = node.resampler;
        if (resampler?.inputBuffer?.length) {
          const required = Math.ceil(resampler.options.targetFrameSize *
            resampler.options.nativeSampleRate / resampler.options.targetSampleRate);
          const padding = new Float32Array(Math.max(0, required - resampler.inputBuffer.length));
          for (const frame of resampler.process(padding)) node.processFrame(frame);
        }
      };
    }

    mic.drainAndPause = () => {
      if (!drainPromise) {
        // Final drain/padding belongs to the completed capture, not new sound.
        monitoring = false;
        drainPromise = (async () => {
          // End microphone capture now; leave the graph/model alive to drain.
          mic.stream.getTracks().forEach(track => track.stop());
          await stopCapture();
          await tail;
          if (disposed) throw new Error('Recording was cancelled while pausing.');
          if (frameError) throw frameError;
          mic.pause(); // Synchronous onSpeechEnd, AFTER the last inference.
          mic.sourceNode.disconnect();
        })();
      }
      return drainPromise;
    };
    return mic;
  } catch (error) {
    mic.destroy();
    throw error;
  }
}
