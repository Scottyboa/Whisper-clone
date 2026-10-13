// Adapter for the pinned vad-web 0.0.22 API. No fixed sleep is used to
// infer completion: capture acknowledges its last frame, then inference
// drains in order, then pause emits the final speech segment.
export async function createDrainableSonioxVAD(factory, options) {
  let disposed = false;
  const guarded = { ...options };
  for (const name of ['onSpeechStart', 'onSpeechEnd', 'onVADMisfire', 'onFrameProcessed']) {
    guarded[name] = (...args) => { if (!disposed) return options[name]?.(...args); };
  }
  const mic = await factory.new(guarded);
  const node = mic.audioNodeVAD;
  let tail = Promise.resolve();
  let frameError = null;
  let drainPromise = null;
  const originalDestroy = mic.destroy.bind(mic);
  mic.destroy = () => { disposed = true; return originalDestroy(); };

  try {
    if (!node?.processFrame || !node.frameProcessor || !mic.audioContext) {
      throw new Error('Unsupported Silero VAD version; safe pause cannot be installed.');
    }
    const processFrame = node.processFrame.bind(node);
    node.processFrame = (frame) => {
      const work = tail.then(() => {
        if (!disposed) return processFrame(frame);
      });
      // Observe failures immediately, without unhandled promise rejections.
      tail = work.catch(error => { frameError ||= error; });
      return tail;
    };

    let stopCapture;
    const oldNode = node.audioNode;
    if (oldNode?.port) {
      await mic.audioContext.audioWorklet.addModule(
        new URL('./soniox-vad-worklet.js', import.meta.url).href
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
        if (data?.message === 'AUDIO_FRAME') node.processFrame(new Float32Array(data.data));
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
      oldNode.onaudioprocess = event => {
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
