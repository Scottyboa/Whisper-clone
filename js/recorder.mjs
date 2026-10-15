import { createDrainableSonioxVAD } from './soniox-vad-drain.mjs?v=20261015-clock1';
import { VAD_RULES, SAMPLE_RATE, toPCM, wavBlob } from './audio.mjs?v=20261015-clock1';

export class Recorder {
  constructor({ onChange = () => {}, now = Date.now, createVAD } = {}) {
    this.onChange = onChange; this.now = now;
    this.createVAD = createVAD || (options => this.makeVAD(options));
    this.state = 'idle'; this.parts = []; this.samples = 0;
    this.startedAt = null; this.context = null; this.mic = null;
    this.acceptingAudio = false; this.disposed = false;
    this.queue = Promise.resolve();
    this.timingSegments = []; this.timingValid = true; this.discardGeneration = 0;
  }

  // Called synchronously by Start/Link, while the user's click can unlock audio.
  unlock() {
    if (this.disposed) throw new Error('This page is closing.');
    if (!this.context || this.context.state === 'closed') this.context = new AudioContext();
    return this.context.resume();
  }

  async makeVAD(options) {
    if (!globalThis.vad?.AudioNodeVAD) throw new Error('Audio model could not be loaded. Reload the page.');
    if (!navigator.mediaDevices?.getUserMedia) throw new Error('Microphone access requires HTTPS.');
    if (!this.context) throw new Error('Click Link or Start on this computer first.');
    await this.context.resume();
    if (this.context.state !== 'running') throw new Error('Click Start on this computer to enable audio.');
    const stream = await navigator.mediaDevices.getUserMedia({ audio: {
      channelCount: 1, echoCancellation: true, autoGainControl: true, noiseSuppression: true,
    } });
    let source, node;
    const context = this.context;
    try {
      if (this.disposed) throw new Error('This page is closing.');
      // Use the same pinned AudioNodeVAD and Azure drain adapter. Reuse the
      // user-unlocked context so later email commands can start capture.
      const factory = { new: async guarded => {
        source = context.createMediaStreamSource(stream);
        node = await vad.AudioNodeVAD.new(context, guarded);
        node.receive(source);
        return {
          stream, audioContext: context, audioNodeVAD: node, sourceNode: source,
          start: () => node.start(), pause: () => node.pause(),
          destroy: () => { source.disconnect(); node.destroy(); stream.getTracks().forEach(track => track.stop()); },
        };
      } };
      const mic = await createDrainableSonioxVAD(factory, {
        ...options, stream,
        baseAssetPath: new URL('../vendor/vad/', import.meta.url).href,
        onnxWASMBasePath: new URL('../vendor/ort/', import.meta.url).href,
        ortConfig: ort => { ort.env.wasm.numThreads = 1; },
      });
      if (this.disposed) { mic.destroy(); throw new Error('This page is closing.'); }
      mic.start();
      if (!stream.getAudioTracks().some(track => track.readyState === 'live')) {
        mic.destroy(); throw new Error('Microphone is unavailable.');
      }
      return mic;
    } catch (error) {
      stream.getTracks().forEach(track => track.stop());
      try { source?.disconnect(); node?.destroy(); } catch {}
      throw error;
    }
  }

  setState(value) { this.state = value; this.onChange(this); }
  command(action) {
    if (action === 'abort') {
      // Invalidate an in-flight Start/Stop immediately, before its queued Abort.
      this.discardGeneration++; this.acceptingAudio = false;
      this.mic?.stream?.getTracks().forEach(track => track.stop());
    }
    const generation = this.discardGeneration;
    const job = this.queue.then(() => this.perform(action, generation));
    this.queue = job.catch(() => {});
    return job;
  }
  async beginCapture() {
    const generation = this.discardGeneration;
    this.acceptingAudio = true;
    this.mic = await this.createVAD({
      ...VAD_RULES, captureNow: this.now,
      onSpeechStart: () => {}, onVADMisfire: () => {},
      onFrameProcessed: () => {},
      onSpeechEnd: (audio, timing) => {
        if (!this.acceptingAudio || this.disposed || generation !== this.discardGeneration || !audio.length) return;
        if (Array.isArray(timing) && timing.length) {
          for (const [offset, length, epoch] of timing) this.timingSegments.push([this.samples + offset, length, epoch]);
        } else this.timingValid = false;
        this.parts.push(toPCM(audio)); this.samples += audio.length;
      },
    });
  }
  async secureTail() {
    if (!this.mic) return;
    // Continue accepting the final speech callback until capture and inference
    // are acknowledged. Do not discard the tail on Pause or Stop.
    if (!this.mic.drainAndPause) throw new Error('Safe audio drain is unavailable.');
    await this.mic.drainAndPause();
    this.acceptingAudio = false;
    await this.mic.destroy();
    this.mic = null;
  }
  async perform(action, generation = this.discardGeneration) {
    if (this.disposed) throw new Error('This page is closing.');
    if (action !== 'abort' && generation !== this.discardGeneration) return;
    if (action === 'abort') {
      this.setState('aborting'); this.acceptingAudio = false;
      try {
        this.mic?.stream?.getTracks().forEach(track => track.stop());
        await this.mic?.destroy();
      } finally {
        this.mic = null; this.parts = []; this.samples = 0; this.startedAt = null;
        this.timingSegments = []; this.timingValid = true; this.setState('idle');
      }
      return;
    }
    if (action === 'start') {
      if (this.state !== 'idle') return;
      this.parts = []; this.samples = 0; this.startedAt = null;
      this.timingSegments = []; this.timingValid = true;
      this.timeZone = Intl.DateTimeFormat().resolvedOptions().timeZone;
      this.setState('starting');
      try {
        await this.beginCapture();
        if (generation !== this.discardGeneration) return;
        this.startedAt = this.now(); this.setState('recording');
      } catch (error) {
        this.acceptingAudio = false;
        if (generation !== this.discardGeneration) return;
        this.setState('idle'); throw error;
      }
      return;
    }
    if (action === 'pause') {
      if (this.state !== 'recording') return;
      this.setState('pausing');
      try { await this.secureTail(); if (generation === this.discardGeneration) this.setState('paused'); }
      catch (error) { if (generation !== this.discardGeneration) return; this.setState('error'); throw error; }
      return;
    }
    if (action === 'resume') {
      if (this.state !== 'paused') return;
      this.setState('resuming');
      try { await this.beginCapture(); if (generation === this.discardGeneration) this.setState('recording'); }
      catch (error) { this.acceptingAudio = false; if (generation !== this.discardGeneration) return; this.setState('paused'); throw error; }
      return;
    }
    if (action === 'stop') {
      if (!['recording', 'paused', 'error'].includes(this.state)) return;
      const endedAt = this.now();
      this.setState('stopping');
      try { await this.secureTail(); }
      catch (error) { if (generation !== this.discardGeneration) return; this.setState('error'); throw error; }
      if (generation !== this.discardGeneration) return;
      const entry = {
        id: crypto.randomUUID(), startedAt: this.startedAt, endedAt,
        elapsedMs: Math.max(0, endedAt - this.startedAt), audioMs: this.samples / SAMPLE_RATE * 1000,
      };
      const timeline = this.timingValid ? { version: 1, sampleRate: SAMPLE_RATE, timeZone: this.timeZone, segments: this.timingSegments } : null;
      const blob = this.samples ? wavBlob(this.parts, timeline) : null;
      this.parts = []; this.samples = 0; this.startedAt = null;
      this.timingSegments = [];
      this.setState('idle');
      return { entry, blob };
    }
  }
  dispose() {
    this.disposed = true; this.acceptingAudio = false; this.parts = []; this.timingSegments = [];
    this.mic?.stream?.getTracks().forEach(track => track.stop());
    try { this.mic?.destroy(); } catch {}
    this.context?.close().catch(() => {});
  }
}
