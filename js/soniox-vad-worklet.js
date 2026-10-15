// Soniox batch capture. Same frame size and averaging resampling as vad-web
// 0.0.22; adds an acknowledged drain and preserves the partial final frame.
class SonioxBatchCapture extends AudioWorkletProcessor {
  constructor(options) {
    super();
    this.frameSamples = options.processorOptions.frameSamples;
    this.input = [];
    this.inputTime = null;
    this.drained = false;
    this.port.onmessage = ({ data }) => {
      if (data?.message === 'SONIOX_DRAIN') {
        if (!this.drained) {
          this.drained = true;
          if (this.input.length) {
            // Complete only the partial frame, with silence (at most one VAD
            // frame). All preceding frames have already been posted in order.
            const required = Math.ceil(this.frameSamples * sampleRate / 16000);
            while (this.input.length < required) this.input.push(0);
            this.emitFrame();
          }
        }
        this.port.postMessage({ message: 'SONIOX_DRAINED' });
      } else if (data?.message === 'SPEECH_STOP') {
        this.drained = true;
      }
    };
  }

  emitFrame() {
    const frame = new Float32Array(this.frameSamples);
    let index = 0;
    for (let out = 0; out < frame.length; out++) {
      let sum = 0;
      let count = 0;
      const end = Math.min(this.input.length, (out + 1) * sampleRate / 16000);
      while (index < end) { sum += this.input[index++]; count++; }
      frame[out] = count ? sum / count : 0;
    }
    const audioTime = this.inputTime;
    this.input = this.input.slice(index);
    this.inputTime += index / sampleRate;
    this.port.postMessage({ message: 'AUDIO_FRAME', audioTime, data: frame.buffer }, [frame.buffer]);
  }

  process(inputs) {
    if (this.drained) return true;
    const audio = inputs[0]?.[0];
    if (audio) {
      for (let i = 0; i < audio.length; i++) {
        if (!this.input.length) this.inputTime = currentTime + i / sampleRate;
        this.input.push(audio[i]);
        if (this.input.length * 16000 / sampleRate >= this.frameSamples) this.emitFrame();
      }
    }
    return true;
  }
}

registerProcessor('soniox-batch-capture', SonioxBatchCapture);
