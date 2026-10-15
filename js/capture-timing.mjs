// Keep timing only for frames still retained by the pinned VAD's audioBuffer.
export class CaptureTiming {
  constructor() { this.frames = []; }
  add(samples, epoch) { this.frames.push({ samples, epoch }); }
  retain(count) {
    if (!count) this.frames = [];
    else if (this.frames.length > count) this.frames = this.frames.slice(-count);
  }
  speech(samples) {
    const pieces = []; let remaining = samples;
    for (let i = this.frames.length - 1; i >= 0 && remaining > 0; i--) {
      const frame = this.frames[i], length = Math.min(remaining, frame.samples);
      if (!Number.isFinite(frame.epoch)) return null;
      pieces.push([length, frame.epoch + (frame.samples - length) / 16]); remaining -= length;
    }
    if (remaining || !pieces.length) return null;
    const result = []; let offset = 0;
    for (const [length, epoch] of pieces.reverse()) {
      const previous = result.at(-1);
      if (previous && Math.abs(previous[2] + previous[1] / 16 - epoch) < 1) previous[1] += length;
      else result.push([offset, length, epoch]);
      offset += length;
    }
    return result;
  }
}
