// A privacy view may only appear after recording has stopped successfully.
export class PrivacyView {
  constructor({ stopRecording, isStopped, show, restore }) {
    this.stopRecording = stopRecording;
    this.isStopped = isStopped;
    this.show = show; this.restore = restore;
    this.active = false; this.transitioning = false;
  }

  get blocked() { return this.active || this.transitioning; }

  async toggle(code = '') {
    if (this.transitioning) return false;
    if (this.active) {
      if (String(code).trim() !== '1') return false;
      this.active = false;
      this.restore();
      return true;
    }
    // Set this before awaiting Stop to block new local/email recording commands.
    this.transitioning = true;
    try {
      await this.stopRecording();
      if (!this.isStopped()) throw new Error('Recording must stop before switching views.');
      this.active = true;
      this.show();
      return true;
    } finally {
      this.transitioning = false;
    }
  }
}
