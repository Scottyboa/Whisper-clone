const fingerprint = '6b86b273ff34fce19d6b804eff5a3f5747ada4eaa22f1d49c01e52ddb7875b4b';

// A small UI gate, not authentication: browser code can always be inspected.
export class AppGuide {
  constructor({ dialog, button, code, close }) {
    Object.assign(this, { dialog, button, code }); this.checking = false;
    button.addEventListener('click', () => this.open());
    close.addEventListener('click', () => dialog.close());
    dialog.addEventListener('close', () => { code.value = ''; button.focus(); });
  }
  async open() {
    const entered = this.code.value; this.code.value = '';
    if (this.checking || this.dialog.open) return;
    this.checking = true;
    try {
      const digest = await crypto.subtle.digest('SHA-256', new TextEncoder().encode(entered));
      const value = Array.from(new Uint8Array(digest), byte => byte.toString(16).padStart(2, '0')).join('');
      if (value === fingerprint) this.dialog.showModal();
    } catch { /* Leave the guide closed if checking is unavailable. */ }
    finally { this.checking = false; }
  }
}
