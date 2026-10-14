// Presentation only: no recorder, mail, storage, or transcription dependencies.
export class PrivacyView {
  constructor({ view, controls, code, toggleButton }) {
    this.view = view; this.controls = controls; this.code = code;
    this.toggleButton = toggleButton; this.active = false;
    this.home = document.createComment('View controls');
    controls.before(this.home);
    // Escape must not provide another way out of the mockup.
    view.addEventListener('cancel', event => event.preventDefault());
    toggleButton.addEventListener('click', () => this.toggle(code.value));
  }

  toggle(code = '') {
    if (this.active) {
      if (String(code) !== '1') return false;
      this.view.close();
      this.home.after(this.controls);
      this.active = false;
    } else {
      // Cover even an open import dialog without closing it. The real UI stays
      // mounted and all background tasks continue unchanged.
      this.view.prepend(this.controls);
      this.view.showModal();
      this.active = true;
    }
    this.code.value = '';
    this.toggleButton.focus({ preventScroll: true });
    return true;
  }
}
