// main.js

import { initTranscribeLanguage } from './language.js';
import { initRecording } from './recording.js';
import { initNoteGeneration } from './noteGeneration.js';
import { initConsentBanner } from './ui.js';

document.addEventListener('DOMContentLoaded', () => {
  // Initialize language support for the transcribe page.
  initTranscribeLanguage();

  // Initialize the recording functionality.
  initRecording();

  // Initialize note generation and custom prompt handling.
  initNoteGeneration();

  // Initialize the consent banner and ad loading.
  initConsentBanner();
});
