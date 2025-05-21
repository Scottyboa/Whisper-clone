import { initTranscribeLanguage } from './languageLoaderUsage.js';
import { initRecording } from './recording.js';
import { initNoteGeneration } from './noteGeneration.js';
// Removed initConsentBanner import since it's no longer needed
// import { initConsentBanner } from './ui.js';

document.addEventListener('DOMContentLoaded', () => {
  // Initialize language support for the transcribe page.
  initTranscribeLanguage();

  // Initialize the recording functionality.
  initRecording();

  // Initialize note generation and custom prompt handling.
  initNoteGeneration();

  // Add hotkey for the "r" key to trigger the "Start Recording" button,
  // but only when not inside an editable text field.
  document.addEventListener('keydown', (event) => {
    const activeElement = document.activeElement;
    // Check if the active element is an input, textarea, or a contentEditable element.
    if (
      activeElement &&
      (activeElement.tagName === 'INPUT' ||
       activeElement.tagName === 'TEXTAREA' ||
       activeElement.isContentEditable)
    ) {
      return;
    }
    // Check if the pressed key is "r" (case-insensitive).
    if (event.key.toLowerCase() === 'r') {
      const startButton = document.getElementById('startButton');
      if (startButton) {
        startButton.click();
      }
    }
  });
});
