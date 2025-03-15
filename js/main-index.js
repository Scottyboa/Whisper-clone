// main-index.js

import { initIndexLanguage } from './language.js';
import { initConsentBanner, initGuideOverlay } from './ui.js';

document.addEventListener('DOMContentLoaded', () => {
  // Initialize language support for the index page.
  initIndexLanguage();

  // Initialize the consent banner.
  initConsentBanner();

  // Initialize the API key guide overlay and API key redirect functionality.
  initGuideOverlay();
});
