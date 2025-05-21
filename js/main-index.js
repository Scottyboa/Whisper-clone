import { initIndexLanguage } from './languageLoaderUsage.js';
import { initInfoModals } from './ui.js';

document.addEventListener('DOMContentLoaded', async () => {
  // Initialize language support for the index page.
  await initIndexLanguage();

  // Initialize the info accordions (replacing the previous modal implementation).
  initInfoModals();
});
