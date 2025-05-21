// ui.js

// Enable functional buttons on the page.
function enableFunctionalButtons() {
  const startButton = document.getElementById("startButton");
  if (startButton) {
    startButton.disabled = false;
    startButton.title = "";
  }
  const generateNoteButton = document.getElementById("generateNoteButton");
  if (generateNoteButton) {
    generateNoteButton.disabled = false;
    generateNoteButton.title = "";
  }
}

// Initialize info modals (using an accordion UI in this case).
function initInfoModals() {
  console.log("initInfoModals: Accordion UI is enabled; modal initialization is disabled.");
}

// Ad injection functions are now handled directly in transcribe.html.
// The following functions remain as no‑ops to avoid breaking other parts of the code.

function loadAdSenseAds() {
  // No ad loading here. Ads are dynamically injected in transcribe.html.
}

function initAdUnits() {
  // No ad injection here. Ad units are managed in transcribe.html.
}

function initConsentBanner() {
  // Since ads are now managed in transcribe.html, simply enable functional buttons.
  enableFunctionalButtons();
  console.log("Consent banner removed; ads are managed in transcribe.html.");
}

// Export functions for use in other modules.
export { enableFunctionalButtons, initInfoModals, loadAdSenseAds, initAdUnits, initConsentBanner };
