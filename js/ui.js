// ui.js

// === Consent Banner Functions ===

// Sets a cookie with the given name, value, and expiration in days.
function setCookie(name, value, days) {
  let expires = "";
  if (days) {
    const date = new Date();
    date.setTime(date.getTime() + days * 24 * 60 * 60 * 1000);
    expires = "; expires=" + date.toUTCString();
  }
  document.cookie = name + "=" + (value || "") + expires + "; path=/";
}

// Retrieves the value of a cookie with the specified name.
function getCookie(name) {
  const nameEQ = name + "=";
  const ca = document.cookie.split(";");
  for (let c of ca) {
    c = c.trim();
    if (c.indexOf(nameEQ) === 0) return c.substring(nameEQ.length);
  }
  return null;
}

// Dynamically loads the AdSense script.
function loadAdSense() {
  const script = document.createElement("script");
  script.async = true;
  script.src = "https://pagead2.googlesyndication.com/pagead/js/adsbygoogle.js";
  document.head.appendChild(script);
  (adsbygoogle = window.adsbygoogle || []).push({});
}

// Initializes the consent banner: attaches event listeners and checks cookie status.
function initConsentBanner() {
  const cmpAccept = document.getElementById("cmp-accept");
  const cmpManage = document.getElementById("cmp-manage");
  const cmpBanner = document.getElementById("cmp-banner");

  if (cmpAccept) {
    cmpAccept.addEventListener("click", () => {
      setCookie("user_consent", "accepted", 365);
      if (cmpBanner) cmpBanner.style.display = "none";
      loadAdSense();
      const adRevenueMessage = document.getElementById("ad-revenue-message");
      if (adRevenueMessage) {
        adRevenueMessage.style.display = "none";
      }
      console.log("Consent accepted: AdSense loaded and banner hidden.");
    });
  }

  if (cmpManage) {
    cmpManage.addEventListener("click", () => {
      alert("Here you can manage your cookie and ad preferences.");
    });
  }

  if (getCookie("user_consent") === "accepted") {
    if (cmpBanner) cmpBanner.style.display = "none";
    loadAdSense();
    const adRevenueMessage = document.getElementById("ad-revenue-message");
    if (adRevenueMessage) {
      adRevenueMessage.style.display = "none";
    }
    console.log("Consent already accepted: Banner hidden and AdSense loaded.");
  }
}

// === Guide Overlay (Index Page) ===

// Initializes the API key guide overlay and the enter button event listener.
function initGuideOverlay() {
  const overlay = document.getElementById("apiKeyGuideOverlay");
  const closeGuide = document.getElementById("closeGuideBtn");
  const openGuideButton = document.getElementById("openGuideButton");
  const enterTranscriptionBtn = document.getElementById("enterTranscriptionBtn");
  const apiKeyInput = document.getElementById("apiKeyInput");

  // Check if overlay and openGuideButton exist
  if (openGuideButton && overlay) {
    openGuideButton.addEventListener("click", () => {
      overlay.style.display = "flex";
      overlay.style.flexDirection = "column";
      overlay.style.alignItems = "center";
      console.log("Guide overlay opened.");
    });
  } else {
    console.error("Guide overlay or openGuideButton element missing.");
  }

  if (closeGuide && overlay) {
    closeGuide.addEventListener("click", () => {
      overlay.style.display = "none";
      console.log("Guide overlay closed.");
    });
  } else {
    console.error("Close guide button element missing.");
  }

  // Attach event listener to enter button.
  if (enterTranscriptionBtn && apiKeyInput) {
    enterTranscriptionBtn.addEventListener("click", () => {
      console.log("Enter button clicked.");
      const apiKey = apiKeyInput.value.trim();
      if (apiKey) {
        console.log("API key entered:", apiKey);
        sessionStorage.setItem("openai_api_key", apiKey);
        window.location.href = "transcribe.html";
      } else {
        console.log("No valid API key entered.");
        alert("Please enter a valid API key.");
      }
    });
  } else {
    console.error("Enter button or API key input element missing.");
  }
}

export { initConsentBanner, initGuideOverlay };
