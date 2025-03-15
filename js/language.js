// language.js

// Translations for the Index Page
const indexTranslations = {
  en: {
    pageTitle: "Whisper Transcription",
    headerTitle: "Whisper Transcription",
    headerSubtitle: "Convert speech to text for professional consultations",
    startText: "To get started, please enter your OpenAI API key:",
    apiPlaceholder: "Enter API Key here",
    enterButton: "Enter Transcription Tool",
    guideButton: "Guide for setting up API key",
    adRevenueMessage: "As we do not charge for the use of this website and rely solely on ad revenue, we kindly ask you to consent to personalized ads to help support our service."
  },
  no: {
    pageTitle: "Whisper Transkripsjon",
    headerTitle: "Whisper Transkripsjon",
    headerSubtitle: "Konverter tale til tekst for profesjonelle konsultasjoner",
    startText: "For å komme i gang, vennligst skriv inn din OpenAI API-nøkkel:",
    apiPlaceholder: "Skriv inn API-nøkkel her",
    enterButton: "Gå til transkripsjonsverktøy",
    guideButton: "Veiledning for oppsett av API-nøkkel",
    adRevenueMessage: "Siden vi ikke tar betalt for bruk av denne nettsiden og utelukkende er avhengige av annonseinntekter, ber vi deg vennligst om å samtykke til personaliserte annonser for å støtte tjenesten vår."
  }
};

// Updates the index page elements based on the current language
function updateLanguageIndex(lang) {
  document.getElementById("page-title").textContent = indexTranslations[lang].pageTitle;
  document.getElementById("header-title").textContent = indexTranslations[lang].headerTitle;
  document.getElementById("header-subtitle").textContent = indexTranslations[lang].headerSubtitle;
  document.getElementById("start-text").textContent = indexTranslations[lang].startText;
  document.getElementById("apiKeyInput").setAttribute("placeholder", indexTranslations[lang].apiPlaceholder);
  document.getElementById("enterTranscriptionBtn").textContent = indexTranslations[lang].enterButton;
  document.getElementById("openGuideButton").textContent = indexTranslations[lang].guideButton;
  document.getElementById("ad-revenue-message").textContent = indexTranslations[lang].adRevenueMessage;
}

// Initializes the language selection for the index page
function initIndexLanguage() {
  let currentLang = localStorage.getItem("siteLanguage") || "en";
  const langSelect = document.getElementById("lang-select");
  if (!langSelect) return;
  langSelect.value = currentLang;
  updateLanguageIndex(currentLang);
  langSelect.addEventListener("change", function() {
    currentLang = this.value;
    localStorage.setItem("siteLanguage", currentLang);
    updateLanguageIndex(currentLang);
  });
}

// Translations for the Transcribe Page
const transcribeTranslations = {
  en: {
    pageTitle: "Transcription Tool with Ads and Guide Overlay",
    openaiUsageLinkText: "Cost usage overview",
    btnFunctions: "Functions",
    btnGuide: "Guide",
    recordingAreaTitle: "Recording Area",
    recordTimer: "Recording Timer: 0 sec",
    transcribeTimer: "Completion Timer: 0 sec",
    transcriptionPlaceholder: "Transcription result will appear here...",
    startButton: "Start Recording",
    stopButton: "Stop/Complete",
    pauseButton: "Pause Recording",
    statusMessage: "Welcome! Click \"Start Recording\" to begin.",
    noteGenerationTitle: "Note Generation",
    generateNoteButton: "Generate Note",
    noteTimer: "Note Generation Timer: 0 sec",
    generatedNotePlaceholder: "Generated note will appear here...",
    customPromptTitle: "Custom Prompt",
    promptSlotLabel: "Prompt Slot:",
    customPromptPlaceholder: "Enter custom prompt here",
    adUnitText: "Your Ad Here",
    guideHeading: "Guide & Instructions",
    guideText: `Welcome to the Whisper Transcription tool. This application allows medical professionals, therapists, and other practitioners to record and transcribe consultations, as well as generate professional notes using an AI-powered note generator.
<br><br>
<strong>How to Use the Functions:</strong>
<ul>
  <li><strong>Recording:</strong> Click "Start Recording" to begin capturing audio. Audio is captured via MediaStreamTrackProcessor (using WebCodecs) and accumulated for up to 40 seconds before being packaged as a self-contained WAV file.</li>
  <li><strong>Completion:</strong> After clicking "Stop/Complete", the recording stops. A 2-second final capture period collects any remaining audio before processing the final chunk. The Completion Timer then ticks until the full transcript is received.</li>
  <li><strong>Note Generation:</strong> After transcription, click "Generate Note" to produce a note based on your transcript and custom prompt.</li>
  <li><strong>Custom Prompt:</strong> On the right, select a prompt slot (1–10) and enter your custom prompt. Your prompt is saved automatically and linked to your API key.</li>
  <li><strong>Guide Toggle:</strong> Use the "Functions" and "Guide" buttons to switch between the functional view and this guide.</li>
</ul>
Please click "Functions" to return to the main interface.`
  },
  no: {
    pageTitle: "Transkripsjonsverktøy med annonser og veiledningsoverlegg",
    openaiUsageLinkText: "Vis OpenAI bruk",
    btnFunctions: "Funksjoner",
    btnGuide: "Veiledning",
    recordingAreaTitle: "Opptaksområde",
    recordTimer: "Opptakstimer: 0 sek",
    transcribeTimer: "Fullføringstimer: 0 sek",
    transcriptionPlaceholder: "Transkripsjonsresultatet vises her...",
    startButton: "Start opptak",
    stopButton: "Stopp/Fullfør",
    pauseButton: "Pause opptak",
    statusMessage: "Velkommen! Klikk 'Start opptak' for å begynne.",
    noteGenerationTitle: "Notatgenerering",
    generateNoteButton: "Generer notat",
    noteTimer: "Notatgenereringstimer: 0 sek",
    generatedNotePlaceholder: "Generert notat vises her...",
    customPromptTitle: "Tilpasset melding",
    promptSlotLabel: "Meldingsplass:",
    customPromptPlaceholder: "Skriv inn tilpasset melding her",
    adUnitText: "Din annonse her",
    guideHeading: "Veiledning og Instruksjoner",
    guideText: `Velkommen til Whisper Transkripsjonsverktøy. Denne applikasjonen lar medisinske fagpersoner, terapeuter og andre utøvere ta opp og transkribere konsultasjoner, samt generere profesjonelle notater ved hjelp av en AI-drevet notatgenerator.
<br><br>
<strong>Slik bruker du verktøyet:</strong>
<ul>
  <li><strong>Opptak:</strong> Klikk på "Start opptak" for å starte opptaket. Lydopptak fanges via MediaStreamTrackProcessor (med WebCodecs) og akkumuleres i opptil 40 sekunders biter før de pakkes som gyldige WAV-filer.</li>
  <li><strong>Fullføring:</strong> Etter at du klikker "Stopp/Fullfør", avsluttes opptaket. En 2-sekunders sluttfase fanger opp resterende lyd, og deretter tickes fullføringstimeren til transkripsjonen er ferdig.</li>
  <li><strong>Notatgenerering:</strong> Etter transkripsjonen, klikk "Generer notat" for å lage et notat basert på transkripsjonen og din tilpassede melding.</li>
  <li><strong>Tilpasset melding:</strong> Velg et meldingsfelt (1–10) og skriv inn din tilpassede melding. Meldingen lagres automatisk og knyttes til din API-nøkkel.</li>
  <li><strong>Veiledning:</strong> Bruk knappene "Funksjoner" og "Veiledning" for å bytte mellom verktøysgrensesnittet og denne veiledningen.</li>
</ul>
Klikk "Funksjoner" for å gå tilbake til hovedskjermen.`
  }
};

// Updates the transcribe page elements based on the current language
function updateLanguageTranscribe(lang) {
  document.getElementById("page-title-transcribe").textContent = transcribeTranslations[lang].pageTitle;
  document.getElementById("openaiUsageLink").textContent = transcribeTranslations[lang].openaiUsageLinkText;
  document.getElementById("btnFunctions").textContent = transcribeTranslations[lang].btnFunctions;
  document.getElementById("btnGuide").textContent = transcribeTranslations[lang].btnGuide;
  document.getElementById("recordingAreaTitle").textContent = transcribeTranslations[lang].recordingAreaTitle;
  document.getElementById("recordTimer").textContent = transcribeTranslations[lang].recordTimer;
  document.getElementById("transcribeTimer").textContent = transcribeTranslations[lang].transcribeTimer;
  document.getElementById("transcription").setAttribute("placeholder", transcribeTranslations[lang].transcriptionPlaceholder);
  document.getElementById("startButton").textContent = transcribeTranslations[lang].startButton;
  document.getElementById("stopButton").textContent = transcribeTranslations[lang].stopButton;
  document.getElementById("pauseResumeButton").textContent = transcribeTranslations[lang].pauseButton;
  document.getElementById("statusMessage").textContent = transcribeTranslations[lang].statusMessage;
  document.getElementById("noteGenerationTitle").textContent = transcribeTranslations[lang].noteGenerationTitle;
  document.getElementById("generateNoteButton").textContent = transcribeTranslations[lang].generateNoteButton;
  document.getElementById("noteTimer").textContent = transcribeTranslations[lang].noteTimer;
  document.getElementById("generatedNote").setAttribute("placeholder", transcribeTranslations[lang].generatedNotePlaceholder);
  document.getElementById("customPromptTitle").textContent = transcribeTranslations[lang].customPromptTitle;
  document.getElementById("promptSlotLabel").textContent = transcribeTranslations[lang].promptSlotLabel;
  document.getElementById("customPrompt").setAttribute("placeholder", transcribeTranslations[lang].customPromptPlaceholder);
  document.getElementById("adUnit").textContent = transcribeTranslations[lang].adUnitText;
  document.getElementById("guideHeading").textContent = transcribeTranslations[lang].guideHeading;
  document.getElementById("guideText").innerHTML = transcribeTranslations[lang].guideText;
}

// Initializes the language selection for the transcribe page
function initTranscribeLanguage() {
  let currentLangTranscribe = localStorage.getItem("siteLanguage") || "en";
  const langSelect = document.getElementById("lang-select-transcribe");
  if (!langSelect) return;
  langSelect.value = currentLangTranscribe;
  updateLanguageTranscribe(currentLangTranscribe);
  langSelect.addEventListener("change", function() {
    currentLangTranscribe = this.value;
    localStorage.setItem("siteLanguage", currentLangTranscribe);
    updateLanguageTranscribe(currentLangTranscribe);
  });
}

export { initIndexLanguage, initTranscribeLanguage };
