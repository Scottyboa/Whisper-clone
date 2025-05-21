export const indexTranslations = {
  pageTitle: "Transcribe Notes",
  headerTitle: "Transcribe Notes",
  headerSubtitle: "Advanced AI-Powered Speech-to-Text and Clinical Note Generation for Healthcare Consultations",
  startText: "Dont have an API-key yet? Click on «API guide- How to Get» for easy instructions.",
  apiPlaceholder: "Enter API Key here",
  enterButton: "Enter Transcription Tool",
  guideButton: "API guide - How to use",
  securityButton: "Security",
  aboutButton: "About",
  adRevenueMessage: "As this website is free to use and relies solely on ad revenue, please consent to ads to help support the service.",
  securityModalHeading: "Privacy",
securityModalText: `
<strong>Privacy and Data Processing</strong><br><br>
This web app is provided as a tool for speech-to-text and note generation. As a healthcare professional/data controller you are fully responsible for ensuring that all use complies with the GDPR, the Health Personnel Act, and the Norwegian “Norm” for information security.<br><br>

You alone are responsible for making sure the use of this app satisfies every requirement in:<br>
- GDPR<br>
- Health Personnel Act<br>
- Norm for Information Security<br><br>

This includes, among other things:<br>
- Signing the necessary agreements (DPA)<br>
- Carrying out thorough risk assessments (DPIA and TIA)<br><br>

More information on these topics appears further down in this text.<br><br>

The developer of this web app accepts no liability for your use of it or for any failure to comply with applicable regulations.<br><br>
<hr><br>

<strong>1. How does the web app work?</strong><br>
- Records audio using the browser’s recording feature.<br>
- Processes audio in the browser’s memory (RAM).<br>
- Uploads the audio file over a secure HTTPS connection to the OpenAI Whisper API for transcription, using your own API key.<br>
- Sends the transcription (and any additional text/prompt) to the OpenAI API, which generates a draft note—also with your own API key.<br>
- Receives the note directly in your browser over a secure/encrypted connection.<br>
- Your API key is stored only temporarily in SessionStorage. When you close the web app or exit the browser, the key is deleted from memory. To use the app again you must paste in your key anew. This provides an extra layer of security for your key and prevents unauthorised access.<br><br>
<hr><br>

<strong>2. Your own OpenAI API key is required</strong><br>
All communication with OpenAI happens directly from your browser using your personal API key. The developer has no access to your key or data.<br><br>
<hr><br>

<strong>3. Data Processing Agreement (DPA) with OpenAI</strong><br>
If you will use the API services to process personal data, you should sign a DPA with OpenAI. You can find OpenAI’s standard agreement here: <a href="https://ironcladapp.com/public-launch/63ffefa2bed6885f4536d0fe" style="color:blue;" target="_blank">OpenAI Data Processing Agreement (DPA)</a>. Your organisation ID is available here: <a href="https://platform.openai.com/settings/organization/general" style="color:blue;" target="_blank">your OpenAI organisation profile</a>. Once signed, both you and OpenAI acknowledge that you, the user, act as data processor—not OpenAI.<br><br>
<hr><br>

<strong>4. DPIA and TIA – Required risk assessments</strong><br><br>

<strong>DPIA (Data Protection Impact Assessment):</strong> Required under GDPR Article 35 when new technology is used to process special-category data. The purpose is to identify and mitigate privacy risks in the processing itself.<br>
Assess what is processed, why, and which measures are needed to protect patients’ rights.<br>
Template available here: <a href="https://transcribe-notes.netlify.app/dpia-en" style="color:blue;" target="_blank">Suggested DPIA (template)</a><br><br>

<strong>TIA (Transfer Impact Assessment):</strong> Required under the Schrems II ruling and GDPR Articles 44–49 when personal data are transferred to a country outside the EEA (such as the USA). The purpose is to document that the transfer provides a “level of protection essentially equivalent” to the EEA.<br>
Assess US legislation (FISA 702, CLOUD Act, etc.) against the nature of the data and your supplementary technical/contractual safeguards.<br>
Conclude whether the transfer—together with Standard Contractual Clauses and OpenAI’s EU-US Data Privacy Framework certification—remains defensible.<br>
Template available here: <a href="https://transcribe-notes.netlify.app/tia.html" style="color:blue;" target="_blank">Suggested Transfer Impact Assessment (TIA)</a><br><br>

Both assessments should be completed, documented, and approved by you before the web app is used.<br><br>
<hr><br>

<strong>5. Zero Data Retention (ZDR) and data storage at OpenAI</strong><br><br>

<strong>OpenAI’s standard policy</strong><br>
Under OpenAI’s API Data Usage Policy, data sent to the API are not used to train the models. However, they may be stored temporarily (typically up to 30 days) for abuse monitoring and debugging before deletion.<br><br>

<strong>Zero Data Retention (ZDR)</strong><br>
OpenAI offers ZDR for certain larger customers by special agreement, but this is not standard for normal API users and is therefore not active for this app.<br><br>

<strong>Next steps</strong><br>
Future versions of the app may explore support for alternative AI providers that offer ZDR as standard (e.g. certain services on Microsoft Azure). Any updates in this regard will be communicated through the web app.<br><br>
<hr><br>

<strong>6. Prerequisites for potential clinical use</strong><br><br>
Your assessment is decisive: The legality of using this tool with patient data depends entirely on your own thorough evaluation. You must conclude—based on the DPA with OpenAI, DPIA, and TIA—whether the usage is defensible and any residual risk acceptable for your practice.<br><br>

<strong>Minimum requirements before using patient data:</strong><br>
- A valid DPA with OpenAI is in place.<br>
- A practice-specific DPIA and TIA are completed, approved, and conclude that residual risk is acceptable.<br>
- Content responsibility: You are responsible for all content you send to OpenAI via your API key and for quality-assuring the generated draft note before it is possibly transferred to the patient record.<br><br>
<hr><br>

<strong>7. Overview of data storage</strong><br><br>
<table style="border-collapse:collapse;width:100%;">
  <thead>
    <tr>
      <th style="border:1px solid #ccc;padding:4px;">Data&nbsp;Type</th>
      <th style="border:1px solid #ccc;padding:4px;">Where is it stored?</th>
      <th style="border:1px solid #ccc;padding:4px;">For how long?</th>
      <th style="border:1px solid #ccc;padding:4px;">Who has access?</th>
    </tr>
  </thead>
  <tbody>
    <tr>
      <td style="border:1px solid #ccc;padding:4px;">Your OpenAI API key</td>
      <td style="border:1px solid #ccc;padding:4px;">SessionStorage memory in your browser</td>
      <td style="border:1px solid #ccc;padding:4px;">Until you close the web app or the browser</td>
      <td style="border:1px solid #ccc;padding:4px;">Only you and your browser</td>
    </tr>
    <tr>
      <td style="border:1px solid #ccc;padding:4px;">Audio segments while recording</td>
      <td style="border:1px solid #ccc;padding:4px;">Browser memory (RAM)</td>
      <td style="border:1px solid #ccc;padding:4px;">Only during recording/processing. Not stored at OpenAI once processing is finished</td>
      <td style="border:1px solid #ccc;padding:4px;">Only you and your browser</td>
    </tr>
    <tr>
      <td style="border:1px solid #ccc;padding:4px;">Text/draft note</td>
      <td style="border:1px solid #ccc;padding:4px;">OpenAI API (temporary)</td>
      <td style="border:1px solid #ccc;padding:4px;">Up to 30 days at OpenAI</td>
      <td style="border:1px solid #ccc;padding:4px;">You, OpenAI (temporary)</td>
    </tr>
    <tr>
      <td style="border:1px solid #ccc;padding:4px;">Instructions / Prompts</td>
      <td style="border:1px solid #ccc;padding:4px;">Locally in your browser. If you log in to the web app on the same browser, computer, and with the same API key, your prompts will be available again</td>
      <td style="border:1px solid #ccc;padding:4px;">Until you delete them</td>
      <td style="border:1px solid #ccc;padding:4px;">You and your browser</td>
    </tr>
  </tbody>
</table><br><br>
<hr><br>

<strong>8. Source code</strong><br><br>
- The source code is open and runs locally in your browser.<br><br>
<hr><br>

<strong>9. Cookies and ads</strong><br><br>
We use cookies solely to display relevant ads through Google Ads, and for language selection, consent management, and storage of customised prompts you have created. The cookies do not store personal data beyond what is necessary for functionality and personalisation. Google’s cookies have no access to data related to audio recordings and generated text (patient data).
`,

  aboutModalHeading: "About",
  aboutModalText: `This website was created to provide healthcare professionals and other users with direct access to high-quality speech-to-text transcription and clinical note generation—without unnecessary costs or intermediaries.<br><br>
By using your own OpenAI API key, you connect directly to the source of the technology. This means you only pay the actual usage cost set by OpenAI, without markups or subscription fees.<br><br>
Many existing providers offer similar services but charge significantly more—often 8 to 10 times the real cost of the underlying technology. This platform offers the same functionality at a fraction of the price.<br><br>
<strong>Key points:</strong><br>
• No subscription, no account required.<br>
• You only pay OpenAI directly for what you use.<br>
• The website itself is completely free.<br><br>
To continue offering this free service, we would greatly appreciate it if you accept the display of ads from Google Ads. Ad revenue helps us cover hosting and operational costs, allowing the service to remain accessible to everyone.`,
  guideModalHeading: "API key - How to Get",
guideModalText: `To use this web app, you must first create an OpenAI API profile, generate an API key, and ensure that your OpenAI wallet has sufficient funds. Next, copy the API key and paste it into the designated field. When you press "Enter," the web app temporarily stores the API key for the session—this key connects you to OpenAI’s servers so that speech-to-text transcription and note generation can function. Please note that you are charged immediately for each task performed (speech-to-text and/or note generation). For more information on costs, see the "Cost Information" section on the front page. We recommend that you read the privacy and information notice on the front page before using the app.
<br><br>
<strong>1. Create your OpenAI API profile</strong><br>
To get started, you need to set up a profile on the OpenAI API platform. This profile serves as your account for managing API keys and billing. To begin, visit <a href="https://platform.openai.com/signup" style="color:blue;">OpenAI API Sign-Up</a>. Follow the instructions to register and create an account. Once registered, you’ll have access to your dashboard, where you can generate a personal API key and add credits to your OpenAI wallet.
<br><br>
<strong>2. Generate an API key</strong><br>
After creating your profile, generate an API key by navigating to <a href="https://platform.openai.com/account/api-keys" style="color:blue;">API Key Management</a>. Click the button to create a new API key. Important: you will only see the key once. Copy it immediately and store it securely (for example, in a text file). If you lose the key or suspect it has been compromised, you can easily deactivate/delete it in the same section where you generated it and create a new one.
<br><br>
<strong>3. Add funds to your OpenAI wallet</strong><br>
For the web app to function, your OpenAI wallet must have sufficient funds. Visit <a href="https://platform.openai.com/account/billing/overview" style="color:blue;">Billing & Payments</a> to add funds. You can top up with any amount at any time. As long as funds are available, you’ll be able to use the features of this web app—each task is billed immediately. For a detailed pricing breakdown, see "Cost Information."
<br><br>
<strong>Session Security Notice</strong><br>
When you log in by entering the API key into the field on this front page and pressing Enter, it is stored only temporarily in your browser session. This means that if you leave the page, close your browser, or shut down your computer, the API key will not be saved. You will then need to copy and paste it again the next time you use the web app, ensuring that your key remains secure.`,

  priceButton: "Price",
  priceModalHeading: "Price",
priceModalText: `
<div>
  <p><strong>Cost Information</strong></p>
  <p>You only pay for what you use — directly from the source, with no costly middlemen. No subscription. No commitment.</p>

  <p><strong>Prices:</strong></p>
  <ul>
    <li>Speech-to-text: $0.006 per minute</li>
    <li>Note generation: $5 per 1 million tokens (input) and $10 per 1 million tokens (output)</li>
  </ul>

  <p><strong>Example – 15-minute consultation:</strong></p>
  <ul>
    <li>Speech-to-text: 15 × $0.006 = $0.09</li>
    <li>Note generation: typically between $0.005 and $0.01</li>
    <li>Total: approximately $0.10 for the full consultation</li>
  </ul>

  <p><strong>Example monthly cost with regular use:</strong></p>
  <ul>
    <li>20 consultations per day × 4 days per week × 4 weeks = 320 consultations</li>
    <li>Total monthly cost: approximately $30–31</li>
  </ul>

  <p><strong>You only pay for usage:</strong><br>
  If you don’t use the service due to vacation, illness, or other reasons, you pay nothing.</p>
</div>
`,
};

export const transcribeTranslations = {
  pageTitle: "Transcription Tool with Ads and Guide Overlay",
  openaiUsageLinkText: "Cost Usage Overview",
  openaiWalletLinkText: "Wallet Balance",
  btnFunctions: "Functions",
  btnGuide: "Guide",
  backToHome: "Back to frontpage",
  recordingAreaTitle: "Recording Area",
  recordTimer: "Recording Timer: 0 sec",
  transcribeTimer: "Completion Timer: 0 sec",
  transcriptionPlaceholder: "Transcription result will appear here...",
  startButton: "Start Recording",
  readFirstText: "Read first! ➔",
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
guideText: `Welcome to the Transcribe Notes Transcription tool. This application allows medical professionals, therapists, and other practitioners to record and transcribe consultations, as well as generate professional notes using an AI-powered note generator.<br><br>

<strong>How to Use the Functions:</strong><br><br>

<ul>
  <li><strong>Recording:</strong> Patient consent must always be obtained prior to recording. Click "Start Recording" to begin capturing audio. Every 2 minutes, a chunk of audio is automatically sent to the OpenAI servers for transcription. The transcripts will appear sequentially in the transcription output field.<br><br>
  <strong><u>Important:</u> The recorder does not work in every web browser. It is recommended to use either <strong>Google Chrome</strong> or <strong>Microsoft Edge</strong>.</strong></li><br>

  <li><strong>Pause and Resume:</strong> You can use the "Pause" button to temporarily stop the recording—for instance, if the consultation is interrupted or you need to step out of the office briefly. When you click "Pause", the current audio segment is uploaded and transcribed, and the recording is paused. When you're ready to continue, click "Resume", and the recording automatically resumes with the next segment. The timer continues from where it left off, and the session can be ended as usual by clicking "Stop/Complete".</li><br>

  <li><strong>Completion:</strong> After clicking "Stop/Complete", the recording stops. The Completion Timer counts until the full transcript is received (usually within 5–10 seconds).</li><br>

  <li><strong>Custom Prompt:</strong> On the right, select a prompt slot (1–10) and enter your custom prompt. Your prompt is saved automatically and linked to your API key. You can create any prompt that fits your documentation style, tone, and clinical focus. This gives you full flexibility over how your notes are generated.</li><br>

  <li><strong>Note Generation:</strong> Once transcription is complete, click "Generate Note" to create a note based on your transcript and selected/custom prompt. Generated medical notes must be reviewed and validated by healthcare professionals before use.</li><br>

  <li><strong>Usage Overview:</strong> To check your current usage at OpenAI, click on the usage overview hyperlink on the main interface.</li><br>

  <li><strong>Security:</strong> Your audio recording is sent directly to OpenAI’s API servers for transcription, only for the purpose of transcription. It is not stored or used for machine learning. The transcribed text displayed in your browser is not saved anywhere, and is deleted/disappears as soon as you close the browser or load new content.</li><br>

  <li><strong>Guide Toggle:</strong> Click the "Guide" button again to return to the main interface.</li>
</ul><br><br>

<strong>Prompt Examples:</strong><br><br>

<strong>Consultation:</strong><br>
"System prompt – Medical Note Generator

Write a medically accurate, journal-ready note based on a transcribed doctor-patient conversation. Use the following structure (unless otherwise specified in the dictation):
Background (only if relevant history), Presenting complaint/anamnesis, Examination (bullet points), Assessment, Plan.

Rules:
– Do not include information, investigations, or findings not explicitly mentioned.
– Negative findings only if stated.
– Blood tests: write “relevant blood tests are ordered”, do not list them.
– Correct obvious misspellings in medication names.
– Do not use special characters or line breaks before headings.
– Follow explicit instructions from the doctor regarding style, length, or specific wording.

If the doctor adds comments after the patient has left, these must be considered. The note should be well-written."

<br><br>

<strong>Letter to patient:</strong><br>
"Write a letter from the doctor to the patient. Start with Hi \\"name\\", and end with<br>
Regards<br>
\\"Your name\\"<br>
\\"Clinic name\\"<br>
The letter must have a professional and formal tone. You may improve the wording slightly for better flow."

<br><br>

These are examples that work well, but feel free to adapt them to your documentation style, specialty, and type of consultation. You can also create entirely custom prompts for any purpose you wish.
`,
};

export default { indexTranslations, transcribeTranslations };
