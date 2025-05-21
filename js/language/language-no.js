// js/language-no.js

export const indexTranslations = {
  pageTitle: "Transcribe Notes",
  headerTitle: "Transcribe Notes",
  headerSubtitle: "Avansert AI-drevet tale-til-tekst og notatgenerering for helsekonsultasjoner",
  startText: "Har du ikke en API-nøkkel ennå? Klikk på «API nøkkel – Hvordan lage» for enkel veiledning.",
  apiPlaceholder: "Skriv inn API-nøkkel her",
  enterButton: "Gå til transkripsjonsverktøyet",
  guideButton: "API-guide – Slik bruker du den",
  securityButton: "Sikkerhet",
  aboutButton: "Om",
  adRevenueMessage: "Siden dette nettstedet er gratis å bruke og utelukkende finansieres av annonseinntekter, setter vi stor pris på om du godtar annonser for å støtte tjenesten.",
  
  securityModalHeading: "Personvern",
  securityModalText: `
<strong>Personvern og Databehandling</strong><br><br>
Denne webappen er laget som et verktøy for bruk av tale-til-tekst og notatgenerering. Det er ditt fulle ansvar som helsepersonell/behandlingsansvarlig å sikre at all bruk er i samsvar med GDPR, helsepersonelloven og Normen for informasjonssikkerhet.<br><br>

Du er eneansvarlig for at bruken av denne appen oppfyller alle krav i:<br>
- GDPR<br>
- Helsepersonelloven<br>
- Normen for informasjonssikkerhet<br><br>

Dette innebærer blant annet:<br>
- Inngå nødvendige avtaler (DPA)<br>
- Utføre grundige risikovurderinger (DPIA og TIA)<br><br>

- Mer informasjon om dette lengere ned i denne teksten.<br><br>

Utvikler av denne webapp påtar seg intet ansvar for din bruk eller manglende etterlevelse.<br><br>
<hr><br>

<strong>1. Hva fungerer webappen?</strong><br>
- Tar opp lyd via nettleserens opptaksfunksjon.<br>
- Behandler lyd i nettleserens minne (RAM).<br>
- Laster opp lydfil via sikker HTTPS-forbindelse til OpenAI Whisper API for transkripsjon, ved bruk av din egen API-nøkkel.<br>
- Sender transkripsjonen (og eventuell tilleggstekst / prompt) videre til OpenAI API som genererer et notatutkast, også med din egen API-nøkkel.<br>
- Nettleseren mottar notatet direkte fra OpenAI med sikker/kryptert tilkobling.<br>
- Din API-nøkkel lagres bare midlertidig i nettleserens minne (SessionStorage). Skrur du av webappen, eller går ut av nettleseren, så slettes API-nøkkelen din fra nettleserens minne. For å da kunne bruke webappen igjen, så må du klippe-lime inn din API-nøkkel på nytt. Dette fungerer som et ekstra lag med sikkerhet overfor din API-nøkkel, og motvirker ikke-autorisert tilgang til din nøkkel.<br><br>
<hr><br>

<strong>2. Din egen OpenAI API-nøkkel er påkrevd</strong><br>
All kommunikasjon med OpenAI skjer direkte fra din nettleser ved bruk av din personlige API-nøkkel. Utvikleren av denne webappen har ingen tilgang til din nøkkel eller data.<br><br>
<hr><br>

<strong>3. Databehandleravtale (DPA) med OpenAI</strong><br>
Hvis du skal bruke API-tjenestene til behandling av personopplysninger anbefales det at du inngår en databehandleravtale med OpenAI. Du finner OpenAI sin standardavtale her: <a href="https://ironcladapp.com/public-launch/63ffefa2bed6885f4536d0fe" style="color:blue;" target="_blank">OpenAI databehandleravtale (DPA)</a>. Du finner ditt organisasjonsnummer her: <a href="https://platform.openai.com/settings/organization/general" style="color:blue;" target="_blank">din OpenAI organisasjonsprofil</a>. Når avtalen er signert, så har du og OpenAI anerkjent at det er du som bruker, som har rollen som databehandler – ikke OpenAI.<br><br>
<hr><br>

<strong>4. DPIA og TIA – Nødvendige risikovurderinger</strong><br><br>

<strong>DPIA (Data Protection Impact Assessment):</strong> Påkrevd etter GDPR artikkel 35 når ny teknologi brukes til å behandle særlige kategorier opplysninger. Formålet er å identifisere og redusere personvernrisikoene knyttet til selve behandlingen.<br>
Undersøk hva som behandles, hvorfor, og hvilke tiltak som trengs for å beskytte pasientenes rettigheter.<br>
Eksempelmal tilgjengelig her: <a href="https://transcribe-notes.netlify.app/dpia" style="color:blue;" target="_blank">Forslag til DPIA (eksempelmal)</a><br><br>

<strong>TIA (Transfer Impact Assessment):</strong> Påkrevd etter Schrems II-dommen og GDPR artikkel 44–49 når personopplysninger overføres til et land utenfor EØS (som USA). Formålet er å dokumentere at overføringen gir et «vesentlig tilsvarende» personvernnivå.<br>
Vurder amerikansk lovgivning (FISA 702, CLOUD Act m.m.) mot dataenes art og dine supplerende tekniske/kontraktuelle tiltak.<br>
Konkluder på om overføringen – sammen med Standard Contractual Clauses og OpenAIs EU-US Data Privacy Framework-sertifisering – fortsatt er forsvarlig.<br>
Eksempelmal tilgjengelig her: <a href="https://transcribe-notes.netlify.app/tia.html" style="color:blue;" target="_blank">Forslag til Transfer Impact Assessment (TIA)</a><br><br>

Begge vurderingene bør være gjennomført, dokumentert og godkjent av deg som bruker før webappen tas i bruk.<br><br>
<hr><br>

<strong>5. Zero Data Retention (ZDR) og datalagring hos OpenAI</strong><br><br>

<strong>OpenAIs standard policy</strong><br>
Per OpenAIs API Data Usage Policy brukes data sendt til API-et ikke til å trene modellene. Data kan imidlertid lagres midlertidig (typisk opptil 30 dager) for misbruksovervåking og feilsøking før de slettes.<br><br>

<strong>Zero Data Retention (ZDR)</strong><br>
OpenAI tilbyr ZDR for enkelte større kunder etter særskilt avtale, men dette er ikke standard for vanlig API-bruk og er derfor ikke aktivt for denne appen.<br><br>

<strong>Veien videre</strong><br>
Fremtidige versjoner av appen kan utforske støtte for alternative KI-leverandører som tilbyr ZDR som standard (f.eks. visse tjenester på Microsoft Azure). Eventuelle oppdateringer med tanke på dette vil kommuniseres via webappen.<br><br>
<hr><br>

<strong>6. Forutsetninger for potensiell klinisk bruk</strong><br><br>
Din vurdering er avgjørende: Lovligheten av å bruke dette verktøyet med pasientdata avhenger utelukkende av din egen grundige vurdering. Du må selv konkludere – basert på DPA med OpenAI, DPIA og TIA – om bruken er forsvarlig og om restrisikoen er akseptabel for din praksis.<br><br>

<strong>Minimumskrav før bruk med pasientdata:</strong><br>
- Gyldig DPA med OpenAI er på plass.<br>
- Virksomhetsspesifikk DPIA og TIA er gjennomført, godkjent og konkluderer med akseptabel restrisiko.<br>
- Ansvar for innhold: Du er ansvarlig for alt innhold du sender til OpenAI via din API-nøkkel og for å kvalitetssikre notatutkastet som genereres i etterkant, før de evt. overføres til pasientjournal.<br><br>
<hr><br>

<strong>7. Oversikt over datalagring</strong><br><br>
<table style="border-collapse:collapse;width:100%;">
  <thead>
    <tr>
      <th style="border:1px solid #ccc;padding:4px;">Datatype</th>
      <th style="border:1px solid #ccc;padding:4px;">Hvor lagres den?</th>
      <th style="border:1px solid #ccc;padding:4px;">Hvor lenge?</th>
      <th style="border:1px solid #ccc;padding:4px;">Hvem har tilgang?</th>
    </tr>
  </thead>
  <tbody>
    <tr>
      <td style="border:1px solid #ccc;padding:4px;">Din OpenAI API-nøkkel</td>
      <td style="border:1px solid #ccc;padding:4px;">SessionStorage-minne i din nettleser</td>
      <td style="border:1px solid #ccc;padding:4px;">Til du enten avslutter webappen eller nettleseren</td>
      <td style="border:1px solid #ccc;padding:4px;">Kun deg og din nettleser</td>
    </tr>
    <tr>
      <td style="border:1px solid #ccc;padding:4px;">Lydsegmenter under opptak</td>
      <td style="border:1px solid #ccc;padding:4px;">Nettleserens minne (RAM)</td>
      <td style="border:1px solid #ccc;padding:4px;">Kun under opptak/prosessering. Lagres ikke hos OpenAI etter prosessering er fullført</td>
      <td style="border:1px solid #ccc;padding:4px;">Kun deg og din nettleser</td>
    </tr>
    <tr>
      <td style="border:1px solid #ccc;padding:4px;">Tekst/notatutkast</td>
      <td style="border:1px solid #ccc;padding:4px;">OpenAI API (midlertidig)</td>
      <td style="border:1px solid #ccc;padding:4px;">Maks 30 dager hos OpenAI</td>
      <td style="border:1px solid #ccc;padding:4px;">Du, OpenAI (midlertidig)</td>
    </tr>
    <tr>
      <td style="border:1px solid #ccc;padding:4px;">Instruksjoner / Prompter</td>
      <td style="border:1px solid #ccc;padding:4px;">Lokalt i din nettleser. Hvis du som bruker logger inn i webappen på samme nettleser, datamaskin og med samme API-nøkkel, så vil promptene du har laget være tilgjengelige for deg igjen</td>
      <td style="border:1px solid #ccc;padding:4px;">Til du sletter dem</td>
      <td style="border:1px solid #ccc;padding:4px;">Du og din nettleser</td>
    </tr>
  </tbody>
</table><br><br>
<hr><br>

<strong>8. Kildekode</strong><br><br>
- Kildekoden er åpen og kjører lokalt i din nettleser.<br><br>
<hr><br>

<strong>9. Informasjonskapsler og annonser</strong><br><br>
Vi benytter informasjonskapsler (cookies) utelukkende for å kunne vise relevante annonser gjennom Google Ads, og for språkvalg, samtykke og for lagring av tilpassede prompts som du har laget. Informasjonskapslene lagrer ikke personopplysninger utover det som er nødvendig for funksjonalitet og tilpasning. Googles informasjonskapsler har ingen tilgang til data relatert til lydopptak og generert tekst (pasientdata).
`,
  
  aboutModalHeading: "Om",
  aboutModalText: `Denne nettsiden ble opprettet for å gi helsepersonell og andre brukere direkte tilgang til høykvalitets tale-til-tekst transkripsjon og klinisk notatgenerering – uten unødvendige kostnader eller mellomledd.<br><br>
Ved å bruke din egen OpenAI API-nøkkel kobler du deg direkte til kilden for teknologien. Dette betyr at du kun betaler den faktiske bruksprisen fastsatt av OpenAI, uten påslag eller abonnementsavgifter.<br><br>
Mange eksisterende leverandører tilbyr lignende tjenester, men tar betydelig mer – ofte 8 til 10 ganger den reelle kostnaden for den underliggende teknologien. Denne plattformen tilbyr samme funksjonalitet til en brøkdel av prisen.<br><br>
<strong>Nøkkelpunkter:</strong><br>
• Ingen abonnement, ingen konto kreves.<br>
• Du betaler kun OpenAI direkte for det du bruker.<br>
• Nettsiden i seg selv er helt gratis.<br><br>
For at vi skal kunne fortsette å tilby denne tjenesten gratis, så hadde vi satt stor pris på om du godtar at det vises reklame fra Google Ads. Annonseinntektene hjelper oss å dekke kostnader til hosting og drift, slik at tjenesten kan forbli tilgjengelig for alle.`,  
  guideModalHeading: "API nøkkel - Hvordan lage",
guideModalText: `For å bruke denne webappen, må du først opprette en OpenAI API-profil, generere en API-nøkkel og sørge for at din OpenAI-lommebok har tilstrekkelige midler. API-nøkkelen kopieres deretter og limes inn i det angitte feltet. Når du trykker på "Enter", lagrer webappen API-nøkkelen midlertidig for økten – denne nøkkelen kobler deg til OpenAI-serverne slik at tale-til-tekst-transkripsjon og notatgenerering kan fungere. Vennligst merk at du belastes umiddelbart per utførte oppgave (tale-til-tekst og/eller notatgenerering). For mer informasjon om kostnader, se "Kostnadsinformasjon"-seksjonen på forsiden. Vi anbefaler at du som bruker leser gjennom personvern- og informasjonsteksten på forsiden før du tar i bruk appen.
<br><br>
<strong>1. Opprett din OpenAI API-profil</strong><br>
For å komme i gang, må du opprette en profil på OpenAI API-plattformen. Denne profilen fungerer som din konto for administrasjon av API-nøkler og fakturering. For å starte, besøk <a href="https://platform.openai.com/signup" style="color:blue;">OpenAI API Registrering</a>. Følg instruksjonene og opprett en bruker. Når du er registrert, får du tilgang til dashbordet ditt. Du vil da ha mulighet til å generere en personlig API-nøkkel, samt laste opp kreditt til din OpenAI-lommebok.
<br><br>
<strong>2. Generer en API-nøkkel</strong><br>
Etter at du har opprettet profilen din, generer en API-nøkkel ved å gå til <a href="https://platform.openai.com/account/api-keys" style="color:blue;">API-nøkkeladministrasjonen</a>. Klikk på knappen for å opprette en ny API-nøkkel. Viktig: Du vil kun se nøkkelen én gang. Kopier den umiddelbart og oppbevar den sikkert (f.eks. i en tekstfil). Hvis du mister nøkkelen eller mistenker at den har blitt kompromittert, kan du enkelt deaktivere/slette den på samme sted som du genererte den og samtidig opprette en ny.
<br><br>
<strong>3. Sett inn midler på din OpenAI-lommebok</strong><br>
For at webappen skal fungere, må din OpenAI-lommebok ha tilstrekkelige midler. Besøk <a href="https://platform.openai.com/account/billing/overview" style="color:blue;">Fakturerings- og betalingsside</a> for å sette inn midler. Du kan overføre hvilket som helst beløp når som helst. Så lenge midlene er tilgjengelige, vil du kunne bruke funksjonene i denne webappen – hver oppgave belastes umiddelbart. For detaljert prisoversikt, se "Kostnadsinformasjon".
<br><br>
<strong>Sikkerhetsmerknad for økten</strong><br>
Når du logger inn ved å skrive inn API-nøkkelen i feltet på denne forsiden og klikker på enter, så lagres denne kun midlertidig i nettleserøkten din. Dette betyr at hvis du forlater nettsiden, lukker nettleseren eller slår av datamaskinen, vil ikke API-nøkkelen bli lagret. Du må da klippe og lime den inn på nytt neste gang du bruker webappen, noe som sikrer at nøkkelen din forblir sikker.`,  
  priceButton: "Pris",
  priceModalHeading: "Kostnadsinformasjon",
priceModalText: `
<div>
  <p><strong>Kostnadsinformasjon</strong></p>
  <p>Du betaler kun for det du bruker, direkte fra kilden, uten dyre mellomledd – ingen abonnement, ingen binding.</p>

  <p><strong>Priser:</strong></p>
  <ul>
    <li>Tale-til-tekst: $0.006 per minutt</li>
    <li>Notatgenerering: $5 per 1 million tokens (input) og $10 per 1 million tokens (output)</li>
  </ul>

  <p><strong>Eksempel – 15-minutters konsultasjon:</strong></p>
  <ul>
    <li>Tale-til-tekst: 15 × $0.006 = $0.09</li>
    <li>Notatgenerering: vanligvis mellom $0.005 og $0.01</li>
    <li>Totalt: cirka $0.10 for hele konsultasjonen</li>
  </ul>

  <p><strong>Eksempel på månedskostnad ved full bruk:</strong></p>
  <ul>
    <li>20 konsultasjoner per dag × 4 dager i uken × 4 uker = 320 konsultasjoner</li>
    <li>Totalkostnad denne måned: cirka $30–31</li>
  </ul>

  <p><strong>Du betaler bare for bruk:</strong><br>
  Hvis du ikke bruker tjenesten på grunn av ferie, sykdom, permisjon etc, betaler du ingenting.</p>
</div>
`,
};

export const transcribeTranslations = {
  pageTitle: "Transkripsjonsverktøy med annonser og guideoverlegg",
  openaiUsageLinkText: "Kostnadsoversikt",
  openaiWalletLinkText: "OpenAI-kreditt",
  btnFunctions: "Funksjoner",
  btnGuide: "Guide",
  backToHome: "Tilbake til forsiden",
  recordingAreaTitle: "Opptaksområde",
  recordTimer: "Opptakstimer: 0 sek",
  transcribeTimer: "Fullføringstimer: 0 sek",
  transcriptionPlaceholder: "Transkripsjonsresultatet vil vises her...",
  startButton: "Start opptak",
  readFirstText: "Les først! ➔",
  stopButton: "Stopp/Fullfør",
  pauseButton: "Pause opptak",
  statusMessage: "Velkommen! Klikk på \"Start opptak\" for å begynne.",
  noteGenerationTitle: "Notatgenerering",
  generateNoteButton: "Generer notat",
  noteTimer: "Notatgenereringstimer: 0 sek",
  generatedNotePlaceholder: "Generert notat vil vises her...",
  customPromptTitle: "Tilpasset prompt",
  promptSlotLabel: "Prompt Slot:",
  customPromptPlaceholder: "Skriv inn tilpasset prompt her",
  adUnitText: "Din annonse her",
  guideHeading: "Guide & Instruksjoner",
guideText: `Velkommen til <strong>Transcribe Notes</strong>. Denne applikasjonen lar helsepersonell, terapeuter og andre fagpersoner ta opp og transkribere konsultasjoner, samt generere profesjonelle notater ved hjelp av en AI-basert notatgenerator.<br><br>

<strong>Slik bruker du funksjonene:</strong><br><br>

<ul>
  <li><strong>Opptak:</strong> Pasientens samtykke må alltid innhentes før opptak. Klikk på "Start opptak" for å begynne å ta opp lyd. Hvert 2. minutt sendes en lydsekvens automatisk til OpenAI sine servere for transkribering. Transkriberingen vises fortløpende i tekstfeltet for transkripsjon.<br><br>
  <strong><u>Viktig:</u> Opptaksfunksjonen fungerer ikke i alle nettlesere. Vi anbefaler derfor å bruke <strong>Google Chrome</strong> eller <strong>Microsoft Edge</strong>.</strong></li><br>

  <li><strong>Pause og gjenoppta:</strong> Du kan bruke "Pause"-knappen til midlertidig å stoppe opptaket, for eksempel dersom konsultasjonen blir avbrutt eller du trenger å forlate kontoret et øyeblikk. Når du trykker på "Pause", lastes det aktuelle lydsegmentet opp og transkriberes, og opptaket settes på pause. Når du er klar til å fortsette, klikker du på "Fortsett", og opptaket gjenopptas automatisk med neste segment. Tidtakeren fortsetter der den slapp, og opptaket kan til slutt avsluttes som vanlig med "Stopp/Ferdig".</li><br>

  <li><strong>Fullføring:</strong> Når du klikker på "Stopp/Ferdig", stopper opptaket. Fullføringstimeren teller tiden til hele transkripsjonen er mottatt (vanligvis innen 3-7 sekunder).</li><br>

  <li><strong>Tilpasset prompt:</strong> På høyre side kan du velge en promptplass (1–10) og skrive inn din egen prompt. Prompten lagres automatisk og knyttes til din API-nøkkel. Du kan lage hvilken som helst prompt som passer din dokumentasjonsstil, tone og faglige fokus. Dette gir deg full fleksibilitet i hvordan notatene dine genereres. Du finner prompt-eksempler nederst i denne guiden som av erfaring fungerer godt.</li><br>

  <li><strong>Notatgenerering:</strong> Når transkripsjonen er fullført, klikker du på "Generer notat" for å lage et notat basert på transkripsjonen og den valgte/tilpassede prompten. Genererte journalnotater må gjennomgås og valideres av helsepersonell før de tas i bruk.</li><br>

  <li><strong>Kostnadsoversikt:</strong> For å se ditt nåværende forbruk hos OpenAI, klikk på lenken for kostnadsoversikt som er plassert oppe til høyre på denne siden.</li><br>

  <li><strong>Sikkerhet:</strong> Lydopptaket ditt sendes direkte til OpenAI sine API-servere for transkribering, og hverken lagres eller brukes for maskinlæring. Den transkriberte teksten vises kun i nettleseren din, og slettes/forsvinner så snart du lukker nettleseren eller laster inn nytt innhold.</li><br>

  <li><strong>Guide-knapp:</strong> Klikk på "Guide"-knappen igjen for å gå tilbake til hovedvisningen.</li>
</ul><br><br>

<strong>Eksempler på prompts:</strong><br><br>

<strong>Konsultasjon:</strong><br>
"Systemprompt – Medisinsk notatgenerator

Skriv et medisinsk presist, journalklart notat basert på en transkribert lege-pasient-samtale. Bruk følgende struktur (med mindre annet er spesifisert i diktatet):
Bakgrunn (kun ved relevant historikk), Aktuelt/anamnese, Undersøkelse (punktvis), Vurdering, Plan.

Regler:
– Ikke inkluder opplysninger, undersøkelser eller funn som ikke er eksplisitt nevnt.
– Negative funn kun hvis nevnt.
– Hvis blodprøver rekvireres: skriv “relevante blodprøver rekvireres”, ikke list opp alle prøvene så langt lege ikke nevner dette eksplisitt.
– Rett åpenbare feilstavinger i medikamentnavn.
– Ikke bruk spesialtegn eller linjeskift før overskrifter.
– Følg eksplisitte instruksjoner fra legen om stil, lengde eller spesifikke formuleringer.

Dersom legen legger til kommentarer etter at pasienten har gått, skal disse hensyntas. Det er viktig at det brukes godt språk i notatet."<br><br>

<strong>Brev til pasient:</strong><br>
"Skriv brev fra lege til pasient. Start med Hei \\"navn\\", og avslutt med<br>
Mvh<br>
\\"Ditt navn\\"<br>
\\"Navn på legesenteret\\"<br><
Brevet må ha en profesjonell og formel fremtoning. Kan godt rette litt på språket for bedre tekst."<br><br>

Dette er eksempler som fungerer godt, men du står fritt til å tilpasse dem slik at de passer din dokumentasjonsstil, spesialitet og type konsultasjon. Du kan også lage helt egne prompts til hvilket formål du måtte ønske.  
`,
};

export default { indexTranslations, transcribeTranslations };
