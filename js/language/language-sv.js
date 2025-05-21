// js/language-sv.js

export const indexTranslations = {
  pageTitle: "Transcribe Notes",
  headerTitle: "Transcribe Notes",
  headerSubtitle: "Avancerad AI-driven tal-till-text och notisgenerering för vårdkonsultationer",
  startText: "För att komma igång, vänligen ange din OpenAI API-nyckel:",
  apiPlaceholder: "Ange API-nyckel här",
  enterButton: "Gå till transkriptionsverktyget",
  guideButton: "Hur du använder",
  securityButton: "Integritet",
  aboutButton: "Om",
  adRevenueMessage: "Eftersom denna webbplats är gratis att använda och enbart finansieras genom annonsintäkter, vänligen godkänn annonser för att stödja tjänsten.",

securityModalHeading: "Integritet",
securityModalText: `
<strong>Integritet och Databehandling</strong><br><br>
Denna webbapp är skapad som ett verktyg för tal-till-text och anteckningsgenerering. Det är ditt fulla ansvar som vårdpersonal/behandlingsansvarig att säkerställa att all användning sker i enlighet med GDPR, hälso- och sjukvårdslagen och Normen för informationssäkerhet.<br><br>

Du är ensam ansvarig för att användningen av denna app uppfyller alla krav enligt:<br>
- GDPR<br>
- Hälso- och sjukvårdslagen<br>
- Normen för informationssäkerhet<br><br>

Detta innebär bland annat:<br>
- Ingå nödvändiga avtal (DPA)<br>
- Utföra grundliga riskbedömningar (DPIA och TIA)<br><br>

- Mer information om detta finns längre ned i texten.<br><br>

Utvecklaren av denna webbapp tar inget ansvar för din användning eller bristande efterlevnad.<br><br>
<hr><br>

<strong>1. Hur fungerar webbappen?</strong><br>
- Spelar in ljud via webbläsarens inspelningsfunktion.<br>
- Bearbetar ljudet i webbläsarens minne (RAM).<br>
- Laddar upp ljudfilen via en säker HTTPS-anslutning till OpenAI Whisper API för transkribering, med din egen API-nyckel.<br>
- Skickar transkriberingen (och eventuell ytterligare text / prompt) vidare till OpenAI API som genererar ett utkast till anteckning, också med din egen API-nyckel.<br>
- Webbläsaren tar emot anteckningen direkt från OpenAI via en säker/krypterad anslutning.<br>
- Din API-nyckel lagras endast tillfälligt i webbläsarens minne (SessionStorage). Stänger du webbappen eller webbläsaren, raderas din API-nyckel från minnet. För att använda webbappen igen måste du klistra in din API-nyckel på nytt. Detta ger ett extra lager av säkerhet för din API-nyckel och skyddar mot obehörig åtkomst.<br><br>
<hr><br>

<strong>2. Din egen OpenAI API-nyckel krävs</strong><br>
All kommunikation med OpenAI sker direkt från din webbläsare med din personliga API-nyckel. Utvecklaren av denna webbapp har ingen tillgång till din nyckel eller dina data.<br><br>
<hr><br>

<strong>3. Personuppgiftsbiträdesavtal (DPA) med OpenAI</strong><br>
Om du ska använda API-tjänsterna för behandling av personuppgifter rekommenderas att du ingår ett personuppgiftsbiträdesavtal med OpenAI. Du hittar OpenAIs standardavtal här: <a href="https://ironcladapp.com/public-launch/63ffefa2bed6885f4536d0fe" style="color:blue;" target="_blank">OpenAI personuppgiftsbiträdesavtal (DPA)</a>. Du hittar ditt organisationsnummer här: <a href="https://platform.openai.com/settings/organization/general" style="color:blue;" target="_blank">din OpenAI organisationsprofil</a>. När avtalet är signerat har du och OpenAI erkänt att det är du som användare som har rollen som personuppgiftsansvarig – inte OpenAI.<br><br>
<hr><br>

<strong>4. DPIA och TIA – Nödvändiga riskbedömningar</strong><br><br>

<strong>DPIA (Data Protection Impact Assessment):</strong> Krävs enligt GDPR artikel 35 när ny teknik används för att behandla känsliga personuppgifter. Syftet är att identifiera och minska integritetsrisker kopplade till behandlingen.<br>
Undersök vad som behandlas, varför och vilka åtgärder som behövs för att skydda patienternas rättigheter.<br>
Exempelmall finns här: <a href="https://transcribe-notes.netlify.app/dpia" style="color:blue;" target="_blank">Förslag till DPIA (exempelmall)</a><br><br>

<strong>TIA (Transfer Impact Assessment):</strong> Krävs enligt Schrems II-domen och GDPR artiklarna 44–49 vid överföring av personuppgifter till ett land utanför EES (som USA). Syftet är att dokumentera att överföringen erbjuder en "väsentligt likvärdig" nivå av dataskydd.<br>
Bedöm amerikansk lagstiftning (FISA 702, CLOUD Act m.m.) mot datatyperna och dina kompletterande tekniska/avtalsmässiga skyddsåtgärder.<br>
Konkludera om överföringen – tillsammans med standardavtalsklausuler och OpenAIs certifiering enligt EU-US Data Privacy Framework – fortfarande är försvarlig.<br>
Exempelmall finns här: <a href="https://transcribe-notes.netlify.app/tia.html" style="color:blue;" target="_blank">Förslag till Transfer Impact Assessment (TIA)</a><br><br>

Båda bedömningarna bör vara genomförda, dokumenterade och godkända av dig innan webbappen används.<br><br>
<hr><br>

<strong>5. Zero Data Retention (ZDR) och datalagring hos OpenAI</strong><br><br>

<strong>OpenAIs standardpolicy</strong><br>
Enligt OpenAIs API Data Usage Policy används inte data som skickas till API:et för att träna modellerna. Data kan dock lagras tillfälligt (oftast upp till 30 dagar) för missbruksövervakning och felsökning innan de raderas.<br><br>

<strong>Zero Data Retention (ZDR)</strong><br>
OpenAI erbjuder ZDR till vissa större kunder genom särskilda avtal, men detta är inte standard för vanlig API-användning och är därför inte aktivt för denna app.<br><br>

<strong>Framtida utveckling</strong><br>
Framtida versioner av appen kan komma att stödja alternativa AI-leverantörer som erbjuder ZDR som standard (t.ex. vissa tjänster hos Microsoft Azure). Eventuella uppdateringar kommer att kommuniceras via webbappen.<br><br>
<hr><br>

<strong>6. Förutsättningar för potentiell klinisk användning</strong><br><br>
Din egen bedömning är avgörande: Lagligheten av att använda detta verktyg med patientdata beror helt på din egen grundliga utvärdering. Du måste själv dra slutsatsen – baserat på DPA med OpenAI, DPIA och TIA – om användningen är försvarlig och om restrisken är acceptabel för din verksamhet.<br><br>

<strong>Minimikrav före användning med patientdata:</strong><br>
- Giltigt DPA med OpenAI är på plats.<br>
- Verksamhetsspecifik DPIA och TIA är genomförda, godkända och konkluderar med acceptabel restrisk.<br>
- Ansvar för innehåll: Du ansvarar för allt innehåll du skickar till OpenAI via din API-nyckel samt för att kvalitetssäkra det genererade anteckningsutkastet innan eventuell överföring till patientjournal.<br><br>
<hr><br>

<strong>7. Översikt över datalagring</strong><br><br>
<table style="border-collapse:collapse;width:100%;">
  <thead>
    <tr>
      <th style="border:1px solid #ccc;padding:4px;">Datatyp</th>
      <th style="border:1px solid #ccc;padding:4px;">Var lagras den?</th>
      <th style="border:1px solid #ccc;padding:4px;">Hur länge?</th>
      <th style="border:1px solid #ccc;padding:4px;">Vem har tillgång?</th>
    </tr>
  </thead>
  <tbody>
    <tr>
      <td style="border:1px solid #ccc;padding:4px;">Din OpenAI API-nyckel</td>
      <td style="border:1px solid #ccc;padding:4px;">SessionStorage-minne i din webbläsare</td>
      <td style="border:1px solid #ccc;padding:4px;">Tills du avslutar webbappen eller webbläsaren</td>
      <td style="border:1px solid #ccc;padding:4px;">Endast du och din webbläsare</td>
    </tr>
    <tr>
      <td style="border:1px solid #ccc;padding:4px;">Ljudsegment under inspelning</td>
      <td style="border:1px solid #ccc;padding:4px;">Webbläsarens minne (RAM)</td>
      <td style="border:1px solid #ccc;padding:4px;">Endast under inspelning/bearbetning. Sparas inte hos OpenAI efter avslutad bearbetning</td>
      <td style="border:1px solid #ccc;padding:4px;">Endast du och din webbläsare</td>
    </tr>
    <tr>
      <td style="border:1px solid #ccc;padding:4px;">Text/anteckningsutkast</td>
      <td style="border:1px solid #ccc;padding:4px;">OpenAI API (tillfälligt)</td>
      <td style="border:1px solid #ccc;padding:4px;">Max 30 dagar hos OpenAI</td>
      <td style="border:1px solid #ccc;padding:4px;">Du, OpenAI (tillfälligt)</td>
    </tr>
    <tr>
      <td style="border:1px solid #ccc;padding:4px;">Instruktioner / Prompter</td>
      <td style="border:1px solid #ccc;padding:4px;">Lokalt i din webbläsare. Om du loggar in i webbappen på samma webbläsare, dator och med samma API-nyckel kommer dina sparade prompts att vara tillgängliga för dig igen</td>
      <td style="border:1px solid #ccc;padding:4px;">Tills du själv raderar dem</td>
      <td style="border:1px solid #ccc;padding:4px;">Du och din webbläsare</td>
    </tr>
  </tbody>
</table><br><br>
<hr><br>

<strong>8. Källkod</strong><br><br>
- Källkoden är öppen och körs lokalt i din webbläsare.<br><br>
<hr><br>

<strong>9. Cookies och annonser</strong><br><br>
Vi använder cookies enbart för att kunna visa relevanta annonser via Google Ads samt för språkval, samtycke och lagring av anpassade prompts du skapar. Cookies lagrar inte personuppgifter utöver vad som är nödvändigt för funktionalitet och anpassning. Googles cookies har ingen åtkomst till data relaterad till ljudinspelningar och genererad text (patientdata).
`,

  aboutModalHeading: "Om",
aboutModalText: `Denna webbplats skapades för att ge vårdpersonal och andra användare direkt tillgång till högkvalitativ tal-till-text-transkription och generering av kliniska notat – utan onödiga kostnader eller mellanhänder.<br><br>
Genom att använda din egen OpenAI API-nyckel kopplar du dig direkt till källan för teknologin. Det innebär att du endast betalar den faktiska användningskostnaden som sätts av OpenAI, utan påslag eller prenumerationsavgifter.<br><br>
Många befintliga leverantörer erbjuder liknande tjänster men tar betydligt mer betalt – ofta 8 till 10 gånger den verkliga kostnaden för den underliggande tekniken. Denna plattform erbjuder samma funktionalitet till en bråkdel av priset.<br><br>
<strong>Viktiga punkter:</strong><br>
• Ingen prenumeration, inget konto krävs.<br>
• Du betalar endast direkt till OpenAI för det du använder.<br>
• Webbplatsen i sig är helt gratis.<br><br>
För att vi ska kunna fortsätta erbjuda den här gratistjänsten skulle vi verkligen uppskatta om du godkänner att annonser från Google Ads visas. Annonsintäkterna hjälper oss att täcka kostnader för hosting och drift, så att tjänsten kan förbli tillgänglig för alla.`,
  
  guideModalHeading: "API-guide – Hur du använder",
guideModalText: `För att använda denna webbapp måste du först skapa en OpenAI API-profil, generera en API-nyckel och se till att din OpenAI-plånbok har tillräckliga medel. API-nyckeln kopieras därefter och klistras in i det angivna fältet. När du trycker på "Enter" sparar webbappen API-nyckeln temporärt för sessionen – denna nyckel ansluter dig till OpenAI-servrarna så att tal-till-text-transkription och anteckningsgenerering kan fungera. Vänligen notera att du debiteras omedelbart för varje utförd uppgift (tal-till-text och/eller anteckningsgenerering). För mer information om kostnader, se avsnittet "Kostnadsinformation" på startsidan. Vi rekommenderar att du som användare läser igenom sekretess- och informationsmeddelandet på startsidan innan du tar i bruk appen.
<br><br>
<strong>1. Skapa din OpenAI API-profil</strong><br>
För att komma igång måste du skapa ett konto på OpenAI API-plattformen. Detta konto fungerar som din administrationspanel för API-nycklar och fakturering. Besök <a href="https://platform.openai.com/signup" style="color:blue;">OpenAI API Registrering</a> och följ instruktionerna för att registrera dig. När du är registrerad får du tillgång till din instrumentpanel, där du kan generera en personlig API-nyckel samt fylla på din OpenAI-plånbok med medel.
<br><br>
<strong>2. Generera en API-nyckel</strong><br>
Efter att du skapat ditt konto går du till <a href="https://platform.openai.com/account/api-keys" style="color:blue;">API-nyckeladministrationen</a>. Klicka på knappen för att skapa en ny API-nyckel. Viktigt: Du kommer bara att se nyckeln en gång. Kopiera den omedelbart och förvara den säkert (t.ex. i en krypterad textfil). Om du tappar bort nyckeln eller misstänker att den har äventyrats kan du inaktivera eller radera den på samma sida och därefter skapa en ny.
<br><br>
<strong>3. Fyll på medel på din OpenAI-plånbok</strong><br>
För att webbappen ska fungera måste din OpenAI-plånbok ha tillräckliga medel. Besök <a href="https://platform.openai.com/account/billing/overview" style="color:blue;">Fakturerings- och betalningssida</a> för att överföra medel. Du kan sätta in valfritt belopp när som helst. Så länge medlen finns tillgängliga kan du använda appens funktioner – varje uppgift debiteras omedelbart. För en detaljerad prisöversikt, se avsnittet "Kostnadsinformation".
<br><br>
<strong>Säkerhetsnotis för sessionen</strong><br>
När du loggar in genom att klistra in API-nyckeln i fältet på denna sida och trycker på Enter sparas den endast temporärt i din webbläsarsession. Detta innebär att om du lämnar sidan, stänger webbläsaren eller stänger av datorn kommer API-nyckeln att raderas. Du måste då klistra in den på nytt nästa gång du använder webbappen, vilket säkerställer att din nyckel förblir skyddad.`,

  priceButton: "Pris",
  priceModalHeading: "Pris",
priceModalText: `
<div>
  <p><strong>Kostnadsinformation</strong></p>
  <p>Du betalar endast för det du använder – direkt från källan, utan dyra mellanhänder. Ingen prenumeration. Inga bindningar.</p>

  <p><strong>Priser:</strong></p>
  <ul>
    <li>Tal-till-text: $0.006 per minut</li>
    <li>Notatgenerering: $5 per 1 miljon tokens (input) och $10 per 1 miljon tokens (output)</li>
  </ul>

  <p><strong>Exempel – 15 minuters konsultation:</strong></p>
  <ul>
    <li>Tal-till-text: 15 × $0.006 = $0.09</li>
    <li>Notatgenerering: vanligtvis mellan $0.005 och $0.01</li>
    <li>Totalt: cirka $0.10 för hela konsultationen</li>
  </ul>

  <p><strong>Exempel på månadskostnad vid full användning:</strong></p>
  <ul>
    <li>20 konsultationer per dag × 4 dagar i veckan × 4 veckor = 320 konsultationer</li>
    <li>Total månadskostnad: cirka $30–31</li>
  </ul>

  <p><strong>Du betalar bara för användning:</strong><br>
  Om du inte använder tjänsten på grund av semester, sjukdom eller ledighet, betalar du ingenting.</p>
</div>
`,
};

export const transcribeTranslations = {
  pageTitle: "Transkriptionstjänst med annonser och guideöverlägg",
  openaiUsageLinkText: "Översikt över kostnader",
  openaiWalletLinkText: "Plånbokssaldo",
  btnFunctions: "Funktioner",
  btnGuide: "Guide",
  backToHome: "Tillbaka till startsidan",
  recordingAreaTitle: "Inspelningsområde",
  recordTimer: "Inspelningstimer: 0 sek",
  transcribeTimer: "Fullföljandetimer: 0 sek",
  transcriptionPlaceholder: "Transkriptionsresultatet visas här...",
  startButton: "Starta inspelning",
  readFirstText: "Läs först! ➔",
  stopButton: "Stoppa/Avsluta",
  pauseButton: "Pausa inspelning",
  statusMessage: "Välkommen! Klicka på 'Starta inspelning' för att börja.",
  noteGenerationTitle: "Notisgenerering",
  generateNoteButton: "Generera notis",
  noteTimer: "Notisgenereringstimer: 0 sek",
  generatedNotePlaceholder: "Den genererade notisen visas här...",
  customPromptTitle: "Anpassad prompt",
  promptSlotLabel: "Promptplats:",
  customPromptPlaceholder: "Ange anpassad prompt här",
  adUnitText: "Din annons här",
  guideHeading: "Guide & Instruktioner",
guideText: `Välkommen till <strong>Transcribe Notes</strong>. Denna applikation gör det möjligt för vårdpersonal, terapeuter och andra yrkesutövare att spela in och transkribera konsultationer, samt generera professionella journalanteckningar med hjälp av en AI-driven notatgenerator.<br><br>

<strong>Så här använder du funktionerna:</strong><br><br>

<ul>
  <li><strong>Inspelning:</strong> Patientens samtycke måste alltid inhämtas innan denna applikation används. Klicka på "Starta inspelning" för att börja spela in ljud. Varje 2 minuter skickas ett ljudavsnitt automatiskt till OpenAIs servrar för transkribering. Transkriptionen visas successivt i textfältet för transkribering.<br><br>
  <strong><u>Viktigt:</u> Inspelningsfunktionen fungerar inte i alla webbläsare. Vi rekommenderar att du använder <strong>Google Chrome</strong> eller <strong>Microsoft Edge</strong>.</strong></li><br>

  <li><strong>Paus och återuppta:</strong> Du kan använda knappen "Paus" för att tillfälligt stoppa inspelningen – till exempel om konsultationen avbryts eller om du behöver lämna rummet en stund. När du klickar på "Paus" laddas det aktuella ljudsegmentet upp och transkriberas, och inspelningen pausas. När du är redo att fortsätta klickar du på "Återuppta", och inspelningen återupptas automatiskt med nästa segment. Timern fortsätter från där den stannade, och sessionen kan avslutas som vanligt med "Stoppa/Avsluta".</li><br>

  <li><strong>Avslut:</strong> När du klickar på "Stoppa/Klar", avslutas inspelningen. Tidsräknaren för slutförande visar hur lång tid det tar att ta emot hela transkriptionen (vanligtvis inom 5–10 sekunder).</li><br>

  <li><strong>Anpassad prompt:</strong> Till höger kan du välja en promptplats (1–10) och skriva in din egen prompt. Prompten sparas automatiskt och kopplas till din API-nyckel. Du kan skapa vilken prompt du vill som passar din dokumentationsstil, ton och kliniska inriktning. Detta ger dig full flexibilitet i hur anteckningarna genereras.</li><br>

  <li><strong>Generera anteckning:</strong> När transkriptionen är klar, klicka på "Generera anteckning" för att skapa ett journalutdrag baserat på din transkription och valda/skapade prompt. Genererade journalanteckningar måste granskas och valideras av vårdpersonal innan de används.</li><br>

  <li><strong>Kostnadsöversikt:</strong> För att se din nuvarande användning hos OpenAI, klicka på länken för kostnadsöversikt som är placerad uppe till höger på sidan.</li><br>

  <li><strong>Säkerhet:</strong> Din ljudinspelning skickas direkt till OpenAIs API-servrar, som inte lagrar datan och endast använder den för transkribering. Den transkriberade texten visas endast i din webbläsare, och <strong>den raderas/försvinner så snart du stänger webbläsaren eller laddar nytt innehåll.</strong></li><br>

  <li><strong>Guide-knappen:</strong> Klicka på "Guide"-knappen igen för att återgå till huvudsidan.</li>
</ul><br><br>

<strong>Exempel på promptar:</strong><br><br>

<strong>Konsultation:</strong><br>
"Systemprompt – Medicinsk notatsgenerator

Skriv en medicinskt korrekt, journalfärdig notis baserad på ett transkriberat samtal mellan läkare och patient. Använd följande struktur (om inget annat anges i diktatet):
Bakgrund (endast vid relevant historik), Aktuellt/anamnes, Undersökning (punktform), Bedömning, Plan.

Regler:
– Inkludera inte information, undersökningar eller fynd som inte uttryckligen nämns.
– Negativa fynd endast om de anges.
– Blodprover: skriv “relevanta blodprover beställs”, lista dem inte.
– Rätta uppenbara stavfel i läkemedelsnamn.
– Använd inte specialtecken eller radbrytningar före rubriker.
– Följ läkarens uttryckliga instruktioner kring stil, längd eller specifika formuleringar.

Om läkaren lägger till kommentarer efter att patienten har lämnat ska dessa beaktas. Notatet ska vara välformulerat."

<br><br>

<strong>Brev till patient:</strong><br>
"Skriv ett brev från läkaren till patienten. Börja med Hej \\"namn\\", och avsluta med<br>
Vänligen<br>
\\"Ditt namn\\"<br>
\\"Namn på vårdcentral\\"<br>
Brevet ska ha en professionell och formell ton. Du kan förbättra språket något för bättre flyt."

<br><br>

Dessa är välfungerande exempel, men du kan gärna anpassa dem till din egen dokumentationsstil, specialitet och typ av konsultation. Du kan också skapa helt egna promptar för andra ändamål.
`,
};
