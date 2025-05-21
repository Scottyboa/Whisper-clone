// js/language-de.js

export const indexTranslations = {
  pageTitle: "Transcribe Notes",
  headerTitle: "Transcribe Notes",
  headerSubtitle: "Fortschrittliche KI-gestützte Sprach-zu-Text-Transkription und Notizenerstellung für medizinische Konsultationen",
  startText: "Um zu beginnen, geben Sie bitte Ihren OpenAI API-Schlüssel ein:",
  apiPlaceholder: "Geben Sie hier den API-Schlüssel ein",
  enterButton: "Transkriptionstool öffnen",
  guideButton: "API-Anleitung – So nutzen Sie es",
  securityButton: "Sicherheit",
  aboutButton: "Über",
  adRevenueMessage: "Da diese Website kostenlos genutzt werden kann und ausschließlich auf Werbeeinnahmen angewiesen ist, stimmen Sie bitte personalisierter Werbung zu, um den Dienst zu unterstützen.",
  securityModalHeading: "Datenschutz",
securityModalText: 
`<strong>Datenschutz und Datenverarbeitung</strong><br><br>
Diese Web-App ist ein Werkzeug für Sprach-zu-Text und das Erstellen von Notizen. Als Gesundheits­fachkraft / Verantwortliche r für die Verarbeitung liegt es vollständig in deiner Verantwortung sicherzustellen, dass jede Nutzung mit der DSGVO, dem norwegischen Gesundheits­personalgesetz (Helsepersonelloven) und der Norm für Informationssicherheit übereinstimmt.<br><br>

Du trägst die alleinige Verantwortung dafür, dass die Nutzung dieser App alle Anforderungen aus:<br>
- DSGVO (GDPR)<br>
- Helsepersonelloven<br>
- Norm für Informationssicherheit<br><br>

erfüllt. Das bedeutet unter anderem:<br>
- Abschluss aller erforderlichen Vereinbarungen (DPA)<br>
- Durchführung gründlicher Risikoanalysen (DPIA und TIA)<br><br>

– Weitere Informationen hierzu findest du weiter unten in diesem Text.<br><br>

Der Entwickler dieser Web-App übernimmt keinerlei Verantwortung für deine Nutzung oder eine fehlende Compliance.<br><br>
<hr><br>

<strong>1. Wie funktioniert die Web-App?</strong><br>
- Nimmt Ton über die Aufnahme­funktion des Browsers auf.<br>
- Verarbeitet die Audiodaten im Arbeitsspeicher (RAM) des Browsers.<br>
- Lädt die Audiodatei über eine gesicherte HTTPS-Verbindung mit deinem eigenen API-Schlüssel an die OpenAI-Whisper-API zur Transkription hoch.<br>
- Sendet die Transkription (und ggf. zusätzlichen Text / Prompt) mit deinem eigenen API-Schlüssel an die OpenAI-API, die daraus einen Notiz­entwurf erstellt.<br>
- Der Browser erhält die Notiz direkt von OpenAI über eine verschlüsselte Verbindung.<br>
- Dein API-Schlüssel wird nur vorübergehend im SessionStorage des Browsers gespeichert. Schließt du die Web-App oder den Browser, wird der Schlüssel aus dem Speicher gelöscht. Um die App erneut zu nutzen, musst du den API-Schlüssel wieder einfügen. Das bietet eine zusätzliche Schutzschicht für deinen Schlüssel und verhindert unbefugten Zugriff.<br><br>
<hr><br>

<strong>2. Eigener OpenAI-API-Schlüssel erforderlich</strong><br>
Sämtliche Kommunikation mit OpenAI erfolgt direkt aus deinem Browser unter Verwendung deines persönlichen API-Schlüssels. Der Entwickler dieser Web-App hat keinen Zugriff auf deinen Schlüssel oder deine Daten.<br><br>
<hr><br>

<strong>3. Auftragsverarbeitungsvertrag (DPA) mit OpenAI</strong><br>
Für die Verarbeitung von Personen­daten über die API-Dienste wird empfohlen, einen Auftragsverarbeitungs­vertrag mit OpenAI abzuschließen. Die Standard­vereinbarung von OpenAI findest du hier: <a href="https://ironcladapp.com/public-launch/63ffefa2bed6885f4536d0fe" style="color:blue;" target="_blank">OpenAI-Auftragsverarbeitungs­vertrag (DPA)</a>. Deine Organisations­nummer erhältst du hier: <a href="https://platform.openai.com/settings/organization/general" style="color:blue;" target="_blank">dein OpenAI-Organisations­profil</a>. Mit der unterschriebenen Vereinbarung erkennen du und OpenAI an, dass du als Nutzer die Rolle des Daten­verarbeiters übernimmst – nicht OpenAI.<br><br>
<hr><br>

<strong>4. DPIA und TIA – erforderliche Risikoanalysen</strong><br><br>

<strong>DPIA (Data Protection Impact Assessment):</strong> Gemäß Artikel 35 DSGVO erforderlich, wenn neue Technologien zur Verarbeitung besonderer Kategorien von Daten eingesetzt werden. Ziel ist es, die Datenschutz­risiken der Verarbeitung zu identifizieren und zu minimieren.<br>
Untersuche, welche Daten verarbeitet werden, warum, und welche Maßnahmen nötig sind, um die Rechte der Patientinnen und Patienten zu schützen.<br>
Beispielformular hier verfügbar: <a href="https://transcribe-notes.netlify.app/dpia" style="color:blue;" target="_blank">Vorschlag für DPIA (Beispielformular)</a><br><br>

<strong>TIA (Transfer Impact Assessment):</strong> Nach dem Schrems-II-Urteil und den Artikeln 44–49 DSGVO erforderlich, wenn Personen­daten in ein Land außerhalb des EWR (z. B. die USA) übermittelt werden. Ziel ist es zu dokumentieren, dass das Schutzniveau der Übermittlung „im Wesentlichen gleichwertig“ ist.<br>
Bewerte die US-Gesetzgebung (FISA 702, CLOUD Act usw.) im Verhältnis zur Art der Daten und deinen ergänzenden technischen und vertraglichen Maßnahmen.<br>
Ziehe eine Schlussfolgerung, ob die Übermittlung – zusammen mit Standard Contractual Clauses und OpenAIs Zertifizierung nach dem EU-US Data Privacy Framework – weiterhin vertretbar ist.<br>
Beispielformular hier verfügbar: <a href="https://transcribe-notes.netlify.app/tia.html" style="color:blue;" target="_blank">Vorschlag für Transfer Impact Assessment (TIA)</a><br><br>

Beide Bewertungen sollten durchgeführt, dokumentiert und von dir als Nutzer genehmigt sein, bevor die Web-App eingesetzt wird.<br><br>
<hr><br>

<strong>5. Zero Data Retention (ZDR) und Datenspeicherung bei OpenAI</strong><br><br>

<strong>OpenAIs Standardrichtlinie</strong><br>
Nach der OpenAI-Richtlinie zur API-Datennutzung werden Daten, die an die API gesendet werden, nicht zum Training der Modelle verwendet. Die Daten können jedoch vorübergehend (typischerweise bis zu 30 Tage) für Missbrauchs­überwachung und Fehler­behebung gespeichert werden, bevor sie gelöscht werden.<br><br>

<strong>Zero Data Retention (ZDR)</strong><br>
OpenAI bietet ZDR für einige größere Kunden nach individueller Vereinbarung an, jedoch ist dies für die reguläre API-Nutzung nicht Standard und daher für diese App nicht aktiviert.<br><br>

<strong>Weiteres Vorgehen</strong><br>
Künftige Versionen der App können eine Unterstützung alternativer KI-Anbieter prüfen, die ZDR standardmäßig anbieten (z. B. bestimmte Dienste auf Microsoft Azure). Etwaige Updates hierzu werden über die Web-App kommuniziert.<br><br>
<hr><br>

<strong>6. Voraussetzungen für einen potenziellen klinischen Einsatz</strong><br><br>
Deine eigene Bewertung ist entscheidend: Die rechtmäßige Nutzung dieses Werkzeugs mit Patienten­daten hängt ausschließlich von deiner gründlichen Beurteilung ab. Du musst – auf Basis des DPA mit OpenAI, der DPIA und der TIA – selbst zu dem Schluss kommen, ob die Nutzung vertretbar ist und das Restrisiko für deine Praxis akzeptabel bleibt.<br><br>

<strong>Mindestanforderungen vor der Nutzung mit Patientendaten:</strong><br>
- Ein gültiger DPA mit OpenAI ist abgeschlossen.<br>
- Eine unternehmens­spezifische DPIA und TIA sind durchgeführt, genehmigt und kommen zu einem akzeptablen Restrisiko.<br>
- Inhaltsverantwortung: Du trägst die Verantwortung für alle Inhalte, die du über deinen API-Schlüssel an OpenAI sendest, und musst den generierten Notizentwurf vor einer etwaigen Übernahme in die Patientenakte fachlich prüfen.<br><br>
<hr><br>

<strong>7. Übersicht über die Datenspeicherung</strong><br><br>
<table style="border-collapse:collapse;width:100%;">
  <thead>
    <tr>
      <th style="border:1px solid #ccc;padding:4px;">Datentyp</th>
      <th style="border:1px solid #ccc;padding:4px;">Speicherort</th>
      <th style="border:1px solid #ccc;padding:4px;">Speicherdauer</th>
      <th style="border:1px solid #ccc;padding:4px;">Zugriff</th>
    </tr>
  </thead>
  <tbody>
    <tr>
      <td style="border:1px solid #ccc;padding:4px;">Dein OpenAI-API-Schlüssel</td>
      <td style="border:1px solid #ccc;padding:4px;">SessionStorage im Browser</td>
      <td style="border:1px solid #ccc;padding:4px;">Bis du die Web-App oder den Browser schließt</td>
      <td style="border:1px solid #ccc;padding:4px;">Nur du und dein Browser</td>
    </tr>
    <tr>
      <td style="border:1px solid #ccc;padding:4px;">Audiosegmente während der Aufnahme</td>
      <td style="border:1px solid #ccc;padding:4px;">Arbeitsspeicher (RAM) des Browsers</td>
      <td style="border:1px solid #ccc;padding:4px;">Nur während Aufnahme / Verarbeitung. Nach der Verarbeitung nicht bei OpenAI gespeichert</td>
      <td style="border:1px solid #ccc;padding:4px;">Nur du und dein Browser</td>
    </tr>
    <tr>
      <td style="border:1px solid #ccc;padding:4px;">Text / Notizentwurf</td>
      <td style="border:1px solid #ccc;padding:4px;">OpenAI-API (vorübergehend)</td>
      <td style="border:1px solid #ccc;padding:4px;">Max. 30 Tage bei OpenAI</td>
      <td style="border:1px solid #ccc;padding:4px;">Du, OpenAI (vorübergehend)</td>
    </tr>
    <tr>
      <td style="border:1px solid #ccc;padding:4px;">Anweisungen / Prompts</td>
      <td style="border:1px solid #ccc;padding:4px;">Lokal im Browser. Wenn du dich in der Web-App auf demselben Browser, Gerät und mit demselben API-Schlüssel anmeldest, sind deine gespeicherten Prompts erneut verfügbar</td>
      <td style="border:1px solid #ccc;padding:4px;">Bis du sie löschst</td>
      <td style="border:1px solid #ccc;padding:4px;">Du und dein Browser</td>
    </tr>
  </tbody>
</table><br><br>
<hr><br>

<strong>8. Quellcode</strong><br><br>
- Der Quellcode ist offen einsehbar und läuft lokal in deinem Browser.<br><br>
<hr><br>

<strong>9. Cookies und Werbung</strong><br><br>
Wir verwenden Cookies ausschließlich, um relevante Werbung über Google Ads anzuzeigen sowie für Sprachauswahl, Einwilligungen und das Speichern deiner angepassten Prompts. Die Cookies speichern keine Personen­daten, die über das für Funktionalität und Personalisierung notwendige Maß hinausgehen. Die Cookies von Google haben keinen Zugriff auf Daten im Zusammenhang mit Audioaufnahmen und generiertem Text (Patientendaten).
`,
  aboutModalHeading: "Über uns",
  aboutModalText: `Diese Website wurde entwickelt, um Gesundheitsfachkräfte und andere Nutzer mit direktem Zugang zu hochwertiger Spracherkennung und klinischer Notizgenerierung zu versorgen – ohne unnötige Kosten oder Zwischenhändler.<br><br>
Durch die Verwendung Ihres eigenen OpenAI API-Schlüssels verbinden Sie sich direkt mit der Quelle der Technologie. Das bedeutet, dass Sie nur die tatsächlichen Nutzungskosten zahlen, die von OpenAI festgelegt werden, ohne Aufschläge oder Abonnementgebühren.<br><br>
Viele bestehende Anbieter offerieren ähnliche Dienste, verlangen jedoch deutlich mehr – oftmals 8 bis 10 Mal die tatsächlichen Kosten der zugrunde liegenden Technologie. Diese Plattform bietet dieselbe Funktionalität zu einem Bruchteil des Preises.<br><br>
<strong>Wichtige Punkte:</strong><br>
• Kein Abonnement, kein Konto erforderlich.<br>
• Sie zahlen nur OpenAI direkt für die tatsächlich genutzte Leistung.<br>
• Die Website selbst ist völlig kostenlos.<br><br>
Damit wir diesen kostenlosen Dienst weiterhin anbieten können, würden wir uns sehr freuen, wenn du der Anzeige von Werbung über Google Ads zustimmst. Die Werbeeinnahmen helfen uns, die Kosten für Hosting und Betrieb zu decken, damit der Dienst für alle verfügbar bleiben kann.`,
  guideModalHeading: "Anleitung",
guideModalText: `Um diese Webanwendung zu nutzen, müssen Sie zunächst ein OpenAI-API-Profil erstellen, einen API-Schlüssel generieren und sicherstellen, dass Ihr OpenAI-Guthaben ausreichend ist. Kopieren Sie anschließend den API-Schlüssel und fügen Sie ihn in das dafür vorgesehene Feld ein. Sobald Sie die Eingabetaste drücken, speichert die Webanwendung den API-Schlüssel nur temporär für die aktuelle Sitzung – dieser Schlüssel stellt die Verbindung zu den OpenAI-Servern her, damit Sprach-zu-Text-Transkription und Notizenerstellung funktionieren. Bitte beachten Sie, dass Ihnen jede ausgeführte Aufgabe (Sprach-zu-Text und/oder Notizenerstellung) sofort in Rechnung gestellt wird. Weitere Informationen zu den Kosten finden Sie im Abschnitt „Kosteninformationen“ auf der Startseite. Wir empfehlen allen Nutzern, vor der Verwendung der App die Datenschutz- und Informationshinweise auf der Startseite zu lesen.
<br><br>
<strong>1. Erstellen Sie Ihr OpenAI-API-Profil</strong><br>
Um loszulegen, müssen Sie ein Profil auf der OpenAI-API-Plattform anlegen. Dieses Profil dient als Ihr Konto zur Verwaltung von API-Schlüsseln und zur Abrechnung. Rufen Sie dazu <a href="https://platform.openai.com/signup" style="color:blue;">OpenAI API Registrierung</a> auf. Folgen Sie den Anweisungen und legen Sie einen Nutzer an. Nach der Registrierung haben Sie Zugriff auf Ihr Dashboard, wo Sie einen persönlichen API-Schlüssel generieren und Guthaben aufladen können.
<br><br>
<strong>2. Generieren Sie einen API-Schlüssel</strong><br>
Nachdem Sie Ihr Profil erstellt haben, generieren Sie einen API-Schlüssel, indem Sie zu <a href="https://platform.openai.com/account/api-keys" style="color:blue;">API-Schlüsselverwaltung</a> gehen. Klicken Sie auf die Schaltfläche zum Erstellen eines neuen API-Schlüssels. Wichtig: Sie sehen den Schlüssel nur einmal. Kopieren Sie ihn sofort und bewahren Sie ihn sicher auf (z. B. in einer Textdatei). Sollten Sie den Schlüssel verlieren oder den Verdacht haben, dass er kompromittiert wurde, können Sie ihn an derselben Stelle deaktivieren/löschen und gleichzeitig einen neuen erstellen.
<br><br>
<strong>3. Laden Sie Guthaben auf Ihr OpenAI-Konto</strong><br>
Damit die Webanwendung funktioniert, muss Ihr OpenAI-Konto über ausreichend Guthaben verfügen. Besuchen Sie <a href="https://platform.openai.com/account/billing/overview" style="color:blue;">Abrechnungs- und Zahlungsübersicht</a>, um Guthaben aufzuladen. Sie können jederzeit einen beliebigen Betrag transferieren. Solange ausreichend Guthaben verfügbar ist, können Sie alle Funktionen dieser Webanwendung nutzen – jede Aufgabe wird sofort abgerechnet. Eine detaillierte Preisübersicht finden Sie im Abschnitt „Kosteninformationen“.
<br><br>
<strong>Sicherheitshinweis zur Sitzung</strong><br>
Wenn Sie sich einloggen, indem Sie den API-Schlüssel in das Feld auf dieser Startseite eingeben und die Eingabetaste drücken, wird dieser nur temporär in Ihrer Browsersitzung gespeichert. Das bedeutet, dass der Schlüssel nicht mehr verfügbar ist, wenn Sie die Seite verlassen, den Browser schließen oder den Computer ausschalten. Beim nächsten Besuch der Webanwendung müssen Sie den Schlüssel erneut einfügen, um die Sicherheit Ihres Schlüssels zu gewährleisten.`,

  priceButton: "Preis",
  priceModalHeading: "Preis",
priceModalText: `
<div>
  <p><strong>Kostenübersicht</strong></p>
  <p>Sie zahlen nur für das, was Sie tatsächlich nutzen – direkt an die Quelle, ohne teure Zwischenhändler. Kein Abo. Keine Bindung.</p>

  <p><strong>Preise:</strong></p>
  <ul>
    <li>Spracherkennung: $0.006 pro Minute</li>
    <li>Notizerstellung: $5 pro 1 Million Tokens (Input) und $10 pro 1 Million Tokens (Output)</li>
  </ul>

  <p><strong>Beispiel – 15-minütige Konsultation:</strong></p>
  <ul>
    <li>Spracherkennung: 15 × $0.006 = $0.09</li>
    <li>Notizerstellung: typischerweise zwischen $0.005 und $0.01</li>
    <li>Gesamt: etwa $0.10 für die gesamte Konsultation</li>
  </ul>

  <p><strong>Monatliche Beispielkosten bei voller Nutzung:</strong></p>
  <ul>
    <li>20 Konsultationen pro Tag × 4 Tage pro Woche × 4 Wochen = 320 Konsultationen</li>
    <li>Gesamtkosten pro Monat: etwa $30–31</li>
  </ul>

  <p><strong>Sie zahlen nur bei Nutzung:</strong><br>
  Bei Urlaub, Krankheit oder Elternzeit fallen keine Kosten an.</p>
</div>
`,
};

export const transcribeTranslations = {
  pageTitle: "Transkriptionstool mit Werbung und Anleitung",
  openaiUsageLinkText: "Kostenübersicht",
  openaiWalletLinkText: "Kontostand",
  btnFunctions: "Funktionen",
  btnGuide: "Anleitung",
  backToHome: "Zurück zur Startseite",
  recordingAreaTitle: "Aufnahmebereich",
  recordTimer: "Aufnahmetimer: 0 sek",
  transcribeTimer: "Abschlusstimer: 0 sek",
  transcriptionPlaceholder: "Transkriptionsergebnis wird hier angezeigt...",
  startButton: "Aufnahme starten",
  readFirstText: "Erst lesen! ➔",
  stopButton: "Stoppen/Abschließen",
  pauseButton: "Aufnahme pausieren",
  statusMessage: "Willkommen! Klicken Sie auf 'Aufnahme starten', um zu beginnen.",
  noteGenerationTitle: "Notizenerstellung",
  generateNoteButton: "Notiz generieren",
  noteTimer: "Notiz-Timer: 0 sek",
  generatedNotePlaceholder: "Generierte Notiz erscheint hier...",
  customPromptTitle: "Benutzerdefinierter Prompt",
  promptSlotLabel: "Prompt-Slot:",
  customPromptPlaceholder: "Benutzerdefinierten Prompt hier eingeben",
  adUnitText: "Ihre Anzeige hier",
  guideHeading: "Anleitung & Instruktionen",
guideText: `Willkommen bei <strong>Transcribe Notes</strong>. Diese Anwendung ermöglicht es medizinischem Fachpersonal, Therapeut:innen und anderen Anwender:innen, Gespräche aufzuzeichnen und zu transkribieren sowie professionelle Notizen mithilfe eines KI-gestützten Notizgenerators zu erstellen.<br><br>

<strong>So verwendest du die Funktionen:</strong><br><br>

<ul>
  <li><strong>Aufnahme:</strong> Die Einwilligung des Patienten muss stets eingeholt werden, bevor diese Anwendung verwendet wird. Klicke auf "Aufnahme starten", um mit der Tonaufnahme zu beginnen. Alle 2 Minuten wird ein Audioabschnitt automatisch an die Server von OpenAI gesendet, um transkribiert zu werden. Die Transkripte erscheinen fortlaufend im Transkriptionsfeld.<br><br>
  <strong><u>Wichtig:</u> Die Aufnahmefunktion funktioniert nicht in allen Webbrowsern. Wir empfehlen die Verwendung von <strong>Google Chrome</strong> oder <strong>Microsoft Edge</strong>.</strong></li><br>

  <li><strong>Pausieren und Fortsetzen:</strong> Sie können die "Pause"-Schaltfläche verwenden, um die Aufnahme vorübergehend zu stoppen – zum Beispiel, wenn die Konsultation unterbrochen wird oder Sie kurz das Büro verlassen müssen. Wenn Sie auf "Pause" klicken, wird das aktuelle Audiosegment hochgeladen und transkribiert, und die Aufnahme pausiert. Wenn Sie bereit sind fortzufahren, klicken Sie auf "Fortsetzen", und die Aufnahme wird automatisch mit dem nächsten Segment fortgesetzt. Der Timer läuft dort weiter, wo er gestoppt wurde, und die Sitzung kann wie gewohnt mit "Stopp/Abschließen" beendet werden.</li><br>

  <li><strong>Abschluss:</strong> Wenn du auf "Stopp/Fertig" klickst, wird die Aufnahme beendet. Der Abschlusstimer zählt, bis das vollständige Transkript empfangen wurde (in der Regel innerhalb von 5–10 Sekunden).</li><br>

  <li><strong>Benutzerdefinierter Prompt:</strong> Wähle rechts einen Prompt-Slot (1–10) aus und gib deinen eigenen Prompt ein. Dein Prompt wird automatisch gespeichert und mit deinem API-Schlüssel verknüpft. Du kannst jeden beliebigen Prompt erstellen, der zu deinem Dokumentationsstil, Tonfall und fachlichen Fokus passt. So hast du volle Kontrolle über die Generierung deiner Notizen.</li><br>

  <li><strong>Notiz generieren:</strong> Sobald die Transkription abgeschlossen ist, klicke auf "Notiz generieren", um eine medizinische Notiz basierend auf deinem Transkript und dem gewählten Prompt zu erstellen. Generierte medizinische Notizen müssen vor der Verwendung von medizinischem Fachpersonal überprüft und validiert werden.</li><br>

  <li><strong>Kostenübersicht:</strong> Um deine aktuellen Nutzungskosten bei OpenAI zu überprüfen, klicke auf den Link zur Kostenübersicht oben rechts auf dieser Seite.</li><br>

  <li><strong>Sicherheit:</strong> Deine Audioaufnahme wird direkt an die API-Server von OpenAI gesendet, die die Daten nicht speichern und nur für die Transkription verwenden. Der transkribierte Text wird nur in deinem Browser angezeigt und <strong>er wird gelöscht/verschwindet, sobald du den Browser schließt oder neue Inhalte lädst.</strong></li><br>

  <li><strong>Guide-Schaltfläche:</strong> Klicke erneut auf die "Guide"-Schaltfläche, um zur Hauptansicht zurückzukehren.</li>
</ul><br><br>

<strong>Beispiel-Prompts:</strong><br><br>

<strong>Konsultation:</strong><br>
"Systemprompt – Medizinischer Notizgenerator

Erstelle eine medizinisch präzise, dokumentationsfertige Notiz basierend auf einem transkribierten Arzt-Patienten-Gespräch. Verwende folgende Struktur (sofern im Diktat nicht anders angegeben):
Hintergrund (nur bei relevanter Vorgeschichte), Aktuelle Beschwerden/Anamnese, Untersuchung (stichpunktartig), Einschätzung, Plan.

Regeln:
– Keine Informationen, Untersuchungen oder Befunde einfügen, die nicht ausdrücklich erwähnt wurden.
– Negative Befunde nur, wenn erwähnt.
– Blutuntersuchungen: schreibe “relevante Blutuntersuchungen werden veranlasst”, ohne sie aufzulisten.
– Offensichtliche Rechtschreibfehler bei Medikamentennamen korrigieren.
– Keine Sonderzeichen oder Zeilenumbrüche vor Überschriften verwenden.
– Halte dich an explizite Anweisungen des Arztes bzgl. Stil, Länge oder Formulierungen.

Wenn der Arzt nach dem Gespräch noch Anmerkungen macht, sind diese zu berücksichtigen. Die Notiz sollte sprachlich gut ausgearbeitet sein."

<br><br>

<strong>Brief an den Patienten:</strong><br>
"Schreibe einen Brief vom Arzt an den Patienten. Beginne mit Hallo \\"Name\\", und schließe mit<br>
Mit freundlichen Grüßen<br>
\\"Ihr Name\\"<br>
\\"Praxisname\\"<br>
Der Brief soll professionell und formell formuliert sein. Du kannst den Text stilistisch leicht verbessern."

<br><br>

Diese Beispiele funktionieren gut, aber du kannst sie gern an deinen Dokumentationsstil, deine Fachrichtung oder Konsultationstypen anpassen oder ganz eigene Prompts erstellen.
`,
};
