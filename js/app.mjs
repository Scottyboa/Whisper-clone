import { Recorder } from './recorder.mjs?v=20261015-clock1';
import { clock, duration, dateStamp, timeStamp, recordingName, recordingTranscriptName, download } from './audio.mjs?v=20261015-clock1';
import { MailControl } from './graph.mjs?v=20261015-auto1';
import { loadGoogle, importSonioxKey } from './drive.mjs';
import { transcribeFile } from './soniox.mjs?v=20261015-clock1';
import { PrivacyView } from './privacy-view.mjs?v=20261014-demo1';
import { TranscriptDrive } from './transcript-drive.mjs?v=20261015-titles1';

// MSAL's parent window consumes its popup response. Do not start a second
// recorder, alter the URL, or consume the authorization code in this popup.
const callbackPopup = window.opener && /(?:^|[?#&])(?:code|error)=/.test(location.hash || location.search);
if (!callbackPopup) bootstrap();

function bootstrap() {
  const $ = id => document.getElementById(id);
  const KEY = 'whisper-clone.soniox-key', HISTORY = 'whisper-clone.recordings';
  let apiKey = '', history = [], file = null, transcribing = false, linking = false;
  let wakeLock = null, wakeGeneration = 0, importBusy = false;
  let driveBusy = false, drivePending = 0, transcriptionPending = 0;
  let driveQueue = Promise.resolve(), transcriptionQueue = Promise.resolve();
  let commandGeneration = 0;
  const message = (text = '', error = false) => { $('message').textContent = text; $('message').classList.toggle('error', error); };
  try {
    apiKey = sessionStorage.getItem(KEY) || '';
    const stored = JSON.parse(sessionStorage.getItem(HISTORY) || '[]');
    if (Array.isArray(stored)) history = stored.filter(e => typeof e.id === 'string' && [e.startedAt, e.endedAt, e.elapsedMs, e.audioMs].every(Number.isFinite) && e.startedAt > 0 && e.endedAt >= e.startedAt && e.elapsedMs >= 0 && e.audioMs >= 0)
      .map(({ id, startedAt, endedAt, elapsedMs, audioMs }) => ({ id, startedAt, endedAt, elapsedMs, audioMs }));
  } catch { message('Session storage is unavailable.', true); }

  const recorder = new Recorder({ onChange: updateRecorder });
  const mail = new MailControl({ onCommand: runCommand, onStatus: status => {
    $('linkStatus').textContent = status;
    $('link').textContent = mail.active ? 'Unlink' : 'Link';
  } });
  // Initialize MSAL while idle; Link's popup can then open promptly on click.
  mail.client().catch(() => {});
  const drive = new TranscriptDrive({ client: () => mail.client(), linkedAccount: () => mail.account });

  new PrivacyView({
    view: $('privacyView'), controls: document.querySelector('.privacy-controls'),
    code: $('privacyCode'), toggleButton: $('privacyToggle'),
  });

  function updateRecorder() {
    const state = recorder.state;
    const labels = { idle: 'Ready', starting: 'Starting…', recording: 'Recording', pausing: 'Pausing…', paused: 'Paused', resuming: 'Resuming…', stopping: 'Finishing…', error: 'Audio error' };
    $('recordStatus').textContent = labels[state];
    $('dot').classList.toggle('live', state === 'recording');
    $('dot').classList.toggle('paused', state === 'paused');
    $('start').disabled = state !== 'idle';
    $('pause').disabled = !['recording', 'paused'].includes(state);
    $('stop').disabled = !['recording', 'paused', 'error'].includes(state);
    $('pause').textContent = state === 'paused' ? 'Resume' : 'Pause';
  }
  function updateKey() {
    // Show a fixed mask rather than exposing the secret as an input value.
    $('key').value = apiKey ? '••••••••••••' : '';
    $('clear').disabled = !apiKey || transcribing;
    $('model').textContent = apiKey ? 'Speech-to-Text Model Soniox' : 'Transcript';
    $('speakerControl').hidden = !apiKey;
    $('speakers').disabled = transcribing;
    $('transcribe').disabled = !apiKey || !file || transcribing;
    $('import').disabled = transcribing || importBusy;
    $('upload').disabled = transcribing;
  }
  const driveMessage = (text = '', error = false) => {
    $('driveMessage').textContent = text;
    $('driveMessage').classList.toggle('error', error);
  };
  function updateDrive() {
    $('exportDrive').disabled = driveBusy || !$('transcript').value.trim();
    $('importDrive').disabled = driveBusy;
    $('clearDrive').disabled = driveBusy;
  }
  function queueDrive(task) {
    drivePending++; driveBusy = true; updateDrive();
    const job = driveQueue.then(task).finally(() => {
      driveBusy = --drivePending > 0; updateDrive();
    });
    driveQueue = job.catch(() => {});
    return job;
  }
  async function driveAction(action) {
    if (driveBusy) return;
    // Snapshot only the text being uploaded; later edits and transcription
    // results are left in the field and never replaced by Drive operations.
    const text = $('transcript').value;
    return queueDrive(async () => {
      driveMessage('Connecting to OneDrive…');
      try {
        if (action === 'export') {
          const name = await drive.upload(text);
          driveMessage(`Saved ${name} to OneDrive.`);
        } else if (action === 'import') {
          const result = await drive.exportZip(driveMessage);
          download(result.blob, result.name);
          driveMessage(`Downloaded Transcripts ZIP · ${result.count} text files and COMPLETE.txt.`);
        } else {
          const result = await drive.clear(count => confirm(`Delete ${count} text file${count === 1 ? '' : 's'} directly inside this app’s OneDrive Transcripts folder? Other files and folders will be kept.`), driveMessage);
          driveMessage(result.cancelled ? 'Clear cancelled.' : `Deleted ${result.count} text file${result.count === 1 ? '' : 's'} from OneDrive Transcripts.`);
        }
      } catch (error) { driveMessage(error.message || 'OneDrive operation failed.', true); }
    });
  }
  $('exportDrive').addEventListener('click', () => driveAction('export'));
  $('importDrive').addEventListener('click', () => driveAction('import'));
  $('clearDrive').addEventListener('click', () => driveAction('clear'));
  $('transcript').addEventListener('input', updateDrive);
  function renderHistory() {
    $('history').replaceChildren();
    for (const entry of [...history].reverse()) {
      const start = new Date(entry.startedAt), end = new Date(entry.endedAt);
      const button = document.createElement('button'); button.type = 'button';
      const date = document.createElement('span'); date.className = 'date'; date.textContent = dateStamp(start);
      const time = document.createElement('span'); time.textContent = `${timeStamp(start)}–${dateStamp(start) !== dateStamp(end) ? `${dateStamp(end)} ` : ''}${timeStamp(end)}`;
      const audio = document.createElement('span'); audio.className = 'audio'; audio.textContent = `(audio: ${duration(entry.audioMs)})`;
      button.append(date, time, audio);
      button.addEventListener('click', () => {
        for (const other of $('history').children) other.classList.remove('selected');
        button.classList.add('selected'); $('historyDetail').hidden = false;
        $('historyDetail').replaceChildren();
        for (const [label, value] of [['Date', dateStamp(start)], ['Start', timeStamp(start)], ['Stop', `${dateStamp(start) !== dateStamp(end) ? `${dateStamp(end)} ` : ''}${timeStamp(end)}`], ['Elapsed', duration(entry.elapsedMs)], ['Audio', duration(entry.audioMs)]]) {
          const line = document.createElement('p'), name = document.createElement('strong'); name.textContent = `${label}: `;
          line.append(name, document.createTextNode(value)); $('historyDetail').append(line);
        }
      });
      $('history').append(button);
    }
  }

  async function runCommand(action) {
    const generation = ++commandGeneration;
    try {
      const automatic = action === 'stop-and-transcribe';
      // Snapshot configuration at command receipt, before Stop drains the VAD.
      const key = apiKey, account = mail.account;
      const result = await recorder.command(automatic ? 'stop' : action);
      if (!result) return;
      const { entry, blob } = result;
      history.push(entry); renderHistory();
      // Metadata only. No audio, transcript, account address, or message body.
      try { sessionStorage.setItem(HISTORY, JSON.stringify(history)); }
      catch { message('History could not be saved for refresh.', true); }
      if (blob) {
        message(`Recording finished · ${duration(entry.elapsedMs)} elapsed · ${duration(entry.audioMs)} audio`);
        try { download(blob, recordingName(entry)); }
        catch { message('The WAV download could not be started.', true); }
      } else { message('No speech detected.'); }
      $('timer').textContent = clock(entry.elapsedMs);
      if (automatic) {
        // Stop has drained the VAD and produced an independent WAV. Start the
        // next capture now; provider work must never delay or undo the restart.
        // A newer explicit command received during Stop takes precedence.
        const restart = generation === commandGeneration ? recorder.command('start').then(() => {
          if (generation === commandGeneration && recorder.state === 'recording') $('timer').textContent = clock(0);
          return null;
        }, error => error) : Promise.resolve(null);
        let keyError = null;
        if (blob) {
          if (!key) keyError = new Error('WAV download requested, but automatic transcription needs a Soniox API key. Use Import Key.');
          else {
            const source = new File([blob], recordingName(entry), { type: 'audio/wav' });
            // Snapshot the completed recording, not the new active capture.
            queueTranscription(source, key, true, { entry, account }).catch(() => {});
          }
        }
        const restartError = await restart;
        if (restartError) {
          if (generation === commandGeneration && recorder.state === 'idle') $('recordStatus').textContent = 'Restart failed — click Start to retry';
          throw new Error(`The new recording could not start. ${restartError.message || 'Check microphone access.'} ${blob && key ? 'The previous WAV will still be transcribed.' : 'The previous recording was finalized.'}`);
        }
        if (keyError) throw keyError;
      }
    } catch (error) { message(error.message || 'Recording failed.', true); throw error; }
  }
  $('start').addEventListener('click', () => {
    message('');
    recorder.unlock().then(() => runCommand('start')).catch(error => message(error.message, true));
  });
  $('pause').addEventListener('click', () => runCommand(recorder.state === 'paused' ? 'resume' : 'pause').catch(() => {}));
  $('stop').addEventListener('click', () => runCommand('stop').catch(() => {}));
  setInterval(() => {
    if (recorder.startedAt != null) $('timer').textContent = clock(Date.now() - recorder.startedAt);
  }, 250);

  $('link').addEventListener('click', async () => {
    if (mail.active) { mail.unlink(); return; }
    if (linking) return;
    linking = true; $('link').disabled = true;
    try {
      // Unlock capture on this deliberate click, before Microsoft opens.
      const ready = recorder.unlock();
      const linked = mail.link();
      await Promise.all([ready, linked]);
    } catch (error) { mail.unlink(); message(error.message || 'Microsoft sign-in failed.', true); }
    finally { linking = false; $('link').disabled = false; }
  });

  async function acquireWakeLock() {
    const generation = ++wakeGeneration;
    if (!$('awake').checked) return;
    if (!navigator.wakeLock) { $('awake').checked = false; $('awakeStatus').textContent = 'Unavailable'; return; }
    if (document.visibilityState !== 'visible') { $('awakeStatus').textContent = 'Inactive'; return; }
    if (wakeLock && !wakeLock.released) { $('awakeStatus').textContent = 'Active'; return; }
    try {
      const lock = await navigator.wakeLock.request('screen');
      if (generation !== wakeGeneration || !$('awake').checked) { await lock.release(); return; }
      wakeLock = lock; $('awakeStatus').textContent = 'Active';
      lock.addEventListener('release', () => {
        if (wakeLock === lock) { wakeLock = null; $('awakeStatus').textContent = $('awake').checked ? 'Inactive' : 'Off'; }
      });
    } catch { $('awakeStatus').textContent = 'Inactive'; }
  }
  $('awake').addEventListener('change', () => {
    if ($('awake').checked) acquireWakeLock();
    else { wakeGeneration++; wakeLock?.release().catch(() => {}); wakeLock = null; $('awakeStatus').textContent = 'Off'; }
  });
  document.addEventListener('visibilitychange', () => { if ($('awake').checked) acquireWakeLock(); });

  $('import').addEventListener('click', () => {
    $('backupPassword').value = ''; $('importStatus').textContent = '';
    $('confirmImport').disabled = true; $('importDialog').showModal();
    loadGoogle().then(() => { $('confirmImport').disabled = false; })
      .catch(error => { $('importStatus').textContent = error.message; });
  });
  $('cancelImport').addEventListener('click', () => { if (!importBusy) $('importDialog').close(); });
  $('importDialog').addEventListener('cancel', event => { if (importBusy) event.preventDefault(); });
  $('importDialog').addEventListener('close', () => { $('backupPassword').value = ''; });
  $('importForm').addEventListener('submit', async event => {
    event.preventDefault(); if (importBusy) return;
    importBusy = true; updateKey();
    $('confirmImport').disabled = true; $('cancelImport').disabled = true;
    $('importStatus').classList.remove('error'); $('importStatus').textContent = 'Importing…';
    let password = $('backupPassword').value;
    $('backupPassword').value = '';
    try {
      const imported = await importSonioxKey(password);
      // Fail the import if the requested session storage cannot retain the key.
      sessionStorage.setItem(KEY, imported); apiKey = imported;
      $('importDialog').close(); message('');
    } catch (error) {
      $('importStatus').classList.add('error'); $('importStatus').textContent = error.message || 'Key import failed.';
    } finally {
      password = ''; importBusy = false; $('confirmImport').disabled = false;
      $('cancelImport').disabled = false; updateKey();
    }
  });
  $('clear').addEventListener('click', () => {
    if (!confirm('Do you want to remove the API key?')) return;
    try { sessionStorage.removeItem(KEY); } catch { message('Could not clear the key.', true); return; }
    apiKey = ''; $('speakers').checked = false; updateKey();
  });

  $('upload').addEventListener('click', () => $('file').click());
  $('file').addEventListener('change', () => {
    const selected = $('file').files?.[0];
    if (!selected) return;
    file = selected; $('fileName').textContent = file.name; updateKey();
  });
  function queueTranscription(source, key, speakers, automatic = null) {
    transcriptionPending++; transcribing = true; updateKey();
    const job = transcriptionQueue.then(async () => {
      // Keep this recording available for a manual retry if a provider fails.
      file = source; $('fileName').textContent = source.name;
      let cleanupFailed = false;
      try {
        const text = await transcribeFile(source, key, speakers, (status, transcript, error) => {
          if (transcript !== undefined) { $('transcript').value = transcript; updateDrive(); }
          if (error) cleanupFailed = true;
          message(status, error);
        });
        $('transcript').value = text; updateDrive();
        if (automatic) {
          await queueDrive(async () => {
            driveMessage('Saving recording transcript to OneDrive…');
            try {
              const name = await drive.upload(text, {
                name: recordingTranscriptName(automatic.entry), interactive: false,
                account: automatic.account,
              });
              driveMessage(`Saved ${name} to OneDrive.`);
            } catch (error) {
              driveMessage(`Automatic upload failed. The transcript is in the output field; use EX.Drive to retry. ${error.message || ''}`, true);
              throw error;
            }
          });
        }
        if (!cleanupFailed) message(automatic ? 'Recording transcribed with speaker labels and saved to OneDrive.' : '');
      } catch (error) {
        message(error.message || 'Transcription failed. The WAV is selected for retry.', true);
        throw error;
      }
    }).finally(() => {
      transcribing = --transcriptionPending > 0; updateKey();
    });
    // Serialize manual and automatic jobs, and allow later jobs after a failure.
    transcriptionQueue = job.catch(() => {});
    return job;
  }
  $('transcribe').addEventListener('click', () => {
    if (!file || !apiKey || transcribing) return;
    queueTranscription(file, apiKey, $('speakers').checked).catch(() => {});
  });

  window.addEventListener('beforeunload', event => {
    if (recorder.state !== 'idle' || transcribing || driveBusy) { event.preventDefault(); event.returnValue = ''; }
  });
  window.addEventListener('pagehide', () => {
    mail.unlink(); recorder.dispose(); wakeGeneration++;
    wakeLock?.release().catch(() => {}); file = null;
  });
  window.addEventListener('pageshow', event => { if (event.persisted) location.reload(); });
  updateRecorder(); updateKey(); updateDrive(); renderHistory();
}
