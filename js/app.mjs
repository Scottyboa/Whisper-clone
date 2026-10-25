import { Recorder } from './recorder.mjs?v=20261021-sound1';
import { createDriveImportPrompt } from './drive-import-prompt.mjs?v=20261018-folders1';
import { DeviceControl } from './device-control.mjs?v=20261021-sound1';
import { DevicesPanel, createAbortPrompt } from './devices-panel.mjs?v=20261021-sound1';
import { clock, duration, dateStamp, timeStamp, recordingName, recordingTranscriptName, download } from './audio.mjs?v=20261015-clock1';
import { MailControl } from './graph.mjs?v=20261023-upload1';
import { loadGoogle, importSonioxKey } from './drive.mjs';
import { transcribeFile } from './soniox.mjs?v=20261025-secondary3';
import { mergeSecondaryRecordings } from './secondary-recordings.mjs?v=20261025-secondary3';
import { sortSecondaryFiles } from './secondary-sections.mjs?v=20261025-secondary3';
import { createSecondaryPrompt } from './secondary-prompt.mjs?v=20261025-secondary-options1';
import { prepareManualAudio, cancelManualVAD } from './manual-vad.mjs?v=20261025-secondary3';
import { vadDownloadFile } from './vad-download.mjs?v=20261025-secondary3';
import { cancelFlacTasks } from './flac-tasks.mjs?v=20261017-flac2';
import { PrivacyView } from './privacy-view.mjs?v=20261014-demo1';
import { TranscriptDrive } from './transcript-drive.mjs?v=20261018-folders1';
import { AppGuide } from './app-guide.mjs?v=20261015-guide1';

// MSAL's parent window consumes its popup response. Do not start a second
// recorder, alter the URL, or consume the authorization code in this popup.
const callbackPopup = window.opener && /(?:^|[?#&])(?:code|error)=/.test(location.hash || location.search);
if (!callbackPopup) bootstrap();

function bootstrap() {
  const $ = id => document.getElementById(id);
  new AppGuide({dialog:$('guideDialog'),button:$('guide'),code:$('guideCode'),close:$('guideClose')});
  const KEY = 'whisper-clone.soniox-key', HISTORY = 'whisper-clone.recordings';
  let apiKey = '', history = [], file = null, transcribing = false, linking = false, transcriptFilename = null;
  let wakeLock = null, wakeGeneration = 0, importBusy = false;
  let driveBusy = false, drivePending = 0, transcriptionPending = 0;
  let driveQueue = Promise.resolve(), transcriptionQueue = Promise.resolve(), audioDownloadQueue = Promise.resolve();
  let audioDownloadsPending = 0, pageClosing = false, vadProcessing = false;
  let commandGeneration = 0;
  $('speakers').checked = true;
  const message = (text = '', error = false) => { $('message').textContent = text; $('message').classList.toggle('error', error); };
  try {
    apiKey = sessionStorage.getItem(KEY) || '';
    const stored = JSON.parse(sessionStorage.getItem(HISTORY) || '[]');
    if (Array.isArray(stored)) history = stored.filter(e => typeof e.id === 'string' && [e.startedAt, e.endedAt, e.elapsedMs, e.audioMs].every(Number.isFinite) && e.startedAt > 0 && e.endedAt >= e.startedAt && e.elapsedMs >= 0 && e.audioMs >= 0)
      .map(({ id, startedAt, endedAt, elapsedMs, audioMs }) => ({ id, startedAt, endedAt, elapsedMs, audioMs }));
  } catch { message('Session storage is unavailable.', true); }

  const recorder = new Recorder({ onChange: updateRecorder });
  const mail = new MailControl({ onCommand: runCommand, preserveAuth:()=>devices.active, onStatus: status => {
    $('linkStatus').textContent = status;
    $('link').textContent = mail.active ? 'Unlink' : 'Link';
  } });
  // Initialize MSAL while idle; Link's popup can then open promptly on click.
  mail.client().catch(() => {});
  const drive = new TranscriptDrive({ client: () => mail.client(), linkedAccount: () => mail.account });
  const driveImportPrompt = createDriveImportPrompt({dialog:$('driveImportDialog'),paste:$('driveImportPaste'),zip:$('driveImportZip'),apply:$('driveImportApply'),close:$('driveImportClose'),
    title:$('driveImportTitle'),importOptions:$('driveImportOutputs'),help:$('driveImportHelp'),
    folders:[{name:'Transcripts',input:$('driveFolderOriginal')},{name:'translations',input:$('driveFolderTranslations')},{name:'temp',input:$('driveFolderTemp')}]});
  const secondaryPrompt = createSecondaryPrompt({dialog:$('secondaryDialog'),summary:$('secondarySummary'),
    transcribe:$('secondaryTranscribeOnly'),download:$('secondaryWithDownload'),apply:$('secondaryApply'),
    cancel:$('secondaryCancel'),close:$('secondaryClose')});
  const confirmAbort = createAbortPrompt({dialog:$('abortDialog'),text:$('abortQuestion'),yes:$('abortYes'),no:$('abortNo')});
  let deviceName = 'This computer';
  try { deviceName = localStorage.getItem('whisper-clone.device-name') || deviceName; } catch {}
  let panel;
  const devices = new DeviceControl({drive,execute:runCommand,name:deviceName,
    getStatus:()=>({state:recorder.state,startedAt:recorder.startedAt,transcribing,uploading:driveBusy,
      inputActivityVersion:1,lastSoundAt:recorder.lastSoundAt,
      audioReady:!!recorder.context && recorder.context.state !== 'closed'}),onChange:()=>panel?.render()});
  async function connectDevices() {
    const audio = recorder.unlock();
    await Promise.all([audio,devices.connect({account:mail.account || undefined})]);
  }
  panel = new DevicesPanel({devices,connect:connectDevices,confirmAbort,$});
  // Cached, already-consented sessions can announce their presence silently.
  // Start still requires audio to have been enabled locally on this page.
  devices.connect({interactive:false}).catch(()=>{});

  new PrivacyView({
    view: $('privacyView'), controls: document.querySelector('.privacy-controls'),
    code: $('privacyCode'), toggleButton: $('privacyToggle'),
  });

  function updateRecorder() {
    const state = recorder.state;
    const labels = { idle: 'Ready', starting: 'Starting…', recording: 'Recording', pausing: 'Pausing…', paused: 'Paused', resuming: 'Resuming…', stopping: 'Finishing…', aborting: 'Discarding…', error: 'Audio error' };
    $('recordStatus').textContent = labels[state];
    $('dot').classList.toggle('live', state === 'recording');
    $('dot').classList.toggle('paused', state === 'paused');
    $('start').disabled = state !== 'idle';
    $('pause').disabled = !['recording', 'paused'].includes(state);
    $('stop').disabled = !['recording', 'paused', 'error'].includes(state);
    $('abort').disabled = ['idle','aborting'].includes(state);
    $('pause').textContent = state === 'paused' ? 'Resume' : 'Pause';
  }
  function updateKey() {
    // Show a fixed mask rather than exposing the secret as an input value.
    $('key').value = apiKey ? '••••••••••••' : '';
    $('clear').disabled = !apiKey || transcribing;
    $('model').textContent = apiKey ? 'Speech-to-Text Model Soniox' : 'Transcript';
    $('speakerControl').hidden = !apiKey;
    $('speakers').disabled = transcribing;
    $('vadProcess').disabled = !file || transcribing || vadProcessing;
    $('transcribe').disabled = !apiKey || !file || transcribing || vadProcessing;
    $('import').disabled = transcribing || importBusy;
    $('upload').disabled = transcribing || vadProcessing;
    $('secondaryRec').disabled = transcribing || vadProcessing;
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
  async function driveAction(action, options) {
    // Export snapshots the current text. Import replaces the field only when
    // the user explicitly selects COMPLETE.txt insertion in its dialog.
    const text = $('transcript').value, exportName = transcriptFilename;
    return queueDrive(async () => {
      driveMessage('Connecting to OneDrive…');
      try {
        if (action === 'export') {
          const name = await drive.upload(text, {folders:options.folders, ...(exportName ? {name:exportName} : {})});
          driveMessage(`Saved ${name} to OneDrive: ${options.folders.join(', ')}.`);
        } else if (action === 'import') {
          const result = await drive.exportZip(driveMessage, {includeZip:options.zip,folders:options.folders});
          if (options.paste) { $('transcript').value = result.completeText; transcriptFilename = null; updateDrive(); }
          if (options.zip) download(result.blob, result.name);
          const actions = [options.paste ? 'Inserted COMPLETE.txt' : '', options.zip ? 'Downloaded ZIP' : ''].filter(Boolean);
          driveMessage(`${actions.join(' · ')} · ${result.count} text files.`);
        } else {
          const result = await drive.clear(count => confirm(`Delete ${count} text file${count === 1 ? '' : 's'} directly inside these OneDrive folders: ${options.folders.join(', ')}? Other files and folders will be kept.`), driveMessage, {folders:options.folders});
          driveMessage(result.cancelled ? 'Clear cancelled.' : `Deleted ${result.count} text file${result.count === 1 ? '' : 's'} from OneDrive: ${options.folders.join(', ')}.`);
        }
      } catch (error) { driveMessage(error.message || 'OneDrive operation failed.', true); }
    });
  }
  for (const [id, action] of [['exportDrive','export'],['importDrive','import'],['clearDrive','clear']]) {
    $(id).addEventListener('click', async () => {
      const options = await driveImportPrompt(action);
      if (options) await driveAction(action, options);
    });
  }
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

  function queueAudioDownload(result) {
    audioDownloadsPending++;
    const job = audioDownloadQueue.then(() => {
      if (pageClosing) return;
      const status = $('audioDownloadStatus');
      status.classList.remove('error');
      // The recorder already finalized the Silero-retained PCM and clock map.
      // Download it directly, without restoring silence or encoding a FLAC.
      download(result.blob, recordingName(result.entry));
      status.textContent = `VAD WAV download requested · ${duration(result.entry.elapsedMs)} elapsed · ${duration(result.entry.audioMs)} retained audio`;
    }).catch(error => {
      $('audioDownloadStatus').classList.add('error');
      $('audioDownloadStatus').textContent = `Audio download failed. ${error.message || ''}`;
    }).finally(() => { audioDownloadsPending--; });
    audioDownloadQueue = job;
    return job;
  }

  async function runCommand(action) {
    const generation = ++commandGeneration;
    try {
      const automatic = action === 'stop-and-transcribe';
      // Snapshot configuration at command receipt, before Stop drains the VAD.
      const key = apiKey, account = mail.account || devices.account;
      const result = await recorder.command(automatic ? 'stop' : action);
      if (!result) {
        if (action === 'abort') { $('timer').textContent = clock(0); message('Recording discarded.'); }
        return;
      }
      const { entry, blob } = result;
      history.push(entry); renderHistory();
      // Metadata only. No audio, transcript, account address, or message body.
      try { sessionStorage.setItem(HISTORY, JSON.stringify(history)); }
      catch { message('History could not be saved for refresh.', true); }
      if (blob) {
        message(`Recording finished · ${duration(entry.elapsedMs)} elapsed · ${duration(entry.audioMs)} audio`);
      } else { message('No speech detected.'); }
      // Download independently of recording commands and transcription.
      // A recording with no retained speech has no WAV to download.
      if (blob) queueAudioDownload(result);
      else {
        $('audioDownloadStatus').classList.remove('error');
        $('audioDownloadStatus').textContent = 'No speech detected. No audio file downloaded.';
      }
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
          if (!key) keyError = new Error('Audio download queued, but automatic transcription needs a Soniox API key. Use Import Key.');
          else {
            const source = new File([blob], recordingName(entry), { type: 'audio/wav' });
            // Snapshot the completed recording, not the new active capture.
            queueTranscription(source, key, true, { entry, account }).catch(() => {});
          }
        }
        const restartError = await restart;
        if (restartError) {
          if (generation === commandGeneration && recorder.state === 'idle') $('recordStatus').textContent = 'Restart failed — click Start to retry';
          throw new Error(`The new recording could not start. ${restartError.message || 'Check microphone access.'} ${blob && key ? 'The previous recording will still be transcribed.' : 'The previous recording was finalized.'}`);
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
  $('abort').addEventListener('click', async () => {
    if (await confirmAbort()) runCommand('abort').catch(() => {});
  });
  setInterval(() => {
    if (recorder.startedAt != null) $('timer').textContent = clock(Date.now() - recorder.startedAt);
  }, 250);

  $('link').addEventListener('click', async () => {
    if (mail.active) { mail.unlink({clearCache:!devices.active}); return; }
    if (linking) return;
    linking = true; $('link').disabled = true;
    try {
      // Unlock capture on this deliberate click, before Microsoft opens.
      const ready = recorder.unlock();
      const linked = mail.link();
      await Promise.all([ready, linked]);
      if (devices.active && devices.account?.homeAccountId !== mail.account?.homeAccountId) devices.disconnect();
      try { await devices.connect({interactive:false,account:mail.account}); }
      catch (error) { message(`Email linked. Devices: ${error.message}`,true); }
    } catch (error) { mail.unlink({clearCache:!devices.active}); message(error.message || 'Microsoft sign-in failed.', true); }
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
    apiKey = ''; updateKey();
  });

  $('upload').addEventListener('click', () => $('file').click());
  $('file').addEventListener('change', () => {
    const selected = $('file').files?.[0];
    if (!selected) return;
    file = selected; $('fileName').textContent = file.name; updateKey();
  });
  $('vadProcess').addEventListener('click', async () => {
    if (!file || transcribing || vadProcessing) return;
    const source = file, status = $('vadStatus');
    vadProcessing = true; updateKey(); status.classList.remove('error');
    try {
      const result = await prepareManualAudio(source, text => { status.textContent = text; });
      if (pageClosing) return;
      if (result.empty) { status.textContent = 'No speech detected. No file downloaded.'; return; }
      const output = await vadDownloadFile(result);
      if (pageClosing) return;
      download(output, output.name);
      status.textContent = `VAD WAV download requested: ${output.name}`;
    } catch (error) {
      status.classList.add('error'); status.textContent = `VAD processing failed. ${error.message || ''}`;
    } finally { vadProcessing = false; updateKey(); }
  });
  $('secondaryRec').addEventListener('click', () => {
    if (transcribing || vadProcessing) return;
    if (!apiKey) { message('Import a Soniox key before using Secondary rec.', true); return; }
    $('secondaryFiles').value = ''; $('secondaryFiles').click();
  });
  $('secondaryFiles').addEventListener('change', async () => {
    const selected = Array.from($('secondaryFiles').files || []);
    if (!selected.length || transcribing || vadProcessing) return;
    if (!apiKey) { message('Import a Soniox key before using Secondary rec.', true); return; }
    try {
      const sorted = sortSecondaryFiles(selected), first = sorted[0].source, last = sorted.at(-1).source;
      const options = await secondaryPrompt(`Merge ${selected.length} secondary WAV file${selected.length === 1 ? '' : 's'} from ${first.date} ${first.time} to ${last.date} ${last.time}.`);
      if (!options || pageClosing) return;
      if (!apiKey) { message('Import a Soniox key before using Secondary rec.', true); return; }
      $('speakers').checked = true; $('secondaryStatus').textContent = ''; $('secondaryStatus').classList.remove('error');
      queueTranscription(null, apiKey, true, null, {files:sorted.map(item => item.file),download:options.download}).catch(() => {});
    } catch (error) { message(error.message || 'Secondary files could not be selected.', true); }
  });
  function queueTranscription(source, key, speakers, automatic = null, secondary = null) {
    transcriptionPending++; transcribing = true; updateKey();
    const job = transcriptionQueue.then(async () => {
      let cleanupFailed = false, outputFilename = null;
      try {
        if (secondary) {
          const merged = await mergeSecondaryRecordings(secondary.files, status => message(status));
          if (pageClosing) return;
          if (merged.empty) throw new Error('No speech detected in the selected secondary recordings. No file downloaded or sent to Soniox.');
          source = merged.file;
          if (secondary.download) {
            try {
              download(source, source.name);
              $('secondaryStatus').textContent = `Merged WAV download requested: ${source.name}`;
            } catch (error) {
              $('secondaryStatus').classList.add('error');
              $('secondaryStatus').textContent = `Merged WAV download failed; transcription will continue. ${error.message || ''}`;
            }
          } else $('secondaryStatus').textContent = 'VAD processing complete · no WAV download requested.';
        }
        if (pageClosing) return;
        // Keep the merged WAV and its source map available for a manual retry.
        file = source; $('fileName').textContent = source.name;
        const text = await transcribeFile(source, key, speakers, (status, transcript, error, context) => {
          if (transcript !== undefined) {
            outputFilename = context?.filename || null; transcriptFilename = outputFilename;
            $('transcript').value = transcript; updateDrive();
          }
          if (error) cleanupFailed = true;
          message(status, error);
        }, { manualVAD: !automatic && !secondary });
        $('transcript').value = text; transcriptFilename = outputFilename; updateDrive();
        if (automatic) {
          await queueDrive(async () => {
            driveMessage('Saving recording transcript to OneDrive…');
            try {
              const name = await drive.upload(text, {
                name: recordingTranscriptName(automatic.entry), interactive: false,
                account: automatic.account, folders: ['Transcripts', 'temp'],
              });
              driveMessage(`Saved ${name} to OneDrive: Transcripts and temp.`);
            } catch (error) {
              driveMessage(`Automatic upload failed. The transcript is in the output field; use EX.Drive to retry. ${error.message || ''}`, true);
              throw error;
            }
          });
        }
        if (!cleanupFailed) message(automatic ? 'Recording transcribed with speaker labels and saved to OneDrive.' : '');
      } catch (error) {
        message(error.message || 'Transcription failed. The audio file is selected for retry.', true);
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
    if (!file || !apiKey || transcribing || vadProcessing) return;
    queueTranscription(file, apiKey, $('speakers').checked).catch(() => {});
  });

  window.addEventListener('beforeunload', event => {
    if (recorder.state !== 'idle' || transcribing || driveBusy || audioDownloadsPending || vadProcessing) { event.preventDefault(); event.returnValue = ''; }
  });
  window.addEventListener('pagehide', () => {
    pageClosing = true; secondaryPrompt.cancel();
    devices.disconnect(); panel.dispose(); mail.unlink(); recorder.dispose(); cancelFlacTasks(); cancelManualVAD(); wakeGeneration++;
    wakeLock?.release().catch(() => {}); file = null;
  });
  window.addEventListener('pageshow', event => { if (event.persisted) location.reload(); });
  updateRecorder(); updateKey(); updateDrive(); renderHistory();
}
