import { renderSecondary, secondaryNames } from './secondary-sections.mjs?v=20261025-secondary1';
import { clockLabel } from './wav-timing.mjs?v=20261015-clock1';
import { prepareAudio } from './audio-import.mjs?v=20261025-secondary1';
import { prepareManualAudio } from './manual-vad.mjs?v=20261025-secondary1';
import { CONFIG } from './config.mjs';

export function renderTranscript(result, speakers, timing = null) {
  const tokens = Array.isArray(result.tokens) ? result.tokens : [];
  if (!speakers || !tokens.some(token => token.speaker != null)) {
    return (result.text || tokens.map(token => token.text || '').join('')).trim();
  }
  const lines = []; let current = null, text = '', startedAt = null;
  const flush = () => {
    const stamp = clockLabel(timing, startedAt);
    if (text.trim()) lines.push(`${stamp ? `(${stamp}) ` : ''}${current == null ? '' : `Speaker ${current}: `}${text.trim()}`);
    text = ''; startedAt = null;
  };
  for (const token of tokens) {
    const next = token.speaker ?? current;
    if (next !== current && text.trim()) flush();
    current = next;
    if (startedAt == null && token.text?.trim() && Number.isFinite(token.start_ms)) startedAt = token.start_ms;
    text += token.text || '';
  }
  flush(); return lines.join('\n\n');
}

const wait = ms => new Promise(resolve => setTimeout(resolve, ms));
export async function transcribeFile(file, apiKey, speakers, onStatus = () => {}, { manualVAD = false } = {}) {
  let fileId, transcriptionId;
  const request = async (path, options = {}) => {
    const response = await fetch(`${CONFIG.sonioxBase}/${path}`, {
      ...options, cache: 'no-store', signal: AbortSignal.timeout(120000),
      headers: { Authorization: `Bearer ${apiKey}`, ...options.headers },
    });
    if (!response.ok) {
      const error = new Error(`Soniox request failed (${response.status}).`);
      error.status = response.status; throw error;
    }
    return response;
  };
  const cleanup = async path => {
    for (let attempt = 0; attempt < 3; attempt++) {
      try { await request(path, { method: 'DELETE' }); return true; }
      catch (error) { if (error.status === 404) return true; }
      if (attempt < 2) await wait(1000 * (attempt + 1));
    }
    return false;
  };
  let cleanupOK = true;
  try {
    onStatus('Preparing audio…');
    const prepared = manualVAD ? await prepareManualAudio(file, onStatus) :
      await prepareAudio(file, value => onStatus(`Preparing audio… ${Math.round(value * 100)}%`));
    if (prepared.empty) throw new Error(manualVAD ? 'No speech detected.' : 'This recording contains no retained speech.');
    onStatus('Uploading…');
    const form = new FormData(); form.append('file', prepared.file, prepared.file.name || file.name);
    const upload = await (await request('files', { method: 'POST', body: form })).json();
    fileId = upload.id;
    if (!fileId) throw new Error('Soniox did not return a file ID.');
    const job = await (await request('transcriptions', { method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify({
      model: CONFIG.sonioxModel, file_id: fileId,
      enable_speaker_diarization: !!speakers || !!prepared.secondary, enable_language_identification: true,
    }) })).json();
    transcriptionId = job.id;
    if (!transcriptionId) throw new Error('Soniox did not return a transcription ID.');
    onStatus('Transcribing…');
    const deadline = Date.now() + 60 * 60 * 1000;
    while (true) {
      const state = await (await request(`transcriptions/${encodeURIComponent(transcriptionId)}`)).json();
      if (state.status === 'completed') break;
      if (state.status === 'error') throw new Error('Soniox could not transcribe this file.');
      if (Date.now() > deadline) throw new Error('Transcription timed out.');
      await wait(2000);
    }
    const result = await (await request(`transcriptions/${encodeURIComponent(transcriptionId)}/transcript`)).json();
    const text = prepared.secondary ? renderSecondary(result, prepared.secondary, renderTranscript) : renderTranscript(result, speakers, prepared.timing);
    // Display the result before deleting provider resources.
    onStatus('Cleaning up…', text, false, prepared.secondary ? {filename:secondaryNames(prepared.secondary).transcript} : null);
    return text;
  } finally {
    if (transcriptionId) cleanupOK = await cleanup(`transcriptions/${encodeURIComponent(transcriptionId)}`) && cleanupOK;
    if (fileId) cleanupOK = await cleanup(`files/${encodeURIComponent(fileId)}`) && cleanupOK;
    if (!cleanupOK) onStatus('Provider cleanup failed. Remove this upload from your Soniox account.', undefined, true);
    apiKey = '';
  }
}
