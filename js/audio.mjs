export const SAMPLE_RATE = 16000;

// WhisperAzure/js/soniox.js batch settings (source commit 2ec1c0b).
export const VAD_RULES = Object.freeze({
  model: 'legacy', frameSamples: 1536,
  submitUserSpeechOnPause: true,
  positiveSpeechThreshold: 0.4,
  negativeSpeechThreshold: 0.35,
  redemptionFrames: 5,
  preSpeechPadFrames: 2,
  minSpeechFrames: 3,
});

export function toPCM(samples) {
  const pcm = new Int16Array(samples.length);
  for (let i = 0; i < samples.length; i++) {
    const s = Math.max(-1, Math.min(1, samples[i]));
    pcm[i] = s < 0 ? s * 0x8000 : s * 0x7fff;
  }
  return pcm;
}

export function wavBlob(parts) {
  const samples = parts.reduce((sum, part) => sum + part.length, 0);
  const bytes = samples * 2;
  if (bytes > 0xffffffff - 36) throw new Error('Recording is too large for a WAV file.');
  const header = new ArrayBuffer(44);
  const view = new DataView(header);
  const text = (offset, value) => [...value].forEach((c, i) => view.setUint8(offset + i, c.charCodeAt(0)));
  text(0, 'RIFF'); view.setUint32(4, 36 + bytes, true); text(8, 'WAVE');
  text(12, 'fmt '); view.setUint32(16, 16, true); view.setUint16(20, 1, true);
  view.setUint16(22, 1, true); view.setUint32(24, SAMPLE_RATE, true);
  view.setUint32(28, SAMPLE_RATE * 2, true); view.setUint16(32, 2, true);
  view.setUint16(34, 16, true); text(36, 'data'); view.setUint32(40, bytes, true);
  // Blob concatenation avoids allocating a second full PCM array.
  const littleEndian = new Uint8Array(new Uint16Array([1]).buffer)[0] === 1;
  const encoded = littleEndian ? parts : parts.map(part => {
    const result = new DataView(new ArrayBuffer(part.length * 2));
    part.forEach((sample, i) => result.setInt16(i * 2, sample, true));
    return result.buffer;
  });
  return new Blob([header, ...encoded], { type: 'audio/wav' });
}

const pad = value => String(value).padStart(2, '0');
export function clock(ms) {
  const s = Math.max(0, Math.floor(ms / 1000));
  return `${pad(Math.floor(s / 3600))}:${pad(Math.floor(s / 60) % 60)}:${pad(s % 60)}`;
}
export function duration(ms) {
  const s = Math.max(0, Math.round(ms / 1000));
  return `${Math.floor(s / 3600) ? `${Math.floor(s / 3600)}h ` : ''}${Math.floor(s / 60) % 60}m ${s % 60}s`;
}
export function dateStamp(date) { return `${date.getFullYear()}-${pad(date.getMonth() + 1)}-${pad(date.getDate())}`; }
export function timeStamp(date) { return `${pad(date.getHours())}:${pad(date.getMinutes())}:${pad(date.getSeconds())}`; }
export function recordingName(entry) {
  const start = new Date(entry.startedAt), end = new Date(entry.endedAt);
  const endDate = dateStamp(start) === dateStamp(end) ? '' : `${dateStamp(end)}_`;
  return `${dateStamp(start)}_${timeStamp(start).replaceAll(':', '-')}_to_${endDate}${timeStamp(end).replaceAll(':', '-')}_(${duration(entry.audioMs).replaceAll(' ', '')}).wav`;
}

export function recordingTranscriptName(entry) {
  const stamp = ms => {
    const date = new Date(ms);
    return `${dateStamp(date)}_${timeStamp(date).replaceAll(':', '-')}-${String(date.getMilliseconds()).padStart(3, '0')}`;
  };
  return `${stamp(entry.startedAt)}_to_${stamp(entry.endedAt)}_VAD-${duration(entry.audioMs).replaceAll(' ', '')}.txt`;
}

export function download(blob, filename) {
  const url = URL.createObjectURL(blob);
  const anchor = document.createElement('a');
  anchor.href = url; anchor.download = filename;
  document.body.append(anchor); anchor.click(); anchor.remove();
  // The URL is temporary; no recording is kept in history or browser storage.
  setTimeout(() => URL.revokeObjectURL(url), 60000);
}
