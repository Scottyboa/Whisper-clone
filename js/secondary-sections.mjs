import { duration } from './audio.mjs?v=20261015-clock1';

const CHUNK = 'wcsr', MAX_BYTES = 2 * 1024 * 1024;
export const MAX_SECONDARY_FILES = 1000;
const osloClock = new Intl.DateTimeFormat('en-GB', {timeZone:'Europe/Oslo',
  year:'numeric', month:'2-digit', day:'2-digit', hour:'2-digit', minute:'2-digit', hourCycle:'h23'});
// This recorder stays on Norway's summer clock (UTC+02:00) all year.
// Derive the real instant from that fixed clock, then display Norway local time.
function recorderSource(name) {
  const match = /^R-(\d{1,12})_(\d{2})(\d{2})(\d{2})(\d{2})(\d{2})_SVOS\.wav$/i.exec(name || '');
  if (!match) throw new Error(`Unsupported secondary filename: ${name}. Expected R-00001_YYMMDDHHmm_SVOS.WAV.`);
  const [, sequence, yy, mm, dd, hh, min] = match;
  const year = 2000 + Number(yy), month = Number(mm), day = Number(dd);
  const date = new Date(Date.UTC(year, month - 1, day));
  if (date.getUTCFullYear() !== year || date.getUTCMonth() !== month - 1 || date.getUTCDate() !== day || Number(hh) > 23 || Number(min) > 59)
    throw new Error(`Invalid date or time in secondary filename: ${name}.`);
  return { name, date: `${year}-${mm}-${dd}`, time: `${hh}:${min}`, sequence: Number(sequence),
    at:Date.UTC(year, month - 1, day, Number(hh), Number(min)) - 120 * 60000 };
}
function norwaySource(raw) {
  const parts = Object.fromEntries(osloClock.formatToParts(raw.at).map(part => [part.type, part.value]));
  return {name:raw.name, date:`${parts.year}-${parts.month}-${parts.day}`, time:`${parts.hour}:${parts.minute}`, sequence:raw.sequence};
}
export function secondarySource(name) {
  return norwaySource(recorderSource(name));
}
export function sortSecondaryFiles(files) {
  if (!files?.length || files.length > MAX_SECONDARY_FILES) throw new Error(`Choose between 1 and ${MAX_SECONDARY_FILES} secondary WAV files.`);
  const seen = new Set();
  return Array.from(files, file => {
    const raw = recorderSource(file.name), source = norwaySource(raw), key = file.name.toLowerCase();
    if (seen.has(key)) throw new Error(`Duplicate secondary file: ${file.name}.`);
    seen.add(key); return { file, source, at:raw.at };
  }).sort((a, b) => a.at - b.at || a.source.sequence - b.source.sequence || a.source.name.localeCompare(b.source.name))
    .map(({file, source}) => ({file, source}));
}

export function validateSecondary(value, samples) {
  if (![1, 2].includes(value?.version) || value.sampleRate !== 16000 || !Number.isSafeInteger(samples) || samples <= 0 ||
      !Array.isArray(value.sources) || !value.sources.length || value.sources.length > MAX_SECONDARY_FILES ||
      !Array.isArray(value.ranges) || !value.ranges.length || value.ranges.length > 50000) throw new Error('Invalid secondary recording metadata.');
  const sources = value.sources.map(source => {
    const raw = recorderSource(source?.name), corrected = norwaySource(raw);
    // Version 1 stored the uncorrected filename clock. Normalize it once on
    // read; version 2 already stores Norway local labels. Never shift twice.
    const expected = value.version === 1 ? raw : corrected;
    if (expected.date !== source.date || expected.time !== source.time) throw new Error('Secondary recording dates do not match their filenames.');
    return corrected;
  });
  const sorted = sortSecondaryFiles(sources.map(source => ({name:source.name})));
  if (sorted.some((item, index) => item.source.name !== sources[index].name)) throw new Error('Secondary recordings are out of order.');
  let offset = 0, previous = -1;
  const ranges = value.ranges.map(range => {
    if (!Array.isArray(range) || range.length !== 3) throw new Error('Invalid secondary recording boundaries.');
    const [start, length, source] = range;
    if (start !== offset || !Number.isSafeInteger(length) || length <= 0 || !Number.isSafeInteger(source) ||
        source < previous || source < 0 || source >= sources.length) throw new Error('Invalid secondary recording boundaries.');
    offset += length; previous = source; return [start, length, source];
  });
  if (offset !== samples) throw new Error('Secondary recording boundaries do not match the audio.');
  return { version:2, sampleRate:16000, sources, ranges };
}
export function secondaryNames(map) {
  const first = map.sources[0], last = map.sources.at(-1);
  const time = source => source.time.replace(':', '-') + '-00';
  const start = `${first.date}_${time(first)}`, end = `${last.date}_${time(last)}`;
  const samples = map.ranges.reduce((sum, [, length]) => sum + length, 0);
  const vad = duration(samples / 16).replaceAll(' ', '');
  return {
    wav: `secondary rec - ${start}_to_${first.date === last.date ? time(last) : end}_(${vad}).wav`,
    transcript: `secondary rec - ${start}-000_to_${end}-000_VAD-${vad}.txt`,
  };
}
export function retainedSecondary(map, cuts, kept) {
  if (!map) return null;
  const ranges = []; let offset = 0, index = 0;
  for (const [start, length] of cuts) {
    const end = start + length;
    while (index < map.ranges.length && map.ranges[index][0] + map.ranges[index][1] <= start) index++;
    for (let i = index; i < map.ranges.length && map.ranges[i][0] < end; i++) {
      const [at, size, source] = map.ranges[i], count = Math.min(end, at + size) - Math.max(start, at);
      if (count <= 0) continue;
      if (ranges.at(-1)?.[2] === source) ranges.at(-1)[1] += count;
      else ranges.push([offset, count, source]);
      offset += count;
    }
  }
  return validateSecondary({...map, ranges}, kept);
}

export async function attachSecondary(file, map, samples = (file.size - 44) / 2) {
  // Both merge and manual VAD produce canonical mono 16 kHz, 16-bit WAVs.
  const valid = validateSecondary(map, samples);
  const bytes = new TextEncoder().encode(JSON.stringify(valid));
  if (bytes.length > MAX_BYTES) throw new Error('Secondary recording metadata is too large.');
  const chunk = new Uint8Array(8 + bytes.length + bytes.length % 2);
  chunk.set(new TextEncoder().encode(CHUNK)); new DataView(chunk.buffer).setUint32(4, bytes.length, true); chunk.set(bytes, 8);
  const prefix = new Uint8Array(await file.slice(0, 12).arrayBuffer());
  if (prefix.length !== 12 || new TextDecoder().decode(prefix.subarray(0, 4)) !== 'RIFF') throw new Error('The merged WAV could not be read.');
  if (file.size + chunk.length - 8 > 0xffffffff) throw new Error('The merged audio is too large for a WAV file.');
  new DataView(prefix.buffer).setUint32(4, file.size + chunk.length - 8, true);
  return new File([prefix, file.slice(12), chunk], file.name, {type:'audio/wav'});
}

export async function readSecondary(file) {
  if (file.size < 12) return null;
  const head = new Uint8Array(await file.slice(0, 12).arrayBuffer());
  const fourCC = bytes => new TextDecoder().decode(bytes);
  if (fourCC(head.subarray(0, 4)) !== 'RIFF' || fourCC(head.subarray(8)) !== 'WAVE') return null;
  if (new DataView(head.buffer).getUint32(4, true) + 8 !== file.size) return null;
  let offset = 12, chunks = 0, encoded = null, format = null, audioBytes = null;
  const keep = [];
  while (offset + 8 <= file.size && ++chunks <= 4096) {
    const header = new Uint8Array(await file.slice(offset, offset + 8).arrayBuffer());
    const id = fourCC(header.subarray(0, 4)), size = new DataView(header.buffer).getUint32(4, true);
    const next = offset + 8 + size + size % 2;
    if (next > file.size) { if (encoded !== null || id === CHUNK) throw new Error('The secondary WAV is incomplete.'); return null; }
    if (id === CHUNK) {
      if (encoded !== null || size > MAX_BYTES) throw new Error('Invalid secondary recording metadata.');
      encoded = await file.slice(offset + 8, offset + 8 + size).text();
    } else {
      keep.push(file.slice(offset, next));
      if (id === 'fmt ' && size >= 16) format = new DataView(await file.slice(offset + 8, offset + 24).arrayBuffer());
      if (id === 'data') audioBytes = audioBytes === null ? size : NaN;
    }
    offset = next;
  }
  if (encoded === null) return null;
  if (offset !== file.size || format?.getUint16(0, true) !== 1 || format.getUint16(2, true) !== 1 ||
      format.getUint32(4, true) !== 16000 || format.getUint16(14, true) !== 16 || !audioBytes || audioBytes % 2 !== 0)
    throw new Error('Unsupported secondary WAV format.');
  let map;
  try { map = validateSecondary(JSON.parse(encoded), audioBytes / 2); }
  catch { throw new Error('Invalid secondary recording metadata.'); }
  const payload = new Blob(keep);
  new DataView(head.buffer).setUint32(4, payload.size + 4, true);
  return {file:new File([head, payload], secondaryNames(map).wav, {type:'audio/wav'}), secondary:map};
}

export function renderSecondary(result, map, renderSpeakers) {
  const groups = map.sources.map(() => []), tokens = Array.isArray(result.tokens) ? result.tokens : [];
  const ends = map.ranges.map(([start, length]) => start + length);
  let previous = null;
  for (const token of tokens) {
    if (!token.text) continue;
    let source = previous;
    if (Number.isFinite(token.start_ms) && token.start_ms >= 0) {
      const sample = token.start_ms * 16;
      let lo = 0, hi = ends.length;
      while (lo < hi) { const mid = (lo + hi) >> 1; if (sample < ends[mid]) hi = mid; else lo = mid + 1; }
      if (lo === ends.length) {
        if (token.text.trim()) throw new Error('Soniox returned a token outside the merged recording.');
      } else source = map.ranges[lo][2];
    }
    if (source === null && token.text.trim()) throw new Error('Soniox did not return timestamps needed to divide the secondary transcript.');
    if (source !== null) groups[source].push(token);
    previous = source;
  }
  if (!tokens.length && result.text?.trim()) throw new Error('Soniox did not return timestamps needed to divide the secondary transcript.');
  const retained = new Set(map.ranges.map(([, , source]) => source));
  return [secondaryNames(map).transcript, ...map.sources.map((source, index) => {
    const text = renderSpeakers({tokens:groups[index]}, true);
    return `${source.date} ${source.time} — ${source.name}\n\n${text || (retained.has(index) ? '[No transcription returned.]' : '[No speech detected.]')}`;
  })].join('\n\n');
}
