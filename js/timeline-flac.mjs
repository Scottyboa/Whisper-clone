// RFC 9639, streamable subset: mono PCM16 at 16 kHz, fixed 4096-sample
// blocks, CONSTANT for silence and VERBATIM for other audio. Speech samples
// remain bit-identical. No full-duration PCM buffer or external codec is needed.
import { validateTiming, MAX_TIMING_BYTES } from './wav-timing.mjs?v=20261015-clock1';
import { wavBlob } from './audio.mjs?v=20261015-clock1';

const RATE = 16000, BLOCK = 4096, CHUNK = 1024 * 1024;
const TAG = 'WHISPER_CLONE_TIMING=', SCHEMA = 'whisper-clone.flac.v1';
const CODEC = 'pcm16-constant-verbatim-v1';
const utf8 = new TextEncoder();
const crcTable = (bits, poly) => Uint16Array.from({ length: 256 }, (_, i) => {
  let value = i << (bits - 8);
  for (let n = 0; n < 8; n++) value = (value << 1) ^ ((value & (1 << (bits - 1))) ? poly : 0);
  return value & ((1 << bits) - 1);
});
const C8 = crcTable(8, 0x07), C16 = crcTable(16, 0x8005);
function crc(bytes, bits) {
  let value = 0;
  const table = bits === 8 ? C8 : C16, mask = (1 << bits) - 1;
  for (const byte of bytes) value = ((value << 8) ^ table[((value >>> (bits - 8)) ^ byte) & 255]) & mask;
  return value;
}
const u24 = n => [n >>> 16 & 255, n >>> 8 & 255, n & 255];
const u32le = n => [n & 255, n >>> 8 & 255, n >>> 16 & 255, n >>> 24 & 255];
const metadata = (type, bytes, last = false) => new Blob([new Uint8Array([type | (last ? 128 : 0), ...u24(bytes.size ?? bytes.length)]), bytes]);
const yieldUI = () => new Promise(resolve => setTimeout(resolve, 0));

function codedNumber(n) {
  if (n < 128) return [n];
  let width = 2;
  while (n >= 2 ** (5 * width + 1)) width++;
  const result = new Array(width);
  for (let i = width - 1; i > 0; i--) { result[i] = 128 | (n & 63); n = Math.floor(n / 64); }
  result[0] = (256 - 2 ** (8 - width)) | n;
  return result;
}

function encodeFrame(samples, number) {
  const size = samples.length;
  const header = new Uint8Array([255, 248, 0x70, 0x08, ...codedNumber(number), (size - 1) >>> 8, (size - 1) & 255]);
  let constant = true;
  for (let i = 1; i < size; i++) if (samples[i] !== samples[0]) { constant = false; break; }
  const frame = new Uint8Array(header.length + 1 + 1 + (constant ? 2 : size * 2) + 2);
  frame.set(header); frame[header.length] = crc(header, 8);
  let offset = header.length + 1;
  frame[offset++] = constant ? 0 : 2;
  const data = new DataView(frame.buffer);
  if (constant) data.setInt16(offset, samples[0]);
  else for (let i = 0; i < size; i++) data.setInt16(offset + i * 2, samples[i]);
  const check = crc(frame.subarray(0, -2), 16);
  data.setUint16(frame.length - 2, check);
  return frame;
}

function zoneOK(zone) {
  try { new Intl.DateTimeFormat('en-GB', { timeZone: zone }).format(0); return typeof zone === 'string'; }
  catch { return false; }
}

export function makeFlacTimeline(entry, timing, keptSamples) {
  if (![entry?.startedAt, entry?.endedAt].every(Number.isFinite) || entry.startedAt <= 0 || entry.endedAt < entry.startedAt ||
      !Number.isSafeInteger(keptSamples) || keptSamples < 0 || !zoneOK(timing?.timeZone)) throw new Error('Recording timing is unavailable.');
  const valid = keptSamples ? validateTiming(timing, keptSamples) :
    timing?.version === 1 && timing.sampleRate === RATE && Array.isArray(timing.segments) && !timing.segments.length ? timing : null;
  if (!valid) throw new Error('Recording timing is incomplete.');
  let end = 0;
  const segments = valid.segments.map(([offset, length, epoch]) => {
    const position = Math.max(0, Math.round((epoch - entry.startedAt) * RATE / 1000));
    // Sub-millisecond capture-clock rounding can overlap adjacent pieces.
    if (position + 16 < end) throw new Error('Recording clock changed during capture.');
    const start = Math.max(position, end); end = start + length;
    return [offset, length, epoch, start];
  });
  // Preserve the acknowledged partial final frame, including its tiny padding.
  const totalSamples = Math.max(1, Math.round((entry.endedAt - entry.startedAt) * RATE / 1000), end);
  if (!Number.isSafeInteger(totalSamples) || totalSamples >= 2 ** 36) throw new Error('Recording exceeds the FLAC duration limit.');
  const map = { schema: SCHEMA, version: 1, codec: CODEC, sampleRate: RATE, channels: 1, bitsPerSample: 16,
    startedAt: entry.startedAt, endedAt: entry.startedAt + totalSamples / RATE * 1000, timeZone: timing.timeZone,
    totalSamples, keptSamples, segments };
  if (!validMap(map, totalSamples)) throw new Error('Recording timing cannot be restored safely.');
  return map;
}

function validMap(map, totalSamples) {
  if (map?.schema !== SCHEMA || map.version !== 1 || map.codec !== CODEC || map.sampleRate !== RATE ||
      map.channels !== 1 || map.bitsPerSample !== 16 || map.totalSamples !== totalSamples ||
      !Number.isSafeInteger(map.keptSamples) || map.keptSamples < 0 || map.keptSamples > totalSamples ||
      !Number.isFinite(map.startedAt) || map.startedAt <= 0 || !Number.isFinite(map.endedAt) ||
      Math.abs(map.endedAt - map.startedAt - totalSamples / 16) > 1 || !zoneOK(map.timeZone) ||
      !Array.isArray(map.segments) || map.segments.length > 50000) return false;
  let kept = 0, end = 0;
  for (const segment of map.segments) {
    if (!Array.isArray(segment) || segment.length !== 4) return false;
    const [offset, length, epoch, start] = segment;
    if (offset !== kept || !Number.isSafeInteger(length) || length <= 0 || !Number.isFinite(epoch) || epoch <= 0 ||
        !Number.isSafeInteger(start) || start < end || start + length > totalSamples ||
        Math.abs((epoch - map.startedAt) * 16 - start) > 32) return false;
    kept += length; end = start + length;
  }
  return kept === map.keptSamples && (!kept || !!validateTiming({ ...map, segments: map.segments.map(s => s.slice(0, 3)) }, kept));
}

// Bounded Blob reads work in both a module Worker and the test/runtime fallback.
class Reader {
  constructor(blob, offset = 0) { this.blob = blob; this.position = offset; this.buffer = new Uint8Array(); this.index = 0; }
  async read(size) {
    if (!Number.isSafeInteger(size) || size < 0 || this.position + size > this.blob.size) throw new Error('Truncated audio.');
    if (this.buffer.length - this.index < size) {
      this.buffer = new Uint8Array(await this.blob.slice(this.position, Math.min(this.blob.size, this.position + Math.max(CHUNK, size))).arrayBuffer());
      this.index = 0;
    }
    const bytes = this.buffer.subarray(this.index, this.index + size);
    this.index += size; this.position += size; return bytes;
  }
}

export async function encodeTimelineFlac({ blob, entry, timing }, progress = () => {}) {
  const keptSamples = Math.round(entry.audioMs * 16);
  const map = makeFlacTimeline(entry, timing, keptSamples);
  if (keptSamples && (!blob || blob.size < 44 + keptSamples * 2)) throw new Error('Recording audio is incomplete.');
  const json = utf8.encode(TAG + JSON.stringify(map));
  if (json.length > MAX_TIMING_BYTES) throw new Error('Recording timing exceeds the metadata limit.');
  const reader = new Reader(blob || new Blob(), keptSamples ? 44 : 0);
  const frames = [], seeks = []; let output = [], bytes = 0, groupBytes = 0, sourceSegment = 0, copied = 0;
  const samples = new Int16Array(BLOCK);
  const frameCount = Math.ceil(map.totalSamples / BLOCK);
  for (let frame = 0; frame < frameCount; frame++) {
    const start = frame * BLOCK, length = Math.min(BLOCK, map.totalSamples - start);
    samples.fill(0); let cursor = start;
    while (sourceSegment < map.segments.length) {
      const segment = map.segments[sourceSegment], end = segment[3] + segment[1];
      if (end <= cursor) { sourceSegment++; continue; }
      if (segment[3] >= start + length) break;
      cursor = Math.max(cursor, segment[3]);
      const count = Math.min(end, start + length) - cursor;
      const raw = await reader.read(count * 2), view = new DataView(raw.buffer, raw.byteOffset, raw.byteLength);
      for (let i = 0; i < count; i++) samples[cursor - start + i] = view.getInt16(i * 2, true);
      copied += count; cursor += count;
      if (cursor === end) sourceSegment++;
      if (cursor === start + length) break;
    }
    const encoded = encodeFrame(samples.subarray(0, length), frame);
    if (frame % 40 === 0) seeks.push([start, bytes, length]);
    output.push(encoded); bytes += encoded.length; groupBytes += encoded.length;
    if (groupBytes >= CHUNK) { frames.push(new Blob(output)); output = []; groupBytes = 0; }
    if (frame % 256 === 0) { progress(frame / frameCount); await yieldUI(); }
  }
  if (copied !== keptSamples) throw new Error('Recording sample count changed.');
  if (output.length) frames.push(new Blob(output));
  const info = new Uint8Array(34), view = new DataView(info.buffer);
  view.setUint16(0, BLOCK); view.setUint16(2, BLOCK);
  view.setBigUint64(10, BigInt(RATE) << 44n | 15n << 36n | BigInt(map.totalSamples));
  // An all-zero MD5 means "not supplied" in STREAMINFO (RFC 9639).
  const vendor = utf8.encode('Whisper-clone timeline FLAC v1');
  const comments = new Blob([new Uint8Array(u32le(vendor.length)), vendor, new Uint8Array([...u32le(1), ...u32le(json.length)]), json]);
  const seek = new Uint8Array(seeks.length * 18), seekView = new DataView(seek.buffer);
  seeks.forEach(([sample, offset, count], i) => {
    seekView.setBigUint64(i * 18, BigInt(sample)); seekView.setBigUint64(i * 18 + 8, BigInt(offset)); seekView.setUint16(i * 18 + 16, count);
  });
  progress(1);
  return { blob: new Blob([utf8.encode('fLaC'), metadata(0, info), metadata(3, seek), metadata(4, comments, true), ...frames], { type: 'audio/flac' }), map };
}

async function readMetadata(file) {
  if (file.size < 42 || new TextDecoder().decode(await file.slice(0, 4).arrayBuffer()) !== 'fLaC') return null;
  let offset = 4, info, map = null, tags = 0, last = false, blocks = 0;
  while (!last && offset + 4 <= file.size && ++blocks <= 4096) {
    const head = new Uint8Array(await file.slice(offset, offset + 4).arrayBuffer());
    const type = head[0] & 127, size = head[1] * 65536 + head[2] * 256 + head[3];
    last = !!(head[0] & 128); offset += 4;
    if (offset + size > file.size || (blocks === 1 && (type !== 0 || size !== 34))) return null;
    if (type === 0) {
      if (info || size !== 34) return null;
      const view = new DataView(await file.slice(offset, offset + size).arrayBuffer());
      const value = view.getBigUint64(10);
      info = { sampleRate: Number(value >> 44n), channels: Number(value >> 41n & 7n) + 1,
        bits: Number(value >> 36n & 31n) + 1, samples: Number(value & ((1n << 36n) - 1n)) };
    } else if (type === 4 && size <= MAX_TIMING_BYTES + 4096) {
      const data = new Uint8Array(await file.slice(offset, offset + size).arrayBuffer()), view = new DataView(data.buffer);
      if (data.length < 8) return null;
      let at = view.getUint32(0, true) + 4;
      if (at + 4 > size) return null;
      const count = view.getUint32(at, true); at += 4;
      if (count > 65536) return null;
      for (let i = 0; i < count; i++) {
        if (at + 4 > size) return null;
        const length = view.getUint32(at, true); at += 4;
        if (at + length > size) return null;
        const comment = new TextDecoder('utf-8', { fatal: true }).decode(data.subarray(at, at + length)); at += length;
        if (comment.startsWith(TAG)) { tags++; map = JSON.parse(comment.slice(TAG.length)); }
      }
      if (at !== size) return null;
    }
    offset += size;
  }
  if (!last || tags !== 1 || info?.sampleRate !== RATE || info.channels !== 1 || info.bits !== 16 ||
      !info.samples || !validMap(map, info.samples)) return null;
  return { map, offset };
}

// Only decode the deliberately small codec subset emitted above. Re-encoded,
// ordinary, malformed or unknown-version FLACs keep the existing upload path.
export async function prepareTimelineFlac(file, progress = () => {}) {
  const original = { file, timing: null };
  try {
    const metadata = await readMetadata(file);
    if (!metadata) return original;
    const { map } = metadata, reader = new Reader(file, metadata.offset);
    let sample = 0, number = 0, segment = 0, kept = 0, groupSamples = 0, group = [], output = [];
    while (sample < map.totalSamples) {
      const prefix = await reader.read(4), header = [...prefix];
      if (prefix[0] !== 255 || prefix[1] !== 248 || prefix[2] !== 0x70 || prefix[3] !== 8) return original;
      const first = (await reader.read(1))[0]; header.push(first);
      let frameNumber = first, width = 1;
      if (first >= 128) {
        width = 0; for (let mask = 128; first & mask; mask >>= 1) width++;
        if (width < 2 || width > 6) return original;
        frameNumber = first & (127 >> width);
        const rest = await reader.read(width - 1);
        for (const byte of rest) { if ((byte & 192) !== 128) return original; header.push(byte); frameNumber = frameNumber * 64 + (byte & 63); }
      }
      if (frameNumber !== number++ || codedNumber(frameNumber).length !== width) return original;
      const block = await reader.read(2); header.push(...block);
      const length = block[0] * 256 + block[1] + 1;
      const headerCRC = (await reader.read(1))[0];
      if (length !== Math.min(BLOCK, map.totalSamples - sample) || crc(header, 8) !== headerCRC) return original;
      const sub = (await reader.read(1))[0];
      if (sub !== 0 && sub !== 2) return original;
      const bytes = await reader.read(sub ? length * 2 : 2), data = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
      const frame = new Uint8Array(header.length + 2 + bytes.length);
      frame.set(header); frame[header.length] = headerCRC; frame[header.length + 1] = sub; frame.set(bytes, header.length + 2);
      const footer = await reader.read(2);
      if (crc(frame, 16) !== footer[0] * 256 + footer[1]) return original;
      // Entire silent blocks outside retained segments need no sample-by-sample
      // decoding. This is why reimporting a long timeline needs no second VAD.
      while (segment < map.segments.length && sample >= map.segments[segment][3] + map.segments[segment][1]) segment++;
      const nextSegment = map.segments[segment];
      if (sub === 0 && data.getInt16(0) === 0 && (!nextSegment || nextSegment[3] >= sample + length)) {
        sample += length;
        if (number % 256 === 0) { progress(sample / map.totalSamples); await yieldUI(); }
        continue;
      }
      const retained = new Int16Array(length); let count = 0;
      for (let i = 0; i < length; i++) {
        const position = sample + i;
        while (segment < map.segments.length && position >= map.segments[segment][3] + map.segments[segment][1]) segment++;
        const current = map.segments[segment], value = data.getInt16(sub ? i * 2 : 0);
        if (current && position >= current[3]) retained[count++] = value;
        else if (value !== 0) return original; // Never discard audio based solely on a metadata claim.
      }
      if (count) { group.push(retained.slice(0, count)); groupSamples += count; kept += count; }
      if (groupSamples >= CHUNK / 2) { output.push(wavBlob(group).slice(44)); group = []; groupSamples = 0; }
      sample += length;
      if (number % 256 === 0) { progress(sample / map.totalSamples); await yieldUI(); }
    }
    if (reader.position !== file.size || kept !== map.keptSamples) return original;
    if (!kept) return { file: null, timing: null, empty: true };
    if (group.length) output.push(wavBlob(group).slice(44));
    // Reuse the established WAV encoder for its small header without copying all PCM.
    const audioBytes = kept * 2;
    if (audioBytes > 0xffffffff - 36) return original;
    const header = new Uint8Array(await wavBlob([]).arrayBuffer()), view = new DataView(header.buffer);
    view.setUint32(4, 36 + audioBytes, true); view.setUint32(40, audioBytes, true);
    const name = (file.name || 'recording.flac').replace(/\.[^.]*$/, '') + '.wav';
    const timing = { version: 1, sampleRate: RATE, timeZone: map.timeZone, segments: map.segments.map(s => s.slice(0, 3)) };
    progress(1);
    return { file: new File([header, ...output], name, { type: 'audio/wav' }), timing };
  } catch { return original; }
}
