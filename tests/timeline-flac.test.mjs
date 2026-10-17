import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtemp, readFile, writeFile, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { spawnSync } from 'node:child_process';
import { encodeTimelineFlac, prepareTimelineFlac, makeFlacTimeline } from '../js/timeline-flac.mjs';
import { prepareAudio } from '../js/audio-import.mjs';
import { wavBlob } from '../js/audio.mjs';
import { renderTranscript, transcribeFile } from '../js/soniox.mjs';

const epoch = Date.parse('2026-10-17T12:00:00Z');
const pcm = Int16Array.from({ length: 32000 }, (_, i) => i % 3 ? Math.round(Math.sin(i * .1) * 20000) : -32768 + i % 65536);
const timing = { version: 1, sampleRate: 16000, timeZone: 'Europe/Oslo', segments: [[0, 16000, epoch + 500], [16000, 16000, epoch + 2500]] };
const entry = { startedAt: epoch, endedAt: epoch + 4000, elapsedMs: 4000, audioMs: 2000 };
const fixture = async () => {
  const compact = wavBlob([pcm], timing);
  const result = await encodeTimelineFlac({ blob: compact, entry, timing });
  return { ...result, file: new File([result.blob], 'recording.flac', { type: 'audio/flac' }), compact };
};

test('full-length FLAC reimport recovers the exact speech PCM, timezone and clock timestamps', async () => {
  const { file, map } = await fixture();
  assert.equal(map.totalSamples, 64000);
  assert.deepEqual(map.segments.map(s => s[3]), [8000, 40000]);
  const prepared = await prepareAudio(file);
  assert.equal(prepared.file.type, 'audio/wav'); assert.equal(prepared.file.name, 'recording.wav');
  assert.deepEqual(new Uint8Array(await prepared.file.arrayBuffer()), new Uint8Array(await wavBlob([pcm]).arrayBuffer()));
  assert.deepEqual(prepared.timing, timing);
  const text = renderTranscript({ tokens: [{ text: '日本語', speaker: 1, start_ms: 0 }, { text: 'Hello', speaker: 2, start_ms: 1000 }] }, true, prepared.timing);
  assert.equal(text, '(14:00:00) Speaker 1: 日本語\n\n(14:00:02) Speaker 2: Hello');
});

test('previous 4096-sample FLAC downloads still reimport with exact PCM and clocks', async () => {
  // Saved from the original encoder: three constant blocks, with only the
  // middle block retained. This fixture must not be rebuilt by the new encoder.
  const encoded = await readFile(new URL('./fixtures/timeline-flac-4096.base64', import.meta.url), 'utf8');
  const file = new File([Buffer.from(encoded.trim(), 'base64')], 'previous.flac');
  const prepared = await prepareAudio(file);
  assert.deepEqual(new Uint8Array(await prepared.file.arrayBuffer()),
    new Uint8Array(await wavBlob([new Int16Array(4096).fill(1234)]).arrayBuffer()));
  assert.deepEqual(prepared.timing, { version: 1, sampleRate: 16000, timeZone: 'UTC', segments: [[0, 4096, epoch + 256]] });
});

test('independent FFmpeg decoder verifies full duration, speech samples, silence and seeking', { skip: spawnSync('ffmpeg', ['-version']).status !== 0 }, async () => {
  const directory = await mkdtemp(join(tmpdir(), 'whisper-flac-'));
  try {
    const { file } = await fixture(), path = join(directory, 'test.flac');
    await writeFile(path, new Uint8Array(await file.arrayBuffer()));
    const decoded = spawnSync('ffmpeg', ['-v', 'error', '-i', path, '-f', 's16le', '-acodec', 'pcm_s16le', '-'], { maxBuffer: 1024 * 1024 });
    assert.equal(decoded.status, 0, decoded.stderr.toString());
    const expected = new Int16Array(64000); expected.set(pcm.subarray(0, 16000), 8000); expected.set(pcm.subarray(16000), 40000);
    assert.deepEqual(decoded.stdout, Buffer.from(expected.buffer));
    const sought = spawnSync('ffmpeg', ['-v', 'error', '-ss', '2.5', '-i', path, '-t', '0.1', '-f', 's16le', '-acodec', 'pcm_s16le', '-']);
    assert.equal(sought.status, 0, sought.stderr.toString());
    assert.deepEqual(sought.stdout, Buffer.from(pcm.slice(16000, 17600).buffer));
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('four-hour file stores silence compactly and uses bounded reads during export and reimport', async () => {
  const data = Int16Array.from({ length: 3200 }, (_, i) => i - 1600);
  const map = { ...timing, segments: [[0, 1600, epoch + 10000], [1600, 1600, epoch + 14300000]] };
  const longEntry = { ...entry, endedAt: epoch + 14400000, elapsedMs: 14400000, audioMs: 200 };
  const requests = [], original = wavBlob([data], map);
  const source = { size: original.size, slice(start, end) { requests.push(end - start); return original.slice(start, end); } };
  const { blob, map: restored } = await encodeTimelineFlac({ blob: source, entry: longEntry, timing: map });
  assert.equal(restored.totalSamples, 230400000); assert.ok(blob.size < 16 * 1024 * 1024, String(blob.size));
  const saved = new File([blob], 'four-hours.flac');
  const imported = { name: saved.name, size: saved.size, slice(start, end) { requests.push(end - start); return saved.slice(start, end); } };
  const prepared = await prepareTimelineFlac(imported);
  assert.equal(prepared.file.size, 6444); assert.deepEqual(prepared.timing, map);
  assert.deepEqual(new Uint8Array(await prepared.file.arrayBuffer()), new Uint8Array(await wavBlob([data]).arrayBuffer()));
  assert.ok(Math.max(...requests) <= 1024 * 1024);
});

test('fully silent recordings keep their duration and reimport avoids a pointless Soniox job', async () => {
  const emptyTiming = { ...timing, segments: [] };
  const { blob } = await encodeTimelineFlac({ blob: null, entry: { ...entry, audioMs: 0 }, timing: emptyTiming });
  assert.ok(blob.size < 5000);
  const prepared = await prepareAudio(new File([blob], 'silent.flac'));
  assert.equal(prepared.empty, true);
  await assert.rejects(transcribeFile(new File([blob], 'silent.flac'), 'fake-key', true), /no retained speech/);
});

async function changeMap(file, edit) {
  const bytes = new Uint8Array(await file.arrayBuffer());
  let offset = 4;
  while (offset < bytes.length) {
    const size = bytes[offset + 1] * 65536 + bytes[offset + 2] * 256 + bytes[offset + 3];
    if ((bytes[offset] & 127) === 4) {
      const head = offset + 4, view = new DataView(bytes.buffer), vendorLength = view.getUint32(head, true);
      const countOffset = head + 4 + vendorLength, textOffset = countOffset + 8;
      const text = new TextDecoder().decode(bytes.subarray(textOffset, offset + 4 + size));
      const prefix = 'WHISPER_CLONE_TIMING=', value = JSON.parse(text.slice(prefix.length));
      edit(value);
      const encoded = new TextEncoder().encode(prefix + JSON.stringify(value));
      const result = new Uint8Array(bytes.length - (offset + 4 + size - textOffset) + encoded.length);
      result.set(bytes.subarray(0, textOffset)); result.set(encoded, textOffset); result.set(bytes.subarray(offset + 4 + size), textOffset + encoded.length);
      new DataView(result.buffer).setUint32(countOffset + 4, encoded.length, true);
      const nextSize = 4 + vendorLength + 8 + encoded.length;
      result.set([nextSize >>> 16 & 255, nextSize >>> 8 & 255, nextSize & 255], offset + 1);
      return new File([result], file.name);
    }
    offset += size + 4;
  }
  throw new Error('No timing comment');
}

test('unknown versions and invalid timing never trim audio; ordinary files retain the existing path', async () => {
  const { file } = await fixture();
  const edits = [m => m.version++, m => m.totalSamples++, m => m.keptSamples++, m => m.timeZone = 'wrong/zone',
    m => m.segments[0][0]++, m => m.segments[1][3] = 0, m => m.endedAt += 1000, m => m.codec = 'another-codec',
    m => m.segments[0][2] += 10000];
  for (const edit of edits) {
    const altered = await changeMap(file, edit), prepared = await prepareAudio(altered);
    assert.equal(prepared.file, altered); assert.equal(prepared.timing, null);
  }
  for (const other of [new File(['fLaCbad'], 'ordinary.flac'), new File(['mp3'], 'file.mp3'), new File([wavBlob([pcm])], 'old.wav')]) {
    assert.equal((await prepareAudio(other)).file, other);
  }
});

test('CRC corruption, truncated frames and misleading metadata cannot silently discard speech', async () => {
  const { file } = await fixture(), source = new Uint8Array(await file.arrayBuffer());
  for (const index of [source.length - 1, source.length - 100]) {
    const bytes = source.slice(); bytes[index] ^= 1;
    const bad = new File([bytes], 'corrupt.flac'); assert.equal((await prepareAudio(bad)).file, bad);
  }
  const truncated = new File([file.slice(0, -1)], 'truncated.flac'); assert.equal((await prepareAudio(truncated)).file, truncated);
  const misleading = await changeMap(file, map => {
    map.segments[0][1] -= 100; map.segments[1][0] -= 100; map.keptSamples -= 100;
  });
  assert.equal((await prepareAudio(misleading)).file, misleading);
});

test('streaming export crosses midnight, keeps long pause gaps, and rejects clock reversal', () => {
  const midnight = Date.parse('2026-10-17T21:59:59Z');
  const map = makeFlacTimeline({ startedAt: midnight, endedAt: midnight + 3600000 },
    { ...timing, segments: [[0, 1, midnight], [1, 1, midnight + 3599000]] }, 2);
  assert.equal(map.totalSamples, 57600000); assert.equal(map.segments[1][3], 57584000);
  assert.throws(() => makeFlacTimeline(entry, { ...timing, segments: [[0, 16000, epoch], [16000, 16000, epoch + 100]] }, 32000), /clock/);
});

test('manual Soniox reimport uploads compact WAV under a WAV filename and returns original clocks', async () => {
  const { file } = await fixture(), fetcher = globalThis.fetch; let uploaded;
  globalThis.fetch = async (url, options = {}) => {
    let result = {};
    if (url.endsWith('/files') && options.method === 'POST') { uploaded = options.body.get('file'); result = { id: 'file' }; }
    else if (url.endsWith('/transcriptions') && options.method === 'POST') result = { id: 'job' };
    else if (url.endsWith('/transcript')) result = { tokens: [{ text: 'Test', speaker: 1, start_ms: 1000 }] };
    else if (options.method !== 'DELETE') result = { status: 'completed' };
    return new Response(JSON.stringify(result));
  };
  try {
    assert.equal(await transcribeFile(file, 'fake-key', true), '(14:00:02) Speaker 1: Test');
    assert.equal(uploaded.name, 'recording.wav'); assert.equal(uploaded.size, 64044);
  } finally { globalThis.fetch = fetcher; }
});
