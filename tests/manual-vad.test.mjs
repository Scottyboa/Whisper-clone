import test from 'node:test';
import assert from 'node:assert/strict';
import vm from 'node:vm';
import { readFileSync } from 'node:fs';
import { decodeFileChunks } from '../js/file-audio.mjs';
import { vadFrames, trimDecodedAudio, retainedTiming } from '../js/file-vad.mjs';
import { prepareManualAudio, cancelManualVAD } from '../js/manual-vad.mjs';
import { transcribeFile } from '../js/soniox.mjs';
import { wavBlob, VAD_RULES } from '../js/audio.mjs';

const sandbox = { self: { ort: {} }, console };
vm.runInNewContext(readFileSync(new URL('../vendor/vad/bundle.min.js', import.meta.url), 'utf8'), sandbox);
const processor = () => {
  const result = new sandbox.self.vad.FrameProcessor(async frame => ({ isSpeech: frame.some(value => Math.abs(value) > .01) ? 1 : 0 }), () => {}, VAD_RULES);
  result.resume(); return result;
};
const wav = (pcm, timing) => new File([wavBlob([pcm], timing)], 'input.wav', { type: 'audio/wav' });
const frame = VAD_RULES.frameSamples;
const epoch = Date.parse('2026-10-23T10:00:00Z');
const flac = () => new File([Buffer.from(readFileSync(new URL('./fixtures/timeline-flac-4096.base64', import.meta.url), 'utf8').trim(), 'base64')], 'old.flac');
const trim = prepared => trimDecodedAudio(prepared, decodeFileChunks(prepared.file), processor());

test('fresh VAD removes long silent sections and keeps pre-padding, tail and the last partial speech frame', async () => {
  const pcm = new Int16Array(frame * 16 + 123);
  pcm.fill(10000, frame * 3, frame * 7); pcm.fill(15000, frame * 13);
  const timing = { version: 1, sampleRate: 16000, timeZone: 'Europe/Oslo', segments: [[0, pcm.length, epoch]] };
  const result = await trim({ file: wav(pcm), timing });
  assert.equal(result.file.type, 'audio/wav');
  assert.equal(result.file.size, 44 + (frame * 15 + 123) * 2);
  assert.deepEqual(result.timing.segments, [[0, frame * 11, epoch + 96], [frame * 11, frame * 4 + 123, epoch + 1152]]);
  const view = new DataView(await result.file.arrayBuffer());
  assert.ok(view.getInt16(result.file.size - 2, true) > 14000, 'the final real sample survives without padded samples');
});

test('silent and too-short noise-only recordings produce no uploadable file', async () => {
  for (const pcm of [new Int16Array(frame * 10), new Int16Array(frame).fill(10000)]) {
    const result = await trim({ file: wav(pcm), timing: null });
    assert.equal(result.empty, true); assert.equal(result.file, null);
  }
});

test('fractional resampling and stereo mixing are independent of decoder chunk boundaries', async () => {
  const left = new Float32Array(44101).fill(.6), right = new Float32Array(44101).fill(.2);
  async function* chunks(size) { for (let at = 0; at < left.length; at += size)
    yield { sampleRate: 44100, channelData: [left.subarray(at, at + size), right.subarray(at, at + size)], progress: Math.min(1, (at + size) / left.length) }; }
  const collect = async size => { const parts = []; for await (const item of vadFrames(chunks(size))) parts.push(...item.frame.subarray(0, item.valid)); return parts; };
  const a = await collect(left.length), b = await collect(1027);
  assert.equal(a.length, Math.ceil(44101 * 16000 / 44100)); assert.deepEqual(a, b);
  assert.ok(a.every(value => Math.abs(value - .4) < 1e-6));
});

test('new speech cuts compose through the original timestamp gaps and timezone', () => {
  const timing = { version: 1, sampleRate: 16000, timeZone: 'Europe/Oslo', segments: [[0, 16000, epoch], [16000, 16000, epoch + 3600000]] };
  assert.deepEqual(retainedTiming(timing, [[8000, 16000], [30000, 2000]], 18000), {
    ...timing, segments: [[0, 8000, epoch + 500], [8000, 8000, epoch + 3600000], [16000, 2000, epoch + 3600875]],
  });
  assert.equal(retainedTiming(null, [[0, 10]], 10), null);
  assert.throws(() => retainedTiming(timing, [[31999, 100]], 100), /timestamps could not be preserved/);
});

test('app FLACs and old timed WAVs also receive a fresh VAD pass after metadata extraction', async () => {
  const inputs = [flac(), wav(new Int16Array(frame * 4).fill(10000), {
    version: 1, sampleRate: 16000, timeZone: 'UTC', segments: [[0, frame * 4, epoch]],
  })];
  for (const file of inputs) {
    let runs = 0;
    const result = await prepareManualAudio(file, () => {}, async (prepared, progress) => {
      runs++; assert.equal(prepared.file.type, 'audio/wav'); assert.ok(prepared.timing);
      return trimDecodedAudio(prepared, decodeFileChunks(prepared.file), processor(), progress);
    });
    assert.equal(runs, 1); assert.ok(result.file); assert.ok(result.timing);
    assert.equal(result.timing.timeZone, 'UTC');
  }
});

test('PCM WAV input is read in bounded chunks and supports stereo 24-bit and floating point', async () => {
  const source = wav(new Int16Array(500000).fill(10000)), reads = [];
  const file = { name: source.name, size: source.size, slice(start, end) { reads.push(end - start); return source.slice(start, end); }, arrayBuffer() { assert.fail('Full WAV allocation'); } };
  let count = 0;
  for await (const chunk of decodeFileChunks(file)) { count += chunk.channelData[0].length; assert.equal(chunk.sampleRate, 16000); }
  assert.equal(count, 500000); assert.ok(Math.max(...reads) <= 262144);
  for (const [encoding, bits] of [[1, 24], [3, 32]]) {
    const bytes = new Uint8Array(44 + 8 * 2 * bits / 8), view = new DataView(bytes.buffer);
    bytes.set(new TextEncoder().encode('RIFF')); view.setUint32(4, bytes.length - 8, true);
    bytes.set(new TextEncoder().encode('WAVEfmt '), 8); view.setUint32(16, 16, true); view.setUint16(20, encoding, true);
    view.setUint16(22, 2, true); view.setUint32(24, 48000, true); view.setUint32(28, 48000 * 2 * bits / 8, true);
    view.setUint16(32, 2 * bits / 8, true); view.setUint16(34, bits, true); bytes.set(new TextEncoder().encode('data'), 36); view.setUint32(40, bytes.length - 44, true);
    for (let at = 44; at < bytes.length; at += bits / 8) {
      if (encoding === 3) view.setFloat32(at, -.25, true);
      else { bytes[at] = 0; bytes[at + 1] = 0; bytes[at + 2] = 0xe0; }
    }
    for await (const chunk of decodeFileChunks(new File([bytes], 'stereo.wav'))) {
      assert.equal(chunk.channelData.length, 2); assert.equal(chunk.sampleRate, 48000);
      assert.ok(chunk.channelData.every(ch => ch.every(value => value === -.25)));
    }
  }
});

test('bundled libFLAC decodes a whole ordinary FLAC in chunks and rejects truncation', async () => {
  const originalWorker = globalThis.Worker; globalThis.Worker = class {};
  let FLACDecoder;
  try { ({ FLACDecoder } = await import('../vendor/flac/flac-decoder.min.mjs')); }
  finally { globalThis.Worker = originalWorker; }
  const factory = async () => { const decoder = new FLACDecoder(); await decoder.ready; return decoder; };
  const file = new File([Buffer.from(readFileSync(new URL('./fixtures/ordinary-flac.base64', import.meta.url), 'utf8').trim(), 'base64')], 'ordinary.flac'); let count = 0;
  for await (const chunk of decodeFileChunks(file, { flacDecoder: factory })) { count += chunk.channelData[0].length; assert.equal(chunk.sampleRate, 16000); }
  assert.equal(count, 12288, 'ordinary decoding retains the full timeline before VAD');
  await assert.rejects(async () => { for await (const chunk of decodeFileChunks(new File([file.slice(0, -5)], 'bad.flac'), { flacDecoder: factory })) void chunk; }, /incomplete|decoding failed/);
});

test('Soniox receives only the new VAD output; silence and processing failures make zero provider requests', async () => {
  const originalFetch = globalThis.fetch, originalWorker = globalThis.Worker;
  const uploads = []; let fail = false;
  globalThis.Worker = class {
    terminate() {}
    postMessage({ prepared }) {
      Promise.resolve().then(async () => {
        try { if (fail) throw new Error('Model failed'); this.onmessage({ data: { result: await trim(prepared) } }); }
        catch (error) { this.onmessage({ data: { error: error.message } }); }
      });
    }
  };
  globalThis.fetch = async (url, options = {}) => {
    let result = {};
    if (url.endsWith('/files') && options.method === 'POST') { uploads.push(options.body.get('file')); result = { id: 'file' }; }
    else if (url.endsWith('/transcriptions') && options.method === 'POST') result = { id: 'job' };
    else if (url.endsWith('/transcript')) result = { tokens: [{ text: 'Hello', speaker: 1, start_ms: 192 }] };
    else if (options.method !== 'DELETE') result = { status: 'completed' };
    return new Response(JSON.stringify(result));
  };
  try {
    const pcm = new Int16Array(frame * 30); pcm.fill(10000, frame * 10, frame * 15);
    const file = wav(pcm, { version: 1, sampleRate: 16000, timeZone: 'UTC', segments: [[0, pcm.length, epoch]] });
    assert.equal(await transcribeFile(file, 'test', true, () => {}, { manualVAD: true }), '(10:00:00) Speaker 1: Hello');
    assert.equal(uploads.length, 1); assert.equal(uploads[0].name, 'input.wav'); assert.ok(uploads[0].size < file.size / 2);
    await assert.rejects(transcribeFile(wav(new Int16Array(frame * 10)), 'test', true, () => {}, { manualVAD: true }), /No speech detected/);
    fail = true;
    await assert.rejects(transcribeFile(file, 'test', true, () => {}, { manualVAD: true }), /Model failed/);
    assert.equal(uploads.length, 1);
  } finally { globalThis.fetch = originalFetch; globalThis.Worker = originalWorker; }
});

test('leaving the page cancels a pending manual VAD worker', async () => {
  const original = globalThis.Worker; let terminate = 0, started;
  const ready = new Promise(resolve => { started = resolve; });
  globalThis.Worker = class { postMessage() { started(); } terminate() { terminate++; } };
  try {
    const pending = prepareManualAudio(wav(new Int16Array(frame * 5)));
    await ready; cancelManualVAD(); await assert.rejects(pending, /cancelled/); assert.equal(terminate, 1);
  } finally { globalThis.Worker = original; }
});
