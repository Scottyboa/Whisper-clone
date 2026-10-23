import test from 'node:test';
import assert from 'node:assert/strict';
import { wavBlob } from '../js/audio.mjs';
import { prepareAudio, clockLabel } from '../js/wav-timing.mjs';
import { vadDownloadFile } from '../js/vad-download.mjs';

const pcm = new Int16Array(32000).fill(4096);
const timing = {version:1,sampleRate:16000,timeZone:'Europe/Oslo',segments:[
  [0,16000,Date.parse('2026-10-23T10:00:00Z')],
  [16000,16000,Date.parse('2026-10-23T10:15:00Z')],
]};
const clean = () => new File([wavBlob([pcm])], 'original.wav', {type:'audio/wav'});

test('VAD download reattaches original clocks without restoring silence or changing PCM', async () => {
  const input = clean();
  const output = await vadDownloadFile({file:input,timing});
  assert.equal(output.name,'original-VAD.wav');assert.equal(output.type,'audio/wav');
  const prepared = await prepareAudio(output);
  assert.deepEqual(prepared.timing,timing);
  assert.deepEqual(new Uint8Array(await prepared.file.arrayBuffer()),new Uint8Array(await input.arrayBuffer()));
  assert.equal((prepared.file.size-44)/32000,2);
  assert.equal(clockLabel(prepared.timing,1000),'12:15:00');
  assert.equal(input.size,64044);
});

test('untimed VAD downloads stay ordinary WAV with no invented clock metadata', async () => {
  const input = clean();
  const output = await vadDownloadFile({file:input,timing:null});
  assert.equal((await prepareAudio(output)).timing,null);
  assert.deepEqual(new Uint8Array(await output.arrayBuffer()),new Uint8Array(await input.arrayBuffer()));
});

test('invalid clock maps and malformed generated WAVs fail instead of corrupting a download', async () => {
  await assert.rejects(vadDownloadFile({file:clean(),timing:{...timing,segments:[[0,1,1]]}}),/timestamps could not be saved/);
  await assert.rejects(vadDownloadFile({file:new File(['bad'],'bad.wav'),timing}),/WAV could not be read/);
});
