import test from 'node:test';
import assert from 'node:assert/strict';
import { hasInputSound, inputActivityInfo, inputActivityLabel } from '../js/input-activity.mjs';
import { Recorder } from '../js/recorder.mjs';

const epoch = new Date(2026, 9, 21, 16, 3, 12).getTime();
const sound = new Float32Array(1536).fill(0.02);
const silence = new Float32Array(1536);
const activity = lastSoundAt => ({ inputActivityVersion: 1, lastSoundAt });

test('input sound detection rejects silence, faint input and invalid samples without altering audio', () => {
  for (const frame of [silence, new Float32Array(1536).fill(0.0001), [], [NaN], [Infinity]])
    assert.equal(hasInputSound(frame), false);
  const frame = Float32Array.from({ length: 1536 }, (_, i) => i % 2 ? 0.02 : -0.02);
  const copy = frame.slice();
  assert.equal(hasInputSound(frame), true);
  assert.deepEqual(frame, copy);
});

test('sound labels distinguish missing support, no sound yet, local clock time and older dates', () => {
  assert.equal(inputActivityLabel({}, epoch), 'Sound activity unavailable');
  assert.equal(inputActivityLabel(activity(null), epoch), 'No sound detected yet');
  assert.equal(inputActivityLabel(activity(epoch), epoch + 5000), '16:03:12 · 5s ago');
  assert.equal(inputActivityLabel(activity(epoch), epoch + 120000), '16:03:12 · 2m ago');
  assert.equal(inputActivityLabel(activity(epoch), epoch + 3720000), '16:03:12 · 1h 2m ago');
  assert.equal(inputActivityLabel(activity(epoch), epoch + 86400000), '2026-10-21 16:03:12 · 24h 0m ago');
  assert.equal(inputActivityLabel(activity(epoch + 1000), epoch), '16:03:13 · 0s ago');
});

test('unsupported or malformed device activity never appears as silence', () => {
  for (const value of [{}, { inputActivityVersion: 1 }, { ...activity(null), inputActivityVersion: 2 },
    activity('16:03'), activity(0), activity(-1), activity(Infinity), activity(epoch + 10000)]) {
    assert.deepEqual(inputActivityInfo(value, epoch), {});
    assert.equal(inputActivityLabel(value, epoch), 'Sound activity unavailable');
  }
  assert.deepEqual(inputActivityInfo({ ...activity(epoch), samples: sound, level: 0.02 }, epoch), activity(epoch));
});

test('recording observes input before speech is accepted, preserves pause/resume, and resets on a fresh start', async () => {
  let now = epoch;
  const captures = [], recorder = new Recorder({ now: () => now, createVAD: async options => {
    captures.push(options);
    return { drainAndPause: async () => {}, destroy() {}, stream: { getTracks: () => [] } };
  } });
  await recorder.command('start');
  assert.equal(recorder.lastSoundAt, null);
  captures[0].onInputFrame(silence);
  assert.equal(recorder.lastSoundAt, null);
  now += 1000; captures[0].onInputFrame(sound);
  assert.equal(recorder.lastSoundAt, now);
  assert.equal(recorder.samples, 0, 'no VAD speech callback is needed');
  const first = now;
  now += 60000; captures[0].onInputFrame(silence);
  await recorder.command('pause'); captures[0].onInputFrame(sound);
  assert.equal(recorder.lastSoundAt, first);
  await recorder.command('resume');
  captures[0].onInputFrame(sound); captures[1].onInputFrame(silence);
  assert.equal(recorder.lastSoundAt, first, 'old capture callbacks cannot update the resumed capture');
  captures[1].onInputFrame(sound);
  assert.equal(recorder.lastSoundAt, now);
  const last = now;
  now += 1000;
  const finished = await recorder.command('stop');
  captures[1].onInputFrame(sound);
  assert.equal(recorder.lastSoundAt, last);
  assert.equal(finished.blob, null, 'the monitor does not add audio to the VAD output');
  await recorder.command('start');
  assert.equal(recorder.lastSoundAt, null);
  captures[1].onInputFrame(sound);
  assert.equal(recorder.lastSoundAt, null);
  captures[2].onInputFrame(sound);
  const beforeAbort = recorder.lastSoundAt;
  await recorder.command('abort'); now += 1000; captures[2].onInputFrame(sound);
  assert.equal(recorder.lastSoundAt, beforeAbort);
  await recorder.command('start');
  assert.equal(recorder.lastSoundAt, null);
  recorder.dispose(); captures[3].onInputFrame(sound);
  assert.equal(recorder.lastSoundAt, null);
});
