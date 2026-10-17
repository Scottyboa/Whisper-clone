import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtemp, writeFile, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawn } from 'node:child_process';
import { encodeTimelineFlac } from '../js/timeline-flac.mjs';
import { wavBlob } from '../js/audio.mjs';

const library = process.env.WHISPER_TEST_LIBVLC;
const epoch = Date.parse('2026-10-17T12:00:00Z');

test('native VLC keeps playing after forward and backward seeks through speech and hours of silence',
  { skip: !library, timeout: 60000 }, async () => {
    const directory = await mkdtemp(join(tmpdir(), 'whisper-flac-vlc-'));
    try {
      const fixtures = [
        { name: 'speech-and-gaps', seconds: 1800, segments: [[10, 10], [800, 10], [1700, 10]] },
        { name: 'four-hour-gaps', seconds: 14400, segments: [[10, .1], [14300, .1]] },
      ];
      const paths = [];
      for (const fixture of fixtures) {
        let kept = 0;
        const segments = fixture.segments.map(([start, seconds]) => {
          const length = Math.round(seconds * 16000), segment = [kept, length, epoch + start * 1000];
          kept += length; return segment;
        });
        const pcm = Int16Array.from({ length: kept }, (_, i) => Math.sin(i * .04) * 12000);
        const timing = { version: 1, sampleRate: 16000, timeZone: 'UTC', segments };
        const { blob } = await encodeTimelineFlac({ blob: wavBlob([pcm]), timing,
          entry: { startedAt: epoch, endedAt: epoch + fixture.seconds * 1000, audioMs: kept / 16 } });
        const path = join(directory, fixture.name + '.flac'); paths.push(path);
        await writeFile(path, new Uint8Array(await blob.arrayBuffer()));
      }
      const result = await new Promise((resolve, reject) => {
        const child = spawn(process.env.WHISPER_TEST_PYTHON || 'python3',
          [fileURLToPath(new URL('./helpers/vlc-seek.py', import.meta.url)), library, ...paths]);
        let stdout = '', stderr = '';
        const timer = setTimeout(() => { child.kill(); reject(new Error('VLC seeking test timed out.')); }, 45000);
        child.stdout.on('data', bytes => { stdout += bytes; });
        child.stderr.on('data', bytes => { stderr += bytes; });
        child.on('error', error => { clearTimeout(timer); reject(error); });
        child.on('close', code => { clearTimeout(timer); resolve({ code, stdout, stderr }); });
      });
      assert.equal(result.code, 0, result.stdout + '\n' + result.stderr);
      assert.doesNotMatch(result.stderr, /INPUT_CONTROL_SET_POSITION.*failed/);
      const reports = result.stdout.trim().split('\n').map(line => JSON.parse(line));
      assert.equal(reports.length, 2);
      assert.deepEqual(reports.map(report => report.duration), [1800000, 14400000]);
    } finally { await rm(directory, { recursive: true, force: true }); }
  });
