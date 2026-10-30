import test from 'node:test';
import assert from 'node:assert/strict';
import { createServer } from 'node:http';
import { spawn } from 'node:child_process';
import { readFile, mkdtemp, rm, readdir } from 'node:fs/promises';
import { fileURLToPath } from 'node:url';
import { join, resolve, extname } from 'node:path';
import { tmpdir } from 'node:os';
import { protocol } from './helpers/browser.mjs';

const executable = process.env.WHISPER_TEST_CHROME;
const root = fileURLToPath(new URL('../', import.meta.url));
const delay = ms => new Promise(resolve => setTimeout(resolve, ms));

// Private CDP pipes drive only this disposable test browser and local fixture.

test('Chrome downloads playable VAD WAV with original clocks and restarts independently', { skip: !executable, timeout: 60000 }, async () => {
  const directory = await mkdtemp(join(tmpdir(), 'whisper-flac-browser-'));
  const downloads = join(directory, 'downloads');
  const { mkdir } = await import('node:fs/promises'); await mkdir(downloads);
  const fixtures = {
    // This test isolates the recording download and clock import path. The separate
    // manual-VAD browser test runs the real speech model and decoder worker.
    '/js/manual-vad.mjs': `import {prepareAudio} from './audio-import.mjs';export async function prepareManualAudio(file){window.testManualVAD=true;return prepareAudio(file)}export function cancelManualVAD(){}export function createManualVADSession(){throw new Error('Not used in this fixture')}`,
    '/js/recorder.mjs': `import {Recorder as Base} from './test-real-recorder.mjs';export class Recorder extends Base {
      constructor(options){super({...options,now:()=>window.testNow,createVAD:async callbacks=>({async drainAndPause(){callbacks.onSpeechEnd(new Float32Array(16000).fill(.25),[[0,16000,window.testNow-2000]])},destroy(){}})});window.testRecorder=this;}}`,
    '/js/graph.mjs': `export class MailControl {constructor(options){Object.assign(this,options);window.testCommand=options.onCommand;this.active=false}async client(){return {}}unlink(){}}`,
    '/js/device-control.mjs': `export const RECENT_MS=30000,PRESENCE_TTL=120000;export class DeviceControl {constructor(options){Object.assign(this,options);this.active=false;this.rows=[];this.pending=new Map()}async connect(){}disconnect(){}}`,
    '/js/transcript-drive.mjs': `export class TranscriptDrive {async upload(text,options){window.testUploads.push({text,name:options.name,folders:options.folders});return options.name}}`,
  };
  const server = createServer(async (request, response) => {
    try {
      const pathname = new URL(request.url, 'http://localhost').pathname;
      let body;
      if (pathname === '/saved.wav') {
        const name = (await readdir(downloads)).find(name => name.endsWith('.wav'));
        body = await readFile(join(downloads, name));
      } else if (fixtures[pathname]) body = fixtures[pathname];
      else if (pathname === '/js/test-real-recorder.mjs') body = await readFile(join(root, 'js/recorder.mjs'));
      else if (pathname === '/') {
        let html = await readFile(join(root, 'index.html'), 'utf8');
        const setup = `<script>
          window.testNow=Date.parse('2026-10-17T12:00:00Z');window.testUploads=[];window.testPayloads=[];window.testAudioFiles=[];window.testDownloads=[];
          const nativeURL=URL.createObjectURL.bind(URL);URL.createObjectURL=blob=>{window.testDownloads.push(blob);return nativeURL(blob)};
          sessionStorage.setItem('whisper-clone.soniox-key','fixture-only');
          const nativeFetch=window.fetch.bind(window);
          window.fetch=async(url,options={})=>{
            if(!String(url).includes('soniox.com'))return nativeFetch(url,options);
            let result={};
            if(String(url).endsWith('/files')&&options.method==='POST'){
              const file=options.body.get('file');window.testAudioFiles.push(file);window.testPayloads.push({name:file.name,type:file.type,size:file.size});result={id:'fixture-file'};
            }else if(String(url).endsWith('/transcriptions')&&options.method==='POST')result={id:'fixture-job'};
            else if(String(url).endsWith('/transcript'))result={tokens:[{text:'日本語 Test',speaker:1,start_ms:0}]};
            else if(options.method!=='DELETE')result={status:'completed'};
            return new Response(JSON.stringify(result));
          };
        </script>`;
        body = html.replace('<head>', '<head>' + setup);
      } else {
        const path = resolve(root, '.' + pathname);
        if (!path.startsWith(root)) throw new Error('Invalid fixture path');
        body = await readFile(path);
      }
      const mime = pathname === '/' ? 'text/html' : /\.(mjs|js)$/.test(pathname) ? 'text/javascript' : extname(pathname) === '.css' ? 'text/css' : 'application/octet-stream';
      response.writeHead(200, { 'Content-Type': mime, 'Cache-Control': 'no-store' }); response.end(body);
    } catch { response.writeHead(404); response.end(); }
  });
  await new Promise(resolve => server.listen(0, '127.0.0.1', resolve));
  const browser = spawn(executable, ['--no-sandbox', '--headless', '--disable-gpu', '--no-first-run', '--no-default-browser-check', '--remote-debugging-pipe', `--user-data-dir=${join(directory, 'profile')}`], { stdio: ['ignore', 'ignore', 'ignore', 'pipe', 'pipe'] });
  const cdp = protocol(browser);
  try {
    await cdp('Browser.setDownloadBehavior', { behavior: 'allow', downloadPath: downloads });
    const { targetId } = await cdp('Target.createTarget', { url: `http://127.0.0.1:${server.address().port}/` });
    const { sessionId } = await cdp('Target.attachToTarget', { targetId, flatten: true });
    await cdp('Emulation.setTimezoneOverride', { timezoneId: 'Europe/Oslo' }, sessionId);
    const evaluate = async expression => {
      const result = await cdp('Runtime.evaluate', { expression, awaitPromise: true, returnByValue: true }, sessionId);
      if (result.exceptionDetails) throw new Error(JSON.stringify(result.exceptionDetails));
      return result.result.value;
    };
    for (let i = 0; i < 100 && !await evaluate("typeof window.testCommand==='function'"); i++) await delay(50);
    assert.equal(await evaluate("typeof window.testCommand==='function'"), true);
    assert.equal(await evaluate("document.getElementById('audioEnhancement').checked"),true);
    // Real recorder finalization and download; provider and microphone are fixtures.
    await evaluate("window.testCommand('start')");
    await evaluate("window.testNow+=10000;window.testCommand('stop-and-transcribe')");
    assert.equal(await evaluate('window.testRecorder.state'), 'recording');
    for (let i = 0; i < 100 && !(await readdir(downloads)).some(name => name.endsWith('.wav')); i++) await delay(50);
    assert.ok((await readdir(downloads)).some(name => name.endsWith('.wav')),
      await evaluate("document.getElementById('audioDownloadStatus').textContent"));
    for (let i = 0; i < 100 && !await evaluate('window.testUploads.length'); i++) await delay(50);
    assert.equal(await evaluate('window.testUploads.length'), 1);
    assert.deepEqual(await evaluate('window.testUploads[0].folders'), ['Transcripts','temp']);
    assert.equal(await evaluate('window.testPayloads[0].size'), 32044);
    const playback = await evaluate(`(async()=>{const blob=await(await fetch('/saved.wav')).arrayBuffer();
      const context=new AudioContext({sampleRate:16000});try{const decoded=await context.decodeAudioData(blob);
      const pcm=decoded.getChannelData(0);return {duration:decoded.duration,channels:decoded.numberOfChannels,leading:pcm[0],speech:pcm[8000],trailing:pcm[15900]};}finally{await context.close();}})()`);
    assert.equal(playback.duration, 1); assert.equal(playback.channels, 1);
    assert.ok(playback.leading > .2); assert.ok(Math.abs(playback.speech)<.001); assert.ok(Math.abs(playback.trailing)<.001);
    assert.equal(await evaluate(`(async()=>{const {prepareAudio}=await import('./js/audio-import.mjs');
      const prepared=await prepareAudio(new File([window.testDownloads[0]],'download.wav'));
      const a=new Uint8Array(await prepared.file.arrayBuffer()),b=new Uint8Array(await window.testAudioFiles[0].arrayBuffer());
      return a.length===b.length&&a.every((value,index)=>value===b[index]);})()`),true);
    await evaluate(`(async()=>{const blob=await(await fetch('/saved.wav')).blob();const transfer=new DataTransfer();
      transfer.items.add(new File([blob],'saved.wav',{type:'audio/wav'}));const input=document.getElementById('file');
      input.files=transfer.files;input.dispatchEvent(new Event('change'));document.getElementById('speakers').checked=true;
      document.getElementById('transcribe').click();})()`);
    for (let i = 0; i < 100 && await evaluate('window.testPayloads.length') < 2; i++) await delay(50);
    assert.equal(await evaluate('window.testPayloads[1].size'), 32044);
    assert.equal(await evaluate('window.testPayloads[1].name'), 'saved.wav');
    assert.equal(await evaluate('window.testManualVAD'),true);
    for (let i = 0; i < 100 && !await evaluate("document.getElementById('transcript').value.includes('日本語')"); i++) await delay(50);
    assert.match(await evaluate("document.getElementById('transcript').value"), /\(14:00:08\) Speaker 1: 日本語 Test/);
    for (const [button,label] of [['exportDrive','Export'],['importDrive','Import'],['clearDrive','Clear']]) {
      const options = await evaluate(`(()=>{document.getElementById('${button}').click();return {
        open:document.getElementById('driveImportDialog').open,label:document.getElementById('driveImportApply').textContent,
        outputHidden:document.getElementById('driveImportOutputs').hidden,
        original:document.getElementById('driveFolderOriginal').checked};})()`);
      assert.equal(options.open,true);assert.equal(options.label,label);assert.equal(options.original,true);
      assert.equal(options.outputHidden,button!=='importDrive');
      await evaluate("document.getElementById('driveFolderOriginal').click()");
      assert.equal(await evaluate("document.getElementById('driveImportApply').textContent"),'Exit');
      await evaluate("document.getElementById('driveImportClose').click()");
      assert.equal(await evaluate('window.testRecorder.state'),'recording');
    }
    // VAD-only button reuses preparation but makes no provider or Drive calls.
    const previous = await evaluate('({providers:window.testPayloads.length,uploads:window.testUploads.length,text:document.getElementById("transcript").value})');
    await evaluate("document.getElementById('vadProcess').click()");
    for(let i=0;i<100&&!(await readdir(downloads)).some(name=>name.endsWith('-VAD.wav'));i++)await delay(50);
    assert.ok((await readdir(downloads)).some(name=>name.endsWith('-VAD.wav')));
    assert.deepEqual(await evaluate('({providers:window.testPayloads.length,uploads:window.testUploads.length,text:document.getElementById("transcript").value})'),previous);
    // Opting out restores the prior unfiltered capture for the next Stop.
    await evaluate("document.getElementById('audioEnhancement').checked=false;window.testCommand('stop')");
    for(let i=0;i<100&&!await evaluate('window.testDownloads.length>=3');i++)await delay(50);
    const raw=await evaluate(`(async()=>{const {prepareAudio}=await import('./js/audio-import.mjs');
      const parsed=await prepareAudio(new File([window.testDownloads.at(-1)],'raw.wav'));
      const pcm=new Int16Array(await parsed.file.slice(44).arrayBuffer());return {first:pcm[0],last:pcm.at(-1)};})()`);
    assert.ok(raw.first>8000&&raw.last>8000);
    await evaluate("window.testCommand('abort')");
    assert.equal(await evaluate('window.testRecorder.state'), 'idle');
  } finally {
    await cdp('Browser.close').catch(() => {}); browser.kill();
    await new Promise(resolve => server.close(resolve)); await delay(200);
    await rm(directory, { recursive: true, force: true, maxRetries: 5, retryDelay: 100 });
  }
});

