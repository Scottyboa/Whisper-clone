import test from 'node:test';
import assert from 'node:assert/strict';
import { createServer } from 'node:http';
import { spawn, spawnSync } from 'node:child_process';
import { readFile, mkdtemp, rm } from 'node:fs/promises';
import { fileURLToPath } from 'node:url';
import { resolve, join } from 'node:path';
import { tmpdir } from 'node:os';
import { protocol } from './helpers/browser.mjs';

const executable = process.env.WHISPER_TEST_CHROME;
const canSpeak = spawnSync('ffmpeg', ['-hide_banner', '-filters'], { encoding: 'utf8' }).stdout?.includes('flite');
const root = fileURLToPath(new URL('../', import.meta.url));

test('Chrome runs the real Silero worker on manual WAV, stereo FLAC, MP3, app FLAC and silence before Soniox',
  { skip: !executable || !canSpeak, timeout: 60000 }, async () => {
    const directory = await mkdtemp(join(tmpdir(), 'whisper-manual-vad-'));
    const speech = join(directory, 'speech.wav');
    const make = args => { const result = spawnSync('ffmpeg', ['-v', 'error', '-y', ...args]); assert.equal(result.status, 0, result.stderr.toString()); };
    make(['-f', 'lavfi', '-i', 'flite=text=This is a clear spoken sentence for testing the speech detector. We are checking that every word remains in the audio while long silent gaps are removed.:voice=slt', '-af', 'adelay=2000,apad=pad_dur=2', '-ar', '16000', '-ac', '1', speech]);
    make(['-i', speech, '-ac', '2', '-ar', '48000', '-c:a', 'flac', join(directory, 'speech.flac')]);
    make(['-i', speech, join(directory, 'speech.mp3')]);
    make(['-f', 'lavfi', '-i', 'anullsrc=r=16000:cl=mono', '-t', '0.768', '-frame_size', '4096', join(directory, 'silent.flac')]);
    let modelFails = false;
    const server = createServer(async (request, response) => {
      try {
        const path = new URL(request.url, 'http://localhost').pathname;
        if (path === '/fail-model') { modelFails = true; response.end('OK'); return; }
        if (modelFails && path.endsWith('/silero_vad_legacy.onnx')) { response.writeHead(503); response.end(); return; }
        let bytes;
        if (path === '/') bytes = '<html><body>Manual VAD test</body></html>';
        else if (/^\/(speech\.(wav|flac|mp3)|silent\.flac)$/.test(path)) bytes = await readFile(join(directory, path.slice(1)));
        else {
          const filename = resolve(root, '.' + path); if (!filename.startsWith(root)) throw new Error('Invalid path');
          bytes = await readFile(filename);
        }
        response.writeHead(200, { 'Cache-Control': 'no-store', 'Content-Type': path === '/' ? 'text/html' : /\.m?js$/.test(path) ? 'text/javascript' : path.endsWith('.wasm') ? 'application/wasm' : 'application/octet-stream' }); response.end(bytes);
      } catch { response.writeHead(404); response.end(); }
    });
    await new Promise(resolve => server.listen(0, '127.0.0.1', resolve));
    const browser = spawn(executable, ['--no-sandbox', '--headless', '--disable-gpu', '--no-zygote', '--no-first-run', '--remote-debugging-pipe', `--user-data-dir=${join(directory, 'profile')}`], { stdio: ['ignore', 'ignore', 'ignore', 'pipe', 'pipe'] });
    const cdp = protocol(browser);
    try {
      const { targetId } = await cdp('Target.createTarget', { url: `http://127.0.0.1:${server.address().port}/` });
      const { sessionId } = await cdp('Target.attachToTarget', { targetId, flatten: true });
      for (let i = 0; i < 100; i++) {
        const state = await cdp('Runtime.evaluate', { expression: 'location.protocol', returnByValue: true }, sessionId);
        if (state.result.value === 'http:') break;
        await new Promise(resolve => setTimeout(resolve, 20));
      }
      const result = await cdp('Runtime.evaluate', { awaitPromise: true, returnByValue: true, expression: `(async()=>{
        const {transcribeFile}=await import('./js/soniox.mjs');
        const {prepareManualAudio}=await import('./js/manual-vad.mjs');
        const {vadDownloadFile}=await import('./js/vad-download.mjs');
        const {wavBlob}=await import('./js/audio.mjs');
        const {encodeTimelineFlac}=await import('./js/timeline-flac.mjs');
        const realFetch=fetch.bind(window),uploads=[],jobs=[];
        window.fetch=async(url,options={})=>{
          if(!String(url).includes('soniox.com'))return realFetch(url,options);
          let response={};
          if(String(url).endsWith('/files')&&options.method==='POST'){
            const f=options.body.get('file');uploads.push({size:f.size,type:f.type,name:f.name});response={id:'file'};
          }else if(String(url).endsWith('/transcriptions')&&options.method==='POST'){jobs.push(JSON.parse(options.body));response={id:'job'};}
          else if(String(url).endsWith('/transcript'))response={tokens:[{text:'Speech test',speaker:1,start_ms:192}]};
          else if(options.method!=='DELETE')response={status:'completed'};
          return new Response(JSON.stringify(response));
        };
        const files={};for(const ext of ['wav','flac','mp3'])files[ext]=new File([await(await realFetch('/speech.'+ext)).blob()],'speech.'+ext);
        const statuses=[];
        for(const ext of ['wav','flac','mp3'])await transcribeFile(files[ext],'fixture-only',true,s=>statuses.push(s),{manualVAD:true});
        const counts={afterSpeech:uploads.length};
        const localDownloads=[];
        for(const ext of ['wav','flac','mp3']){
          const retained=await prepareManualAudio(files[ext]);
          const output=await vadDownloadFile(retained);
          localDownloads.push({name:output.name,type:output.type,size:output.size});
        }
        counts.afterLocalVAD=uploads.length;
        for(const file of [new File([wavBlob([new Int16Array(16000)])],'silent.wav'),new File([await(await realFetch('/silent.flac')).blob()],'silent.flac')]){
          try{await transcribeFile(file,'fixture-only',true,()=>{},{manualVAD:true});throw new Error('Silent file uploaded');}
          catch(e){if(e.message!=='No speech detected.')throw e;}
        }
        counts.afterSilence=uploads.length;
        // Preserve wall-clock metadata through extraction and another VAD pass.
        const context=new OfflineAudioContext(1,1,16000),decoded=await context.decodeAudioData(await files.wav.arrayBuffer());
        const float=decoded.getChannelData(0),pcm=Int16Array.from(float,v=>Math.round(v*32767));
        const epoch=Date.parse('2026-10-23T10:00:00Z');
        const timing={version:1,sampleRate:16000,timeZone:'Europe/Oslo',segments:[[0,pcm.length,epoch]]};
        const original=new File([wavBlob([pcm],timing)],'timed.wav');
        const first=await prepareManualAudio(original);
        const entry={startedAt:epoch,endedAt:epoch+pcm.length/16,audioMs:(first.file.size-44)/32};
        const encoded=await encodeTimelineFlac({blob:first.file,entry,timing:first.timing});
        const appFlac=new File([encoded.blob],'app.flac');
        const second=await prepareManualAudio(appFlac);
        const timedDownload=await vadDownloadFile(second);
        const {prepareAudio}=await import('./js/wav-timing.mjs');
        const downloadedTiming=(await prepareAudio(timedDownload)).timing;
        const clockText=await transcribeFile(appFlac,'fixture-only',true,()=>{},{manualVAD:true});
        // A model/network failure must fail before the provider upload begins.
        const beforeFailure=uploads.length;
        await realFetch('/fail-model');
        let failed=false;try{await transcribeFile(files.wav,'fixture-only',true,()=>{},{manualVAD:true});}catch{failed=true;}
        return {uploads,jobs,counts,sourceBytes:files.wav.size,statuses,clockText,timing:second.timing,downloadedTiming,localDownloads,
          kept:first.file.size,keptAgain:second.file.size,failed,beforeFailure};
      })()` }, sessionId);
      assert.equal(result.exceptionDetails, undefined, JSON.stringify(result.exceptionDetails));
      const value = result.result.value;
      assert.equal(value.counts.afterSpeech, 3); assert.equal(value.counts.afterSilence, 3);
      assert.equal(value.counts.afterLocalVAD,3);
      assert.ok(value.localDownloads.every(file=>file.name==='speech-VAD.wav'&&file.type==='audio/wav'&&file.size>32044&&file.size<value.sourceBytes));
      assert.deepEqual(value.downloadedTiming,value.timing);
      assert.ok(value.uploads.slice(0, 3).every(file => file.type === 'audio/wav' && file.name.endsWith('.wav') && file.size > 32044 && file.size < value.sourceBytes));
      assert.ok(value.jobs.every(job => job.enable_speaker_diarization === true));
      assert.ok(value.statuses.some(text => text.startsWith('Detecting speech')));
      assert.equal(value.timing.timeZone, 'Europe/Oslo'); assert.ok(value.timing.segments[0][2] > Date.parse('2026-10-23T10:00:01Z'));
      assert.match(value.clockText, /\(12:00:\d\d\) Speaker 1: Speech test/);
      assert.ok(value.keptAgain <= value.kept); assert.equal(value.failed, true); assert.equal(value.uploads.length, value.beforeFailure);
    } finally {
      await cdp('Browser.close').catch(() => {}); browser.kill();
      await new Promise(resolve => server.close(resolve));
      await rm(directory, { recursive: true, force: true, maxRetries: 5, retryDelay: 100 });
    }
  });
