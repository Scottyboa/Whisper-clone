import test from 'node:test';
import assert from 'node:assert/strict';
import { createServer } from 'node:http';
import { spawn, spawnSync } from 'node:child_process';
import { readFile, mkdir, mkdtemp, readdir, rm } from 'node:fs/promises';
import { fileURLToPath } from 'node:url';
import { resolve, join } from 'node:path';
import { tmpdir } from 'node:os';
import { protocol } from './helpers/browser.mjs';

const executable=process.env.WHISPER_TEST_CHROME;
const canSpeak=spawnSync('ffmpeg',['-hide_banner','-filters'],{encoding:'utf8'}).stdout?.includes('flite');
const root=fileURLToPath(new URL('../',import.meta.url));
const delay=ms=>new Promise(resolve=>setTimeout(resolve,ms));

test('Chrome Secondary rec runs real Silero once per batch, downloads playable merged WAV and sends one sectioned speaker job',
  {skip:!executable||!canSpeak,timeout:60000},async()=>{
  const directory=await mkdtemp(join(tmpdir(),'whisper-secondary-')),downloads=join(directory,'downloads');await mkdir(downloads);
  const make=args=>{const result=spawnSync('ffmpeg',['-v','error','-y',...args]);assert.equal(result.status,0,result.stderr.toString());};
  make(['-f','lavfi','-i','flite=text=This is the first recording. It contains a clear spoken sentence for the speech detector.:voice=slt','-af','adelay=2000,apad=pad_dur=2','-ar','16000','-ac','1',join(directory,'first.wav')]);
  make(['-f','lavfi','-i','flite=text=This is another recording. We are keeping this speech in the second part of the merged audio.:voice=slt','-af','adelay=2000,apad=pad_dur=2','-ar','48000','-ac','2','-c:a','pcm_s24le',join(directory,'last.wav')]);
  make(['-f','lavfi','-i','anullsrc=r=16000:cl=mono','-t','2',join(directory,'silent.wav')]);
  let modelLoads=0;
  const fixtures={
    '/js/graph.mjs':`export class MailControl{constructor(options){Object.assign(this,options);window.testCommand=options.onCommand;this.active=false}async client(){return {}}unlink(){}}`,
    '/js/device-control.mjs':`export const RECENT_MS=10000;export class DeviceControl{constructor(options){Object.assign(this,options);this.active=false;this.rows=[];this.pending=new Map()}async connect(){}disconnect(){}}`,
    '/js/transcript-drive.mjs':`export class TranscriptDrive{async upload(text,options){window.testDriveUploads.push({text,options});return options.name}}`,
  };
  const server=createServer(async(request,response)=>{
    try{
      const path=new URL(request.url,'http://localhost').pathname;
      if(path.endsWith('/silero_vad_legacy.onnx'))modelLoads++;
      let body;
      if(fixtures[path])body=fixtures[path];
      else if(/^\/(first|last|silent)\.wav$/.test(path))body=await readFile(join(directory,path.slice(1)));
      else if(path==='/'){
        const setup=`<script>
          sessionStorage.setItem('whisper-clone.soniox-key','fixture-only');
          window.testPayloads=[];window.testJobs=[];window.testDownloads=[];window.testDriveUploads=[];window.testDeletes=[];window.testConfirms=[];window.allowConfirm=true;
          window.confirm=text=>{window.testConfirms.push(text);return window.allowConfirm};
          const nativeURL=URL.createObjectURL.bind(URL);URL.createObjectURL=blob=>{window.testDownloads.push(blob);return nativeURL(blob)};
          const nativeFetch=fetch.bind(window);
          window.fetch=async(url,options={})=>{
            if(!String(url).includes('soniox.com'))return nativeFetch(url,options);
            let result={};
            if(String(url).endsWith('/files')&&options.method==='POST'){window.testPayloads.push(options.body.get('file'));result={id:'file'}}
            else if(String(url).endsWith('/transcriptions')&&options.method==='POST'){window.testJobs.push(JSON.parse(options.body));result={id:'job'}}
            else if(String(url).endsWith('/transcript')){
              const {readSecondary}=await import('./js/secondary-sections.mjs?v=20261025-secondary1');
              const saved=await readSecondary(window.testDownloads[0]);
              result={tokens:[{text:'First clip speech',speaker:1,start_ms:0},{text:'Last clip speech',speaker:2,start_ms:saved.secondary.ranges[1][0]/16}]};
            }else if(options.method==='DELETE')window.testDeletes.push(String(url));
            else result={status:'completed'};
            return new Response(JSON.stringify(result));
          };
        </script>`;
        body=(await readFile(join(root,'index.html'),'utf8')).replace('<head>','<head>'+setup);
      }else{const filename=resolve(root,'.'+path);if(!filename.startsWith(root))throw new Error('Invalid fixture path');body=await readFile(filename);}
      response.writeHead(200,{'Cache-Control':'no-store','Content-Type':path==='/'?'text/html':/\.m?js$/.test(path)?'text/javascript':path.endsWith('.css')?'text/css':path.endsWith('.wasm')?'application/wasm':'application/octet-stream'});response.end(body);
    }catch{response.writeHead(404);response.end();}
  });
  await new Promise(resolve=>server.listen(0,'127.0.0.1',resolve));
  const browser=spawn(executable,['--no-sandbox','--headless','--disable-gpu','--no-zygote','--no-first-run','--remote-debugging-pipe',`--user-data-dir=${join(directory,'profile')}`],{stdio:['ignore','ignore','ignore','pipe','pipe']});
  const cdp=protocol(browser);
  try{
    await cdp('Browser.setDownloadBehavior',{behavior:'allow',downloadPath:downloads});
    const {targetId}=await cdp('Target.createTarget',{url:`http://127.0.0.1:${server.address().port}/`});
    const {sessionId}=await cdp('Target.attachToTarget',{targetId,flatten:true});
    await cdp('Emulation.setTimezoneOverride',{timezoneId:'Europe/Oslo'},sessionId);
    const evaluate=async expression=>{const result=await cdp('Runtime.evaluate',{expression,awaitPromise:true,returnByValue:true},sessionId);assert.equal(result.exceptionDetails,undefined,JSON.stringify(result.exceptionDetails));return result.result.value;};
    for(let i=0;i<100&&!await evaluate("typeof window.testCommand==='function'");i++)await delay(30);
    assert.equal(await evaluate("typeof window.testCommand==='function'"),true);
    await evaluate(`(async()=>{
      document.getElementById('speakers').checked=false;
      const transfer=new DataTransfer();
      for(const [path,name] of [['last.wav','R-00058_2610251719_SVOS.WAV'],['silent.wav','R-00041_2610251511_SVOS.WAV'],['first.wav','R-00040_2610251509_SVOS.WAV']])
        transfer.items.add(new File([await(await fetch('/'+path)).blob()],name,{type:'audio/wav'}));
      const input=document.getElementById('secondaryFiles');input.files=transfer.files;input.dispatchEvent(new Event('change'));
    })()`);
    for(let i=0;i<600&&!await evaluate("document.getElementById('transcript').value.includes('Last clip speech')&&!document.getElementById('secondaryRec').disabled");i++)await delay(40);
    const state=await evaluate(`({text:document.getElementById('transcript').value,status:document.getElementById('message').textContent,downloads:window.testDownloads.length,uploads:window.testPayloads.length,jobs:window.testJobs,speakers:document.getElementById('speakers').checked,deletes:window.testDeletes.length,drive:window.testDriveUploads.length,confirmation:window.testConfirms[0]})`);
    assert.equal(state.uploads,1,state.status);assert.equal(state.downloads,1);assert.equal(state.jobs.length,1);assert.equal(state.jobs[0].enable_speaker_diarization,true);assert.equal(state.speakers,true);assert.equal(state.deletes,2);assert.equal(state.drive,0);
    assert.match(state.text,/^secondary rec - 2026-10-25_15-09-00-000_to_2026-10-25_17-19-00-000_VAD-/);
    assert.match(state.text,/15:09[^]*Speaker 1: First clip speech[^]*15:11[^]*\[No speech detected\.\][^]*17:19[^]*Speaker 2: Last clip speech/);
    assert.match(state.confirmation,/Merge 3 secondary WAV files/);assert.equal(modelLoads,1,'one model load must serve the whole batch');
    for(let i=0;i<100&&!(await readdir(downloads)).some(name=>name.endsWith('.wav'));i++)await delay(30);
    const files=(await readdir(downloads)).filter(name=>name.endsWith('.wav'));assert.equal(files.length,1);assert.match(files[0],/^secondary rec - 2026-10-25_15-09-00_to_17-19-00_/);
    const check=await evaluate(`(async()=>{
      const {prepareAudio}=await import('./js/audio-import.mjs?v=20261025-secondary1');
      const parsed=await prepareAudio(window.testDownloads[0]);
      const a=new Uint8Array(await parsed.file.arrayBuffer()),b=new Uint8Array(await window.testPayloads[0].arrayBuffer());
      const context=new OfflineAudioContext(1,1,16000),decoded=await context.decodeAudioData(await window.testDownloads[0].arrayBuffer());
      return {same:a.length===b.length&&a.every((v,i)=>v===b[i]),duration:decoded.duration,ranges:parsed.secondary.ranges.length,channels:decoded.numberOfChannels};
    })()`);
    assert.equal(check.same,true);assert.equal(check.ranges,2);assert.equal(check.channels,1);assert.ok(check.duration>5&&check.duration<20);
    await evaluate("window.allowConfirm=false;document.getElementById('secondaryFiles').dispatchEvent(new Event('change'))");
    assert.equal(await evaluate('window.testPayloads.length'),1);assert.equal(modelLoads,1);
    // Reimport plus another real Silero pass preserves the source sections.
    const reimport=await evaluate(`(async()=>{
      const {prepareManualAudio}=await import('./js/manual-vad.mjs?v=20261025-secondary1');
      const result=await prepareManualAudio(window.testDownloads[0]);
      return {sources:result.secondary.sources.map(s=>s.time),ranges:result.secondary.ranges.length,bytes:result.file.size};
    })()`);
    assert.deepEqual(reimport.sources,['15:09','15:11','17:19']);assert.equal(reimport.ranges,2);assert.ok(reimport.bytes>44);
  }finally{
    await cdp('Browser.close').catch(()=>{});browser.kill();await new Promise(resolve=>server.close(resolve));
    await rm(directory,{recursive:true,force:true,maxRetries:5,retryDelay:100});
  }
});
