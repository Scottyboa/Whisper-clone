import test from 'node:test';
import assert from 'node:assert/strict';
import { wavBlob } from '../js/audio.mjs';
import { mergeSecondaryRecordings } from '../js/secondary-recordings.mjs';
import { secondarySource, sortSecondaryFiles, secondaryNames, readSecondary, retainedSecondary, renderSecondary, attachSecondary, validateSecondary } from '../js/secondary-sections.mjs';
import { prepareAudio } from '../js/audio-import.mjs';
import { renderTranscript, transcribeFile } from '../js/soniox.mjs';
import { createManualVADSession, cancelManualVAD } from '../js/manual-vad.mjs';
import { vadDownloadFile } from '../js/vad-download.mjs';

const names = ['R-00040_2610251509_SVOS.WAV','R-00041_2610251511_SVOS.WAV','R-00058_2610251719_SVOS.WAV'];
const source = (name, value = 1000) => new File([wavBlob([new Int16Array(16000).fill(value)])],name,{type:'audio/wav'});
function session({silent = [], fail = null} = {}) {
  const calls = []; let closes = 0;
  return {calls,get closes(){return closes;},create:() => ({prepare:async file => {
    calls.push(file.name);
    if (file.name === fail) throw new Error('Input decode failed');
    return silent.includes(file.name) ? {empty:true} : {file, timing:null};
  },close(){closes++;}})};
}

test('filename dates are parsed strictly and selection order is chronological, including tied minutes and midnight', () => {
  assert.deepEqual(secondarySource(names[2]),{name:names[2],date:'2026-10-25',time:'17:19',sequence:58});
  const sorted = sortSecondaryFiles([source('R-00059_2610260001_SVOS.WAV'),source(names[2]),source(names[0]),source('R-00039_2610251509_SVOS.WAV')]);
  assert.deepEqual(sorted.map(item=>item.source.time),['15:09','15:09','17:19','00:01']);
  assert.equal(sorted[0].source.sequence,39);
  for (const name of ['test.wav','R-1_2610321509_SVOS.WAV','R-1_2602291509_SVOS.WAV','R-1_2610252400_SVOS.WAV','R-1_2610251560_SVOS.WAV']) assert.throws(()=>secondarySource(name));
  assert.throws(()=>sortSecondaryFiles([source(names[0]),source(names[0])]),/Duplicate/);
  assert.throws(()=>sortSecondaryFiles([]),/Choose between/);
});

test('merge uses one session, skips silent audio, preserves PCM and keeps all dated source headings',async()=>{
  const runner=session({silent:[names[1]]});
  const result=await mergeSecondaryRecordings([source(names[2],3000),source(names[1]),source(names[0],1000)],()=>{},runner.create);
  assert.deepEqual(runner.calls,names);assert.equal(runner.closes,1);
  assert.equal(result.file.name,'secondary rec - 2026-10-25_15-09-00_to_17-19-00_(0m2s).wav');
  const parsed=await readSecondary(result.file),view=new DataView(await parsed.file.arrayBuffer());
  assert.equal(parsed.file.size,64044);assert.equal(view.getInt16(44,true),1000);assert.equal(view.getInt16(32044,true),3000);
  assert.deepEqual(parsed.secondary.ranges,[[0,16000,0],[16000,16000,2]]);
  const text=renderSecondary({tokens:[{text:'First',start_ms:0,speaker:1},{text:'Last',start_ms:1000,speaker:1}]},parsed.secondary,renderTranscript);
  assert.match(text,/^secondary rec - .*_VAD-0m2s\.txt/);
  assert.ok(text.indexOf('15:09 —')<text.indexOf('15:11 —'));assert.ok(text.indexOf('15:11 —')<text.indexOf('17:19 —'));
  assert.match(text,/15:11[^]*\[No speech detected\.\]/);assert.equal(text.match(/Speaker 1:/g).length,2);
  assert.doesNotMatch(text,/\(15:/,'filename times must not become invented clock timestamps inside clips');
});

test('all silence and any failed source produce no partial merged output and always close the session',async()=>{
  const empty=session({silent:names});assert.deepEqual(await mergeSecondaryRecordings(names.map(name=>source(name)),()=>{},empty.create),{empty:true});assert.equal(empty.closes,1);
  const bad=session({fail:names[1]});await assert.rejects(mergeSecondaryRecordings(names.map(name=>source(name)),()=>{},bad.create),/decode failed/);assert.equal(bad.closes,1);
});

test('titles use full dates across midnight and the last filename time rather than guessed voice-activation duration',async()=>{
  const runner=session();
  const result=await mergeSecondaryRecordings([source('R-00059_2610260001_SVOS.WAV'),source('R-00058_2610252359_SVOS.WAV')],()=>{},runner.create);
  assert.equal(result.file.name,'secondary rec - 2026-10-25_23-59-00_to_2026-10-26_00-01-00_(0m2s).wav');
  assert.equal(secondaryNames(result.secondary).transcript,'secondary rec - 2026-10-25_23-59-00-000_to_2026-10-26_00-01-00-000_VAD-0m2s.txt');
});

test('new VAD cuts preserve file sections across removed audio and a downloaded VAD-only reimport',async()=>{
  const runner=session(),merged=await mergeSecondaryRecordings(names.map(name=>source(name)),()=>{},runner.create);
  const secondary=retainedSecondary(merged.secondary,[[8000,16000],[40000,8000]],24000);
  assert.deepEqual(secondary.ranges,[[0,8000,0],[8000,8000,1],[16000,8000,2]]);
  const output=await vadDownloadFile({file:new File([wavBlob([new Int16Array(24000)])],'merged.wav'),timing:null,secondary});
  const parsed=await prepareAudio(output);assert.deepEqual(parsed.secondary,secondary);assert.equal(parsed.file.size,48044);
  const decoded=new TextDecoder().decode(await parsed.file.arrayBuffer());assert.ok(!decoded.includes('R-00040'));
});

test('metadata validation rejects malformed ranges and changed filename dates',async()=>{
  const map={version:3,sampleRate:16000,sources:[secondarySource(names[0])],ranges:[[0,16000,0]]};
  assert.throws(()=>validateSecondary({...map,ranges:[[1,16000,0]]},16000));
  assert.throws(()=>validateSecondary({...map,sources:[{...map.sources[0],time:'12:00'}]},16000));
  const file=await attachSecondary(source(names[0]),map);
  const buffer=new Uint8Array(await file.arrayBuffer());
  const at=Buffer.from(buffer).indexOf('"version":3');buffer[at+10]='9'.charCodeAt(0);
  await assert.rejects(readSecondary(new File([buffer],'broken.wav')),/Invalid secondary/);
});

test('Soniox uploads one clean merged WAV with speakers forced on, renders each original file and cleans up',async()=>{
  const runner=session(),merged=await mergeSecondaryRecordings([source(names[2]),source(names[0])],()=>{},runner.create);
  const original=globalThis.fetch,uploads=[],jobs=[],deletes=[],contexts=[];
  globalThis.fetch=async(url,options={})=>{
    let result={};
    if (url.endsWith('/files')&&options.method==='POST'){uploads.push(options.body.get('file'));result={id:'file'};}
    else if (url.endsWith('/transcriptions')&&options.method==='POST'){jobs.push(JSON.parse(options.body));result={id:'job'};}
    else if (url.endsWith('/transcript'))result={tokens:[{text:'Hello',speaker:1,start_ms:0},{text:'There',speaker:2,start_ms:1000}]};
    else if (options.method==='DELETE')deletes.push(url);
    else result={status:'completed'};
    return new Response(JSON.stringify(result));
  };
  try {
    const text=await transcribeFile(merged.file,'test',false,(status,text,error,context)=>{if(context)contexts.push(context);});
    assert.equal(uploads.length,1);assert.equal(uploads[0].size,64044);assert.equal(jobs.length,1);assert.equal(jobs[0].enable_speaker_diarization,true);
    assert.equal(await readSecondary(uploads[0]),null);assert.equal(deletes.length,2);
    assert.match(text,/15:09[^]*Speaker 1: Hello[^]*17:19[^]*Speaker 2: There/);
    assert.equal(contexts[0].filename,secondaryNames(merged.secondary).transcript);
  } finally {globalThis.fetch=original;}
});

test('a shared manual VAD session reuses one worker and page close cancels its current job',async()=>{
  const original=globalThis.Worker;let starts=0,terminations=0,resolveStarted;
  const started=new Promise(resolve=>resolveStarted=resolve);
  globalThis.Worker=class {
    constructor(){starts++;}terminate(){terminations++;}
    postMessage({prepared}){if(prepared.file.name===names[2]){resolveStarted();return;}queueMicrotask(()=>this.onmessage({data:{result:{file:prepared.file,timing:null}}}));}
  };
  let runner;
  try {
    runner=createManualVADSession();await runner.prepare(source(names[0]));await runner.prepare(source(names[1]));
    const pending=runner.prepare(source(names[2]));await started;cancelManualVAD();await assert.rejects(pending,/cancelled/);
    runner.close();assert.equal(starts,1);assert.equal(terminations,1);
  } finally {runner?.close();globalThis.Worker=original;}
});

test('provider text without usable token timestamps fails instead of assigning all text to an invented section',async()=>{
  const runner=session(),merged=await mergeSecondaryRecordings([source(names[0])],()=>{},runner.create);
  assert.throws(()=>renderSecondary({text:'No token timing'},merged.secondary,renderTranscript),/timestamps/);
  assert.throws(()=>renderSecondary({tokens:[{text:'No timestamp'}]},merged.secondary,renderTranscript),/timestamps/);
  assert.throws(()=>renderSecondary({tokens:[{text:'Too late',start_ms:1001}]},merged.secondary,renderTranscript),/outside/);
});


test('REC and SVOS files merge together in filename order with unadjusted titles and source headings',async()=>{
  const rec='R-00059_2610252019_REC.WAV',runner=session();
  assert.deepEqual(secondarySource(rec),{name:rec,date:'2026-10-25',time:'20:19',sequence:59});
  assert.equal(secondarySource('R-00059_2610252019_rec.wav').time,'20:19');
  const merged=await mergeSecondaryRecordings([source(rec,3000),source(names[2],2000),source(names[0],1000)],()=>{},runner.create);
  assert.deepEqual(runner.calls,[names[0],names[2],rec]);
  assert.equal(merged.file.name,'secondary rec - 2026-10-25_15-09-00_to_20-19-00_(0m3s).wav');
  const prepared=await readSecondary(merged.file);assert.equal(prepared.secondary.version,3);
  const text=renderSecondary({tokens:[{text:'First',start_ms:0,speaker:1},{text:'Middle',start_ms:1000,speaker:2},{text:'REC clip',start_ms:2000,speaker:1}]},prepared.secondary,renderTranscript);
  assert.match(text,/15:09[^]*Speaker 1: First[^]*17:19[^]*Speaker 2: Middle[^]*20:19 — R-00059_2610252019_REC.WAV[^]*Speaker 1: REC clip/);
  assert.match(secondaryNames(prepared.secondary).transcript,/_20-19-00-000_VAD-0m3s\.txt$/);
});
