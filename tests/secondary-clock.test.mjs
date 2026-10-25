import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { secondarySource, sortSecondaryFiles, validateSecondary, readSecondary, attachSecondary, retainedSecondary, secondaryNames, renderSecondary } from '../js/secondary-sections.mjs';
import { wavBlob } from '../js/audio.mjs';
import { renderTranscript } from '../js/soniox.mjs';

const clock = (stamp,ending='SVOS') => {const source=secondarySource(`R-00001_${stamp}_${ending}.WAV`);return `${source.date} ${source.time}`;};

test('secondary filename clocks stay verbatim in winter and summer for both recorder modes',()=>{
  for (const ending of ['SVOS','REC']) {
    assert.equal(clock('2610251500',ending),'2026-10-25 15:00');
    assert.equal(clock('2610241500',ending),'2026-10-24 15:00');
    assert.equal(clock('2606151500',ending),'2026-06-15 15:00');
    assert.equal(clock('2612151500',ending),'2026-12-15 15:00');
    assert.equal(clock('2610252019',ending),'2026-10-25 20:19');
  }
});

test('clock-change dates and midnight never shift filename labels or dates',()=>{
  for(const [stamp,label] of [['2610250259','2026-10-25 02:59'],['2610250300','2026-10-25 03:00'],
    ['2603290259','2026-03-29 02:59'],['2603290300','2026-03-29 03:00'],
    ['2610260030','2026-10-26 00:30'],['2611010030','2026-11-01 00:30'],['2701010030','2027-01-01 00:30']])
    assert.equal(clock(stamp),label);
});

test('mixed recorder modes sort by unadjusted filename timestamps',()=>{
  const sorted=sortSecondaryFiles(['R-00059_2610252019_REC.WAV','R-00058_2610251719_SVOS.WAV'].map(name=>({name})));
  assert.deepEqual(sorted.map(item=>item.source.time),['17:19','20:19']);
});

test('filename times are independent of the computer timezone',()=>{
  const result=spawnSync(process.execPath,['--input-type=module','-e',`import {secondarySource} from './js/secondary-sections.mjs';console.log(JSON.stringify(secondarySource('R-00059_2610252019_REC.WAV')));`],
    {cwd:new URL('../',import.meta.url),env:{...process.env,TZ:'America/Los_Angeles'},encoding:'utf8'});
  assert.equal(result.status,0,result.stderr);assert.equal(JSON.parse(result.stdout).time,'20:19');
});

function legacyWav(version) {
  const original=new File([wavBlob([new Int16Array(16000).fill(1000)])],'legacy.wav',{type:'audio/wav'});
  const map={version,sampleRate:16000,sources:[{name:'R-00001_2610251500_SVOS.WAV',date:'2026-10-25',time:version===2?'14:00':'15:00',sequence:1}],ranges:[[0,16000,0]]};
  return {original,map};
}
async function legacyFile(original,map) {
  const json=new TextEncoder().encode(JSON.stringify(map)),chunk=new Uint8Array(8+json.length+json.length%2);
  chunk.set(new TextEncoder().encode('wcsr'));new DataView(chunk.buffer).setUint32(4,json.length,true);chunk.set(json,8);
  const prefix=new Uint8Array(await original.slice(0,12).arrayBuffer());new DataView(prefix.buffer).setUint32(4,original.size+chunk.length-8,true);
  return new File([prefix,original.slice(12),chunk],original.name,{type:'audio/wav'});
}

test('both old secondary metadata versions restore raw filename labels without changing PCM or shifting again',async()=>{
  for(const version of [1,2]) {
    const {original,map}=legacyWav(version);
    const prepared=await readSecondary(await legacyFile(original,map));
    assert.equal(prepared.secondary.version,3);assert.equal(prepared.secondary.sources[0].time,'15:00');
    assert.match(prepared.file.name,/^secondary rec - 2026-10-25_15-00-00_to_15-00-00_/);
    assert.deepEqual(new Uint8Array(await prepared.file.arrayBuffer()),new Uint8Array(await original.arrayBuffer()));
    const saved=await attachSecondary(prepared.file,prepared.secondary);
    const again=await readSecondary(saved);assert.equal(again.secondary.sources[0].time,'15:00');
    const trimmed=retainedSecondary(again.secondary,[[0,8000]],8000);assert.equal(trimmed.sources[0].time,'15:00');
    const names=secondaryNames(trimmed);assert.match(names.wav,/2026-10-25_15-00-00_to_15-00-00/);assert.match(names.transcript,/_15-00-00-000/);
    const text=renderSecondary({tokens:[{text:'Example',start_ms:0,speaker:1}]},trimmed,renderTranscript);
    assert.match(text,/2026-10-25 15:00 — R-00001_2610251500_SVOS.WAV/);assert.match(text,/Speaker 1: Example/);
  }
});

test('version 2 metadata crossing midnight restores the original date from its source filename',()=>{
  const map={version:2,sampleRate:16000,sources:[{name:'R-00001_2610260030_SVOS.WAV',date:'2026-10-25',time:'23:30',sequence:1}],ranges:[[0,16000,0]]};
  const result=validateSecondary(map,16000);
  assert.equal(result.sources[0].date,'2026-10-26');assert.equal(result.sources[0].time,'00:30');
});

test('current metadata validates original labels and rejects damaged times and unknown versions',()=>{
  const {map}=legacyWav(1),current=validateSecondary(map,16000);
  assert.deepEqual(validateSecondary(current,16000),current);
  assert.throws(()=>validateSecondary({...current,sources:[{...current.sources[0],time:'14:00'}]},16000));
  assert.throws(()=>validateSecondary({...current,version:4},16000));
});
