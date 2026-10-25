import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { secondarySource, sortSecondaryFiles, validateSecondary, readSecondary, attachSecondary, retainedSecondary, secondaryNames, renderSecondary } from '../js/secondary-sections.mjs';
import { wavBlob } from '../js/audio.mjs';
import { renderTranscript } from '../js/soniox.mjs';

const clock = stamp => {const source=secondarySource(`R-00001_${stamp}_SVOS.WAV`);return `${source.date} ${source.time}`;};

test('secondary fixed summer clock becomes Norway winter time while summer recordings keep their labels',()=>{
  assert.equal(clock('2610251500'),'2026-10-25 14:00');
  assert.equal(clock('2610241500'),'2026-10-24 15:00');
  assert.equal(clock('2606151500'),'2026-06-15 15:00');
  assert.equal(clock('2612151500'),'2026-12-15 14:00');
});

test('the Norway clock transition is evaluated at the recorded instant, including the spring jump',()=>{
  assert.equal(clock('2610250259'),'2026-10-25 02:59');
  assert.equal(clock('2610250300'),'2026-10-25 02:00');
  assert.equal(clock('2603290259'),'2026-03-29 01:59');
  assert.equal(clock('2603290300'),'2026-03-29 03:00');
});

test('winter correction rolls the date back across midnight, month and year boundaries',()=>{
  assert.equal(clock('2610260030'),'2026-10-25 23:30');
  assert.equal(clock('2611010030'),'2026-10-31 23:30');
  assert.equal(clock('2701010030'),'2026-12-31 23:30');
});

test('capture order survives the autumn repeated hour even when corrected clock labels run backwards',()=>{
  const files=['R-00002_2610250300_SVOS.WAV','R-00001_2610250259_SVOS.WAV'].map(name=>({name}));
  const sorted=sortSecondaryFiles(files);
  assert.deepEqual(sorted.map(item=>item.source.time),['02:59','02:00']);
  assert.equal(sorted[0].source.sequence,1);
});

test('secondary conversion stays in Norway time on computers in other timezones',()=>{
  const result=spawnSync(process.execPath,['--input-type=module','-e',`import {secondarySource} from './js/secondary-sections.mjs';console.log(JSON.stringify(secondarySource('R-00001_2610251500_SVOS.WAV')));`],
    {cwd:new URL('../',import.meta.url),env:{...process.env,TZ:'America/Los_Angeles'},encoding:'utf8'});
  assert.equal(result.status,0,result.stderr);assert.equal(JSON.parse(result.stdout).time,'14:00');
});

function legacyWav() {
  const original=new File([wavBlob([new Int16Array(16000).fill(1000)])],'legacy.wav',{type:'audio/wav'});
  const map={version:1,sampleRate:16000,sources:[{name:'R-00001_2610251500_SVOS.WAV',date:'2026-10-25',time:'15:00',sequence:1}],ranges:[[0,16000,0]]};
  return {original,map};
}
async function legacyFile(original,map) {
  const json=new TextEncoder().encode(JSON.stringify(map)),chunk=new Uint8Array(8+json.length+json.length%2);
  chunk.set(new TextEncoder().encode('wcsr'));new DataView(chunk.buffer).setUint32(4,json.length,true);chunk.set(json,8);
  const prefix=new Uint8Array(await original.slice(0,12).arrayBuffer());new DataView(prefix.buffer).setUint32(4,original.size+chunk.length-8,true);
  return new File([prefix,original.slice(12),chunk],original.name,{type:'audio/wav'});
}

test('old secondary WAV metadata imports without errors, corrects headings once and keeps its PCM unchanged',async()=>{
  const {original,map}=legacyWav();
  const prepared=await readSecondary(await legacyFile(original,map));
  assert.equal(prepared.secondary.version,2);assert.equal(prepared.secondary.sources[0].time,'14:00');
  assert.match(prepared.file.name,/^secondary rec - 2026-10-25_14-00-00_to_14-00-00_/);
  assert.deepEqual(new Uint8Array(await prepared.file.arrayBuffer()),new Uint8Array(await original.arrayBuffer()));
  const saved=await attachSecondary(prepared.file,prepared.secondary);
  const again=await readSecondary(saved);assert.equal(again.secondary.sources[0].time,'14:00');
  const trimmed=retainedSecondary(again.secondary,[[0,8000]],8000);assert.equal(trimmed.sources[0].time,'14:00');
  const names=secondaryNames(trimmed);assert.match(names.wav,/2026-10-25_14-00-00_to_14-00-00/);assert.match(names.transcript,/_14-00-00-000/);
  const text=renderSecondary({tokens:[{text:'Example',start_ms:0,speaker:1}]},trimmed,renderTranscript);
  assert.match(text,/2026-10-25 14:00 — R-00001_2610251500_SVOS.WAV/);
  assert.match(text,/Speaker 1: Example/);
});

test('new metadata validates corrected dates against raw names and rejects double-shifted labels or unknown versions',()=>{
  const {map}=legacyWav(),corrected=validateSecondary(map,16000);
  assert.deepEqual(validateSecondary(corrected,16000),corrected);
  assert.throws(()=>validateSecondary({...corrected,sources:[{...corrected.sources[0],time:'13:00'}]},16000));
  assert.throws(()=>validateSecondary({...corrected,version:3},16000));
});
