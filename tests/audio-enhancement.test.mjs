import test from 'node:test';
import assert from 'node:assert/strict';
import {spawnSync} from 'node:child_process';
import {wavBlob} from '../js/audio.mjs';
import {wavFormat} from '../js/file-audio.mjs';
import {prepareAudio} from '../js/audio-import.mjs';
import {attachSecondary} from '../js/secondary-sections.mjs';
import {enhanceAudioFile, AUDIO_ENHANCEMENT} from '../js/audio-enhancement.mjs';

const rate=16000;
const tone=(hz,amplitude=0.1,seconds=6)=>Int16Array.from({length:rate*seconds},(_,i)=>Math.round(32767*amplitude*Math.sin(2*Math.PI*hz*i/rate)));
const wav=pcm=>new File([wavBlob([pcm])],'source.wav',{type:'audio/wav',lastModified:1234});
const pcm=async file=>{const f=await wavFormat(file);return new Int16Array(await file.slice(f.start,f.start+f.size).arrayBuffer());};
const rms=(samples,start=16000)=>Math.sqrt(samples.subarray(start).reduce((n,x)=>n+x*x,0)/(samples.length-start));

test('70 Hz filtering attenuates low rumble while preserving speech-band tone and respecting gain limits',async()=>{
  for(const [hz,minimum,maximum] of [[20,0.07,0.09],[1000,0.99,1.01]]){
    const input=tone(hz),output=await pcm(await enhanceAudioFile(wav(input)));
    const response=rms(output)/rms(input)/AUDIO_ENHANCEMENT.maxGain;
    assert.ok(response>minimum&&response<maximum,`${hz} Hz response ${response}`);
    assert.equal(output.length,input.length);
  }
  const loud=await pcm(await enhanceAudioFile(wav(tone(1000,0.95))));
  assert.ok(loud.every(value=>Math.abs(value)<=Math.ceil(AUDIO_ENHANCEMENT.peak*32768)));
});

test('bounded reads preserve filter state and gain over chunk boundaries and leave the input unchanged',async()=>{
  const original=tone(1000),blob=wavBlob([original]);let largest=0;
  class BoundedFile extends File {
    arrayBuffer(){throw new Error('Whole-file read is forbidden');}
    slice(...args){const part=super.slice(...args),read=part.arrayBuffer.bind(part);
      part.arrayBuffer=()=>{largest=Math.max(largest,part.size);assert.ok(part.size<=131072);return read();};return part;}
  }
  const input=new BoundedFile([blob],'long.wav',{type:'audio/wav'}),output=await pcm(await enhanceAudioFile(input));
  assert.ok(largest>100000);assert.equal(output.length,original.length);
  for(let i=0;i<2000;i++)assert.ok(Math.abs(output[65536+2000+i]-output[2000+i])<=1);
  assert.deepEqual(new Int16Array(await blob.slice(44).arrayBuffer()),original);
});

test('stereo channels keep their separate signal, duration and sample rate',async()=>{
  const mono=tone(440),stereo=Int16Array.from({length:mono.length*2},(_,i)=>i%2?-mono[i>>1]:mono[i>>1]);
  const header=new Uint8Array(await wavBlob([]).arrayBuffer()),v=new DataView(header.buffer);
  v.setUint16(22,2,true);v.setUint32(28,rate*4,true);v.setUint16(32,4,true);
  v.setUint32(4,36+stereo.byteLength,true);v.setUint32(40,stereo.byteLength,true);
  const output=await enhanceAudioFile(new File([header,stereo],'stereo.wav',{type:'audio/wav'})),f=await wavFormat(output),samples=await pcm(output);
  assert.equal(f.channels,2);assert.equal(f.sampleRate,rate);assert.equal(samples.length,stereo.length);
  assert.ok(samples.some(value=>Math.abs(value)>1000));
  for(let i=0;i<samples.length;i+=2)assert.ok(Math.abs(samples[i]+samples[i+1])<=1);
});

test('clock maps, source ranges, file names and metadata bytes survive enhancement unchanged',async()=>{
  const input=tone(440,0.1,2),timing={version:1,sampleRate:rate,timeZone:'UTC',segments:[[0,input.length,Date.parse('2026-10-30T10:00:00Z')]]};
  const map={version:3,sampleRate:rate,sources:[{name:'R-00001_2610301000_REC.WAV',date:'2026-10-30',time:'10:00',sequence:1}],ranges:[[0,input.length,0]]};
  const file=await attachSecondary(new File([wavBlob([input],timing)],'metadata.wav',{type:'audio/wav'}),map,input.length);
  const f=await wavFormat(file),output=await enhanceAudioFile(file),prepared=await prepareAudio(output);
  assert.equal(output.name,file.name);assert.equal(output.size,file.size);assert.equal(output.lastModified,file.lastModified);
  assert.deepEqual(prepared.timing,timing);assert.deepEqual(prepared.secondary,map);
  assert.deepEqual(await output.slice(0,f.start).arrayBuffer(),await file.slice(0,f.start).arrayBuffer());
  assert.deepEqual(await output.slice(f.start+f.size).arrayBuffer(),await file.slice(f.start+f.size).arrayBuffer());
  assert.notDeepEqual(await pcm(output),input);
});

test('disabled enhancement is a byte-identical no-op; silent audio stays silent and invalid audio fails',async()=>{
  const file=new File(['not audio'],'source.bin');assert.equal(await enhanceAudioFile(file,()=>{},{enabled:false}),file);
  await assert.rejects(enhanceAudioFile(file),/VAD-processed PCM16 WAV/);
  const silence=wav(new Int16Array(200000));assert.deepEqual(await pcm(await enhanceAudioFile(silence)),new Int16Array(200000));
});

test('cancellation during enhancement produces no partial output',async()=>{
  const abort=new AbortController();let progress=0;
  await assert.rejects(enhanceAudioFile(wav(tone(440)),()=>{progress++;abort.abort();},{signal:abort.signal}),{name:'AbortError'});
  assert.equal(progress,1);
});

test('filter agrees with an independent FFmpeg Butterworth high-pass', {skip:spawnSync('ffmpeg',['-version']).status!==0},async()=>{
  const input=tone(440,0.1,2),file=wav(input);
  const reference=spawnSync('ffmpeg',['-v','error','-i','pipe:0','-af','highpass=f=70:t=q:w=0.7071067811865476:p=2:r=f64','-f','f32le','pipe:1'],
    {input:Buffer.from(await file.arrayBuffer()),maxBuffer:2*1024*1024});
  assert.equal(reference.status,0,reference.stderr.toString());
  const expected=new Float32Array(reference.stdout.buffer.slice(reference.stdout.byteOffset,reference.stdout.byteOffset+reference.stdout.byteLength));
  const output=await pcm(await enhanceAudioFile(file));assert.equal(output.length,expected.length);
  for(let i=0;i<output.length;i++)assert.ok(Math.abs(output[i]/32768-expected[i]*2)<2/32768);
});
