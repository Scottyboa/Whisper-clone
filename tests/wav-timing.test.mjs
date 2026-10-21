import test from 'node:test';
import assert from 'node:assert/strict';
import vm from 'node:vm';
import { readFileSync } from 'node:fs';
import { wavBlob, VAD_RULES } from '../js/audio.mjs';
import { prepareAudio, clockAt, clockLabel, validateTiming } from '../js/wav-timing.mjs';
import { CaptureTiming } from '../js/capture-timing.mjs';
import { Recorder } from '../js/recorder.mjs';
import { createDrainableSonioxVAD } from '../js/soniox-vad-drain.mjs';
import { renderTranscript, transcribeFile } from '../js/soniox.mjs';

const epoch=Date.parse('2026-10-15T14:33:00Z');
const timeline={version:1,sampleRate:16000,timeZone:'Europe/Oslo',segments:[[0,16000,epoch],[16000,16000,epoch+240000]]};
const pcm=[new Int16Array(16000).fill(123),new Int16Array(16000).fill(-456)];
const asFile=blob=>new File([blob],'recording.wav',{type:'audio/wav'});
const tokens=[{text:'Hello.',speaker:1,start_ms:500},{text:' Hi.',speaker:2,start_ms:1000}];

test('WAV metadata round-trips; provider audio is byte-identical to the old WAV format', async()=>{
  const ordinary=wavBlob(pcm),timed=wavBlob(pcm,timeline);
  const prepared=await prepareAudio(asFile(timed));
  assert.deepEqual(prepared.timing,timeline);
  assert.deepEqual(new Uint8Array(await prepared.file.arrayBuffer()),new Uint8Array(await ordinary.arrayBuffer()));
  assert.equal(new DataView(await timed.slice(0,8).arrayBuffer()).getUint32(4,true),timed.size-8);
  assert.equal(timed.size%2,0);assert.ok(timed.size>ordinary.size);
});

test('legacy WAVs, non-WAV audio and unreadable metadata fall back without throwing',async()=>{
  for(const file of [asFile(wavBlob(pcm)),new File(['mp3 data'],'legacy.mp3'),{size:100,slice(){throw new Error('read failure');}}]) {
    const result=await prepareAudio(file);assert.equal(result.file,file);assert.equal(result.timing,null);
  }
  assert.equal(renderTranscript({tokens},true),'Speaker 1: Hello.\n\nSpeaker 2: Hi.');
});

async function invalidMetadata(body) {
  const raw=wavBlob(pcm),bytes=new TextEncoder().encode(body),chunk=new Uint8Array(8+bytes.length+bytes.length%2);
  chunk.set(new TextEncoder().encode('wctm'));new DataView(chunk.buffer).setUint32(4,bytes.length,true);chunk.set(bytes,8);
  const prefix=new Uint8Array(await raw.slice(0,12).arrayBuffer());new DataView(prefix.buffer).setUint32(4,raw.size+chunk.length-8,true);
  return asFile(new Blob([prefix,raw.slice(12),chunk]));
}

test('invalid JSON/version/coverage/time zone is ignored and stripped from provider audio',async()=>{
  for(const body of ['bad json',JSON.stringify({...timeline,version:2}),JSON.stringify({...timeline,timeZone:'invalid/timezone'}),JSON.stringify({...timeline,segments:[[0,2,epoch]]})]) {
    const prepared=await prepareAudio(await invalidMetadata(body));assert.equal(prepared.timing,null);
    assert.equal(prepared.file.size,wavBlob(pcm).size);
    assert.equal(renderTranscript({tokens},true,prepared.timing),'Speaker 1: Hello.\n\nSpeaker 2: Hi.');
  }
});

test('malformed/truncated RIFF and impossible metadata never prevent transcription fallback',async()=>{
  const source=new Uint8Array(await wavBlob(pcm,timeline).arrayBuffer());
  const bad=source.slice();new DataView(bad.buffer).setUint32(16,0xffffffff,true);
  for(const bytes of [source.slice(0,-1),bad])assert.equal((await prepareAudio(asFile(new Blob([bytes])))).timing,null);
  for(const segments of [[[0,32001,epoch]],[[1,32000,epoch]],[[0,-1,epoch]],[[0,16000,epoch],[16000,16000,epoch-1000]],[[0,32000,Infinity]]])
    assert.equal(validateTiming({...timeline,segments},32000),null);
});

test('speaker-turn clocks restore silence gaps and retain recording timezone across computers',()=>{
  assert.equal(renderTranscript({tokens},true,timeline),'(16:33:00) Speaker 1: Hello.\n\n(16:37:00) Speaker 2: Hi.');
  assert.equal(clockAt(timeline,1000),epoch+240000);
  assert.equal(clockAt(timeline,2000),null);assert.equal(clockAt(timeline,-1),null);
  assert.equal(clockLabel(timeline,1000),'16:37:00');
  assert.equal(renderTranscript({tokens},false,timeline),'Hello. Hi.');
  assert.equal(renderTranscript({tokens:[{text:'No time',speaker:1}]},true,timeline),'Speaker 1: No time');
});

test('clock formatting handles midnight and daylight-saving transitions in the recording zone',()=>{
  const midnight={...timeline,segments:[[0,32000,Date.parse('2026-10-15T21:59:59Z')]]};
  assert.equal(clockLabel(midnight,1500),'00:00:00');
  const dst={...timeline,segments:[[0,32000,Date.parse('2026-10-25T00:59:59Z')]]};
  assert.equal(clockLabel(dst,1500),'02:00:00');
});

test('capture timeline extracts exact pre-padding/tail and preserves capture gaps',()=>{
  const timing=new CaptureTiming();
  timing.add(1536,epoch);timing.add(1536,epoch+96);timing.add(1536,epoch+10000);
  assert.deepEqual(timing.speech(4608),[[0,3072,epoch],[3072,1536,epoch+10000]]);
  timing.retain(1);assert.deepEqual(timing.speech(100),[[0,100,epoch+10000+(1536-100)/16]]);
  assert.equal(timing.speech(2000),null);timing.add(1536,NaN);assert.equal(timing.speech(1536),null);
});

function pinnedVAD() {
  const sandbox={self:{ort:{}},console};vm.runInNewContext(readFileSync(new URL('../vendor/vad/bundle.min.js',import.meta.url),'utf8'),sandbox);
  return sandbox.self.vad;
}

test('real pinned VAD maps captured frames despite inference delay, silence, pause/resume and final drain',async()=>{
  const vad=pinnedVAD(),original=globalThis.AudioWorkletNode;let capture,now=epoch;
  class Worklet {
    constructor(){capture=this;this.port={postMessage:msg=>{if(msg.message==='SONIOX_DRAIN')this.port.onmessage({data:{message:'SONIOX_DRAINED'}});}};}
    disconnect(){}
  }
  globalThis.AudioWorkletNode=Worklet;
  const context={currentTime:0,audioWorklet:{addModule:async()=>{}}};
  const recorder=new Recorder({now:()=>now,createVAD:async options=>{
    const factory={new:async opts=>{
      const processor=new vad.FrameProcessor(async frame=>({isSpeech:frame[0]}),()=>{},VAD_RULES);
      const node=new vad.AudioNodeVAD(context,opts,processor);node.audioNode={port:{postMessage(){}},disconnect(){}};
      return {audioContext:context,audioNodeVAD:node,sourceNode:{connect(){},disconnect(){}},stream:{getTracks:()=>[{stop(){}}]},destroy(){},start:()=>node.start(),pause:()=>node.pause()};
    }};
    const mic=await createDrainableSonioxVAD(factory,options);mic.start();return mic;
  }});
  let frame=0;
  const send=(count,prob)=>{for(let i=0;i<count;i++,frame++){const data=new Float32Array(1536).fill(prob);capture.port.onmessage({data:{message:'AUDIO_FRAME',data:data.buffer,audioTime:frame*0.096}});}};
  try {
    await recorder.command('start');send(100,0);assert.equal(recorder.lastSoundAt,null);
    send(4,1);send(5,0);assert.equal(recorder.lastSoundAt,epoch);
    // Processing these queued frames later must not timestamp them five minutes late.
    now+=300000;await recorder.command('pause');assert.equal(recorder.lastSoundAt,epoch);
    now+=300000;frame=0;await recorder.command('resume');send(50,0);assert.equal(recorder.lastSoundAt,epoch);
    send(3,1);assert.equal(recorder.lastSoundAt,now);
    const {blob,entry}=await recorder.command('stop');const prepared=await prepareAudio(asFile(blob));
    assert.ok(prepared.timing);assert.equal(entry.audioMs,(11+5)*96);
    assert.equal(clockAt(prepared.timing,192),epoch+9600);
    // Pause/resume gap survives, though all silence was removed from the WAV.
    assert.equal(clockAt(prepared.timing,11*96+192),epoch+600000+4800);
    assert.equal(prepared.file.size,44+(11+5)*1536*2);
    assert.equal(recorder.lastSoundAt,now);
  }finally{globalThis.AudioWorkletNode=original;}
});

test('capture worklet attaches audio-clock timestamps, including its padded partial final frame',()=>{
  let Capture;const posted=[];
  const sandbox={AudioWorkletProcessor:class{constructor(){this.port={postMessage:msg=>posted.push(msg)}}},sampleRate:48000,currentTime:10,registerProcessor:(_name,value)=>{Capture=value;}};
  vm.runInNewContext(readFileSync(new URL('../js/soniox-vad-worklet.js',import.meta.url),'utf8'),sandbox);
  const capture=new Capture({processorOptions:{frameSamples:1536}});
  for(let i=0;i<37;i++){sandbox.currentTime=10+i*128/48000;capture.process([[new Float32Array(128).fill(0.25)]]);}
  capture.port.onmessage({data:{message:'SONIOX_DRAIN'}});
  const frames=posted.filter(x=>x.message==='AUDIO_FRAME');assert.equal(frames.length,2);
  assert.equal(frames[0].audioTime,10);assert.ok(Math.abs(frames[1].audioTime-10.096)<1e-8);
  assert.equal(new Float32Array(frames[0].data)[0],0.25);assert.equal(posted.at(-1).message,'SONIOX_DRAINED');
});

test('Soniox receives ordinary PCM, while output uses the downloaded WAV timing map',async()=>{
  const original=globalThis.fetch;let uploaded;
  globalThis.fetch=async(url,opts={})=>{
    let body={};
    if(url.endsWith('/files')&&opts.method==='POST'){uploaded=opts.body.get('file');body={id:'file'};}
    else if(url.endsWith('/transcriptions')&&opts.method==='POST')body={id:'job'};
    else if(url.endsWith('/transcript'))body={tokens};
    else if(opts.method!=='DELETE')body={status:'completed'};
    return new Response(JSON.stringify(body));
  };
  try {
    assert.equal(await transcribeFile(asFile(wavBlob(pcm,timeline)),'test-key',true),'(16:33:00) Speaker 1: Hello.\n\n(16:37:00) Speaker 2: Hi.');
    assert.equal(uploaded.size,wavBlob(pcm).size);
    assert.equal((await prepareAudio(uploaded)).timing,null);
    assert.equal(await transcribeFile(asFile(wavBlob(pcm)),'test-key',true),'Speaker 1: Hello.\n\nSpeaker 2: Hi.');
  }finally{globalThis.fetch=original;}
});

test('ScriptProcessor fallback timestamps real captured buffers and flushes the partial tail',async()=>{
  const vad=pinnedVAD();let mic,now=epoch;
  const size=4096,rate=48000,seconds=size/rate;
  const context={currentTime:0,sampleRate:rate,destination:{},suspend:async()=>{},
    createScriptProcessor:()=>({connect(){},disconnect(){}}),createGain:()=>({gain:{},connect(){},disconnect(){}})};
  const recorder=new Recorder({now:()=>now,createVAD:async options=>{
    mic=await createDrainableSonioxVAD({new:async opts=>{
      const processor=new vad.FrameProcessor(async frame=>({isSpeech:frame[0]}),()=>{},VAD_RULES);
      const node=new vad.AudioNodeVAD(context,opts,processor);await node.setupAudioNode();
      return {audioContext:context,audioNodeVAD:node,sourceNode:{disconnect(){}},stream:{getTracks:()=>[{stop(){}}]},destroy(){},start:()=>node.start(),pause:()=>node.pause()};
    }},options);mic.start();return mic;
  }});
  await recorder.command('start');
  assert.equal(recorder.lastSoundAt,null);
  for(let i=0;i<100;i++){
    context.currentTime=(i+1)*seconds;
    mic.audioNodeVAD.audioNode.onaudioprocess({inputBuffer:{duration:seconds,getChannelData:()=>new Float32Array(size).fill(i<90?0:1)},outputBuffer:{getChannelData:()=>new Float32Array(size)}});
    assert.equal(recorder.lastSoundAt,i<90?null:epoch,'observe each native buffer before inference');
    await new Promise(resolve=>setImmediate(resolve));
  }
  now+=100000;
  const {blob}=await recorder.command('stop'),prepared=await prepareAudio(asFile(blob));
  assert.equal(recorder.lastSoundAt,epoch,'final resampler padding does not refresh the sound clock');
  assert.ok(prepared.timing);
  // First retained pre-speech padding is near the actual 7.68s speech onset,
  // never near the delayed Stop callback at 100 seconds.
  assert.ok(prepared.timing.segments[0][2]>epoch+7000);
  assert.ok(prepared.timing.segments[0][2]<epoch+8000);
  assert.equal(prepared.file.size,44+prepared.timing.segments.reduce((n,s)=>n+s[1],0)*2);
});
