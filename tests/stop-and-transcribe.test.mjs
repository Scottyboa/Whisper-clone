import test from 'node:test';
import assert from 'node:assert/strict';
import vm from 'node:vm';
import { readFileSync } from 'node:fs';
import { Recorder as RealRecorder } from '../js/recorder.mjs';
import { parseCommand, MailControl } from '../js/graph.mjs';
import { transcribeFile as realTranscribe } from '../js/soniox.mjs';
import * as audio from '../js/audio.mjs';

const account = { homeAccountId: 'recording-account' };
const tick = () => new Promise(resolve => setImmediate(resolve));
const deferred = () => { let resolve, reject; const promise = new Promise((a,b) => { resolve=a; reject=b; }); return {promise,resolve,reject}; };
const app = readFileSync(new URL('../js/app.mjs', import.meta.url), 'utf8').replace(/^import .*;\n/gm, '');
function harness({ key = 'soniox-key', speech = true, timed = false, transcribe, upload, onCapture, onDrain, downloadError = false } = {}) {
  const elements = new Map(), downloads = [], transcriptions = [], uploads = [], commands = [], captures = [];
  const makeElement = () => ({
    value: '', checked: false, disabled: false, textContent: '', children: [], listeners: new Map(),
    classList: { toggle() {}, add() {}, remove() {} },
    addEventListener(name, fn) { this.listeners.set(name, fn); },
    append(...nodes) { this.children.push(...nodes); }, replaceChildren() { this.children=[]; },
  });
  const el = id => { if (!elements.has(id)) elements.set(id,makeElement()); return elements.get(id); };
  let mail, recorder, now = new Date(2026,9,15,10,0).getTime();
  class Recorder extends RealRecorder {
    constructor(options) {
      super({ ...options, now: () => now, createVAD: async callbacks => {
        const index=captures.push(callbacks);await onCapture?.(index);
        return { drainAndPause: async () => {
          await onDrain?.(index);
          if (speech) callbacks.onSpeechEnd(new Float32Array(16000).fill(index*0.1), timed ? [[0,16000,now]] : null);
        }, destroy() {} };
      } }); recorder=this;
    }
    command(action) { commands.push(action); return super.command(action); }
  }
  class Mail {
    constructor(options) { Object.assign(this,options); this.account=account; this.active=true; mail=this; }
    async client() { return {}; } unlink() { this.active=false; }
  }
  class Drive {
    async upload(text, options) { uploads.push({text, options}); return upload ? upload(text,options) : options?.name || 'manual.txt'; }
    async clear(confirm) { return {count:0,cancelled:false}; }
  }
  const context = vm.createContext({
    ...audio, download: (blob,name) => { downloads.push({blob,name}); if(downloadError)throw new Error('download blocked'); }, Recorder, MailControl: Mail, TranscriptDrive: Drive,
    PrivacyView: class {}, File,
    transcribeFile: async (...args) => { transcriptions.push(args); return transcribe ? transcribe(...args) : 'Speaker 1: Hello\n\nSpeaker 2: Hi'; },
    sessionStorage: {getItem: name => name.endsWith('soniox-key') ? key : null, setItem() {}, removeItem() {}},
    document: {getElementById:el,querySelector:makeElement,createElement:makeElement,createTextNode:text=>({text}),addEventListener() {}},
    window: {opener:null,addEventListener() {}}, location: {}, navigator: {}, setInterval() {}, confirm:()=>true,
  });
  vm.runInContext(app,context);
  return { el, downloads, transcriptions, uploads, commands, captures, recorder, mail, advance: ms => {now+=ms;} };
}
const commandMail = (overrides={}) => ({id:'command-id', subject:'', body:{contentType:'text',content:'stop and transcribe'},
  from:{emailAddress:{address:'self@example.com'}}, sender:{emailAddress:{address:'self@example.com'}},
  toRecipients:[{emailAddress:{address:'self@example.com'}}], receivedDateTime:'2026-10-15T08:00:00Z', ...overrides});
const parse = message => parseCommand(message,new Set(['self@example.com']),Date.parse('2026-10-15T07:59:00Z'),Date.parse('2026-10-15T08:00:10Z'));

test('new exact command accepts whitespace/case and preserves self-sender, blank-subject and age checks', () => {
  assert.equal(parse(commandMail()),'stop-and-transcribe');
  assert.equal(parse(commandMail({body:{content:' STOP  AND\nTRANSCRIBE '}})),'stop-and-transcribe');
  for (const changes of [{subject:'anything'}, {from:{emailAddress:{address:'other@example.com'}}},
    {sender:{emailAddress:{address:'other@example.com'}}}, {toRecipients:[]},
    {receivedDateTime:'2026-10-15T07:50:00Z'}, {body:{content:'please stop and transcribe'}}]) {
    assert.equal(parse(commandMail(changes)),null);
  }
  for (const action of ['start','pause','resume','stop']) assert.equal(parse(commandMail({body:{content:`${action} recording`}})),action);
});

test('Link requests email and app-folder consent together', async () => {
  let options;
  const mail = new MailControl({auth:{loginPopup:async o=>{options=o;return {account,accessToken:'token'};}},
    fetcher:async()=>new Response(JSON.stringify({mail:'self@example.com',id:'me'}))});
  // Stop after validating login options; no polling or browser lock required.
  mail.request = async () => { mail.generation++; return {}; };
  await mail.link();
  assert.deepEqual(options.scopes,['User.Read','Mail.Read','Files.ReadWrite.AppFolder']);
});

test('remote Stop drains the actual recorder, downloads its WAV and uploads speaker text with its metadata', async () => {
  const h=harness();
  await h.mail.onCommand('start'); h.advance(3600000);
  await h.mail.onCommand('stop-and-transcribe'); await tick();
  assert.equal(h.recorder.state,'recording'); assert.equal(h.downloads.length,1);
  const [source,key,speakers]=h.transcriptions[0];
  assert.equal(key,'soniox-key'); assert.equal(speakers,true); assert.equal(h.el('speakers').checked,false);
  assert.equal(source.type,'audio/wav'); assert.equal(source.size,32044);
  assert.deepEqual(new Uint8Array(await source.arrayBuffer()),new Uint8Array(await h.downloads[0].blob.arrayBuffer()));
  assert.equal(h.uploads[0].text,'Speaker 1: Hello\n\nSpeaker 2: Hi');
  assert.equal(h.uploads[0].options.name,'2026-10-15_10-00-00-000_to_2026-10-15_11-00-00-000_VAD-0m1s.txt');
  assert.equal(h.uploads[0].options.interactive,false); assert.equal(h.uploads[0].options.account,account);
  assert.equal(h.el('history').children.length,1);
});

test('mail stays responsive and consecutive recordings retain separate audio, intervals and text', async () => {
  const gate=deferred(); let n=0;
  const h=harness({transcribe:async()=> ++n===1 ? gate.promise : 'second transcript'});
  await h.mail.onCommand('start'); h.advance(10000); await h.mail.onCommand('stop-and-transcribe');
  assert.equal(h.transcriptions.length,1); assert.equal(h.uploads.length,0);
  assert.equal(h.recorder.state,'recording'); assert.equal(h.captures.length,2);
  h.advance(20000); await h.mail.onCommand('stop-and-transcribe');
  assert.equal(h.downloads.length,2); assert.equal(h.transcriptions.length,1);
  gate.resolve('first transcript'); await tick();
  assert.deepEqual(h.uploads.map(x=>x.text),['first transcript','second transcript']);
  assert.match(h.uploads[0].options.name,/10-00-00-000_to_2026-10-15_10-00-10-000/);
  assert.match(h.uploads[1].options.name,/10-00-10-000_to_2026-10-15_10-00-30-000/);
  assert.equal(h.el('transcribe').disabled,false);
});

test('manual transcription shares the queue; plain Stop never transcribes or uploads', async () => {
  const h=harness(); const selected=new File(['manual'],'manual.wav');
  h.el('file').files=[selected]; h.el('file').listeners.get('change')();
  h.el('speakers').checked=false; h.el('transcribe').listeners.get('click')(); await tick();
  assert.equal(h.transcriptions[0][0],selected); assert.equal(h.transcriptions[0][2],false); assert.equal(h.uploads.length,0);
  await h.mail.onCommand('start'); await h.mail.onCommand('stop'); await tick();
  assert.equal(h.downloads.length,1); assert.equal(h.transcriptions.length,1); assert.equal(h.uploads.length,0); assert.equal(h.recorder.state,'idle');
});

test('idle is ignored; silent recordings and missing keys still rotate without stale transcription', async () => {
  const idle=harness(); await idle.mail.onCommand('stop-and-transcribe'); assert.equal(idle.transcriptions.length,0); assert.equal(idle.captures.length,0);
  const quiet=harness({speech:false}); await quiet.mail.onCommand('start'); await quiet.mail.onCommand('stop-and-transcribe');
  assert.equal(quiet.downloads.length,0); assert.equal(quiet.transcriptions.length,0); assert.equal(quiet.recorder.state,'recording'); assert.equal(quiet.captures.length,2);
  const missing=harness({key:''}); await missing.mail.onCommand('start');
  await assert.rejects(missing.mail.onCommand('stop-and-transcribe'),/needs a Soniox API key/);
  assert.equal(missing.recorder.state,'recording'); assert.equal(missing.downloads.length,1); assert.equal(missing.transcriptions.length,0);
});

test('provider and upload failures preserve retry data and allow subsequent jobs', async () => {
  let fail=true;
  const h=harness({transcribe:async()=>{if(fail)throw new Error('provider down');return 'retained text';},upload:async()=>{throw new Error('Drive offline');}});
  await h.mail.onCommand('start'); await h.mail.onCommand('stop-and-transcribe'); await tick();
  assert.match(h.el('message').textContent,/provider down/); assert.equal(h.uploads.length,0); assert.equal(h.el('transcribe').disabled,false);
  fail=false; h.el('transcribe').listeners.get('click')(); await tick(); assert.equal(h.el('transcript').value,'retained text');
  await h.mail.onCommand('start'); await h.mail.onCommand('stop-and-transcribe'); await tick();
  assert.equal(h.el('transcript').value,'retained text'); assert.match(h.el('driveMessage').textContent,/EX.Drive to retry/);
  assert.equal(h.el('exportDrive').disabled,false); assert.equal(h.recorder.state,'recording');
});

test('filename contains both dates across midnight and the retained audio duration', () => {
  assert.equal(audio.recordingTranscriptName({startedAt:new Date(2026,9,15,23,59,59,123).getTime(),endedAt:new Date(2026,9,16,1,0,0,456).getTime(),audioMs:1425000}),
    '2026-10-15_23-59-59-123_to_2026-10-16_01-00-00-456_VAD-23m45s.txt');
});

test('real Soniox request enables diarization, renders speakers and deletes provider resources', async () => {
  const original=globalThis.fetch, calls=[];
  globalThis.fetch=async(url,options={})=>{
    calls.push({url,options});
    const path=new URL(url).pathname;
    const body= options.method==='DELETE'?{} : path.endsWith('/files')?{id:'file-1'}:
      options.method==='POST'?{id:'job-1'}:path.endsWith('/transcript')?{tokens:[{text:'Hello',speaker:1},{text:'Hi',speaker:2}]}:{status:'completed'};
    return new Response(JSON.stringify(body));
  };
  try {
    const result=await realTranscribe(new File(['wav'],'recording.wav'),'secret',true);
    assert.equal(result,'Speaker 1: Hello\n\nSpeaker 2: Hi');
    assert.equal(JSON.parse(calls.find(c=>c.url.endsWith('/transcriptions')&&c.options.method==='POST').options.body).enable_speaker_diarization,true);
    assert.equal(calls.filter(c=>c.options.method==='DELETE').length,2);
  } finally {globalThis.fetch=original;}
});

test('real mailbox polling processes later commands during transcription and deduplicates the stop email', async () => {
  const gate=deferred(), h=harness({transcribe:()=>gate.promise});
  await h.mail.onCommand('start');
  const now=Date.parse('2026-10-15T08:00:10Z');
  const mail=new MailControl({now:()=>now,onCommand:h.mail.onCommand,auth:{acquireTokenSilent:async()=>({accessToken:'token'})},
    fetcher:async()=>new Response(JSON.stringify({value:[commandMail(),commandMail({id:'next',receivedDateTime:'2026-10-15T08:00:01Z',body:{content:'start recording'}})]}))});
  mail.active=true;mail.account=account;mail.addresses=new Set(['self@example.com']);mail.linkedAt=now-60000;mail.schedule=()=>{};
  await mail.poll(); assert.equal(h.downloads.length,1);assert.equal(h.recorder.state,'recording');
  await mail.poll(); assert.equal(h.downloads.length,1);assert.equal(h.transcriptions.length,1);
  gate.resolve('done');await tick();assert.equal(h.uploads.length,1);
});

test('automatic workflow uploads real clock-stamped output and preserves the same timing map in its WAV download',async()=>{
  const original=globalThis.fetch;
  globalThis.fetch=async(url,opts={})=>new Response(JSON.stringify(opts.method==='DELETE'?{}:
    url.endsWith('/files')?{id:'file'}:opts.method==='POST'?{id:'job'}:
    url.endsWith('/transcript')?{tokens:[{text:'Clock-stamped text',speaker:1,start_ms:0}]}:{status:'completed'}));
  try {
    const h=harness({timed:true,transcribe:realTranscribe});
    await h.mail.onCommand('start');h.advance(10000);await h.mail.onCommand('stop-and-transcribe');
    for(let i=0;i<30&&!h.uploads.length;i++)await tick();
    assert.match(h.uploads[0].text,/^\(10:00:10\) Speaker 1: Clock-stamped text$/);
    assert.equal(h.el('transcript').value,h.uploads[0].text);
    const {prepareAudio}=await import('../js/wav-timing.mjs');
    const prepared=await prepareAudio(new File([h.downloads[0].blob],'saved.wav'));
    assert.ok(prepared.timing);assert.equal(prepared.file.size,32044);
  }finally{globalThis.fetch=original;}
});

test('fresh recording starts while transcription is pending; plain Stop is final even when the old job finishes later',async()=>{
  const gate=deferred(),h=harness({transcribe:()=>gate.promise});
  await h.mail.onCommand('start');const firstStart=h.recorder.startedAt;h.advance(10000);
  await h.mail.onCommand('stop-and-transcribe');
  assert.equal(h.recorder.state,'recording');assert.equal(h.recorder.startedAt,firstStart+10000);
  assert.equal(h.recorder.samples,0);assert.equal(h.recorder.parts.length,0);assert.equal(h.el('timer').textContent,'00:00:00');
  assert.equal(h.uploads.length,0);assert.equal(h.captures.length,2);
  h.advance(5000);await h.mail.onCommand('stop');assert.equal(h.recorder.state,'idle');
  gate.resolve('completed previous recording');await tick();
  assert.equal(h.recorder.state,'idle');assert.equal(h.captures.length,2);assert.equal(h.downloads.length,2);
  assert.equal(h.uploads.length,1);assert.equal(h.uploads[0].text,'completed previous recording');
  assert.match(h.uploads[0].options.name,/10-00-00-000_to_2026-10-15_10-00-10-000/);
  assert.notDeepEqual(new Uint8Array(await h.downloads[0].blob.arrayBuffer()),new Uint8Array(await h.downloads[1].blob.arrayBuffer()));
});

test('a newer explicit Stop during finalization cancels automatic restart',async()=>{
  const gate=deferred(),h=harness({onDrain:()=>gate.promise});
  await h.mail.onCommand('start');
  const automatic=h.mail.onCommand('stop-and-transcribe');await tick();assert.equal(h.recorder.state,'stopping');
  const stop=h.mail.onCommand('stop');gate.resolve();await Promise.all([automatic,stop]);await tick();
  assert.equal(h.recorder.state,'idle');assert.equal(h.captures.length,1);assert.equal(h.downloads.length,1);assert.equal(h.uploads.length,1);
});

test('a newer explicit Start during finalization starts only one new capture',async()=>{
  const gate=deferred(),h=harness({onDrain:()=>gate.promise});
  await h.mail.onCommand('start');
  const automatic=h.mail.onCommand('stop-and-transcribe');await tick();
  const start=h.mail.onCommand('start');gate.resolve();await Promise.all([automatic,start]);
  assert.equal(h.recorder.state,'recording');assert.equal(h.captures.length,2);
});

test('failed microphone restart keeps the old transcription job and reports the stopped capture visibly',async()=>{
  const provider=deferred(),h=harness({onCapture:index=>{if(index===2)throw new Error('Microphone unavailable');},transcribe:()=>provider.promise});
  await h.mail.onCommand('start');
  await assert.rejects(h.mail.onCommand('stop-and-transcribe'),/new recording could not start.*Microphone unavailable/);
  assert.equal(h.recorder.state,'idle');assert.equal(h.downloads.length,1);assert.equal(h.transcriptions.length,1);
  assert.equal(h.el('recordStatus').textContent,'Restart failed — click Start to retry');
  provider.resolve('saved despite restart failure');await tick();assert.equal(h.uploads.length,1);
  assert.equal(h.el('recordStatus').textContent,'Restart failed — click Start to retry');
  await h.mail.onCommand('start');assert.equal(h.recorder.state,'recording');assert.equal(h.captures.length,3);
});

test('failed VAD finalization never restarts or submits unfinished audio',async()=>{
  const h=harness({onDrain:()=>{throw new Error('drain failed');}});
  await h.mail.onCommand('start');await assert.rejects(h.mail.onCommand('stop-and-transcribe'),/drain failed/);
  assert.equal(h.recorder.state,'error');assert.equal(h.captures.length,1);assert.equal(h.downloads.length,0);assert.equal(h.transcriptions.length,0);
});

test('rotating a paused recording creates a fresh capture and a rejected download does not prevent processing',async()=>{
  const h=harness({downloadError:true});await h.mail.onCommand('start');await h.mail.onCommand('pause');
  assert.equal(h.recorder.state,'paused');h.advance(30000);await h.mail.onCommand('stop-and-transcribe');await tick();
  assert.equal(h.recorder.state,'recording');assert.equal(h.captures.length,2);assert.equal(h.transcriptions.length,1);assert.equal(h.uploads.length,1);
});

test('mailbox Stop after a rotating command stops the new recording and duplicate polling cannot restart it',async()=>{
  const gate=deferred(),h=harness({transcribe:()=>gate.promise});await h.mail.onCommand('start');
  const now=Date.parse('2026-10-15T08:00:10Z');
  const mail=new MailControl({now:()=>now,onCommand:h.mail.onCommand,auth:{acquireTokenSilent:async()=>({accessToken:'token'})},
    fetcher:async()=>new Response(JSON.stringify({value:[commandMail(),commandMail({id:'final-stop',receivedDateTime:'2026-10-15T08:00:01Z',body:{content:'stop recording'}})]}))});
  mail.active=true;mail.account=account;mail.addresses=new Set(['self@example.com']);mail.linkedAt=now-60000;mail.schedule=()=>{};
  await mail.poll();assert.equal(h.recorder.state,'idle');assert.equal(h.captures.length,2);assert.equal(h.downloads.length,2);
  await mail.poll();assert.equal(h.recorder.state,'idle');assert.equal(h.captures.length,2);
  gate.resolve('text');await tick();assert.equal(h.recorder.state,'idle');
});
