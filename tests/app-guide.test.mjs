import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { AppGuide } from '../js/app-guide.mjs';

const accessCode = String.fromCharCode(0x31);
function element() {
  return {value:'',disabled:false,open:false,listeners:new Map(),opens:0,
    addEventListener(type,fn){this.listeners.set(type,fn);},
    fire(type){return this.listeners.get(type)?.();},
    showModal(){assert.equal(this.open,false);this.open=true;this.opens++;},
    close(){this.open=false;this.fire('close');},focus(){this.focused=true;},
  };
}
function setup() {
  const dialog=element(),button=element(),code=element(),close=element();
  new AppGuide({dialog,button,code,close});return {dialog,button,code,close};
}

test('the always-enabled Guide button ignores blank, wrong and padded codes',async()=>{
  const h=setup();
  for(const value of ['', '0', '2', 'guide', accessCode+accessCode, ` ${accessCode}`, `${accessCode} `, String.fromCharCode(0xff11)]){
    h.code.value=value;await h.button.fire('click');
    assert.equal(h.dialog.open,false);assert.equal(h.dialog.opens,0);
    assert.equal(h.button.disabled,false);assert.equal(h.code.value,'');
  }
});

test('the matching code opens the guide; closing requires a fresh code next time',async()=>{
  const h=setup();h.code.value=accessCode;await h.button.fire('click');
  assert.equal(h.dialog.open,true);assert.equal(h.code.value,'');assert.equal(h.button.disabled,false);
  h.close.fire('click');assert.equal(h.dialog.open,false);assert.equal(h.button.focused,true);
  await h.button.fire('click');assert.equal(h.dialog.open,false);
  h.code.value=accessCode;await h.button.fire('click');assert.equal(h.dialog.open,true);
  // Native Escape dismissal dispatches the same close event.
  h.dialog.close();assert.equal(h.code.value,'');assert.equal(h.button.focused,true);
  await h.button.fire('click');assert.equal(h.dialog.open,false);
});

test('repeated clicks during the hash check open only one modal and keep the button enabled',async()=>{
  const h=setup();h.code.value=accessCode;const first=h.button.fire('click');
  h.code.value=accessCode;const second=h.button.fire('click');
  await Promise.all([first,second]);
  assert.equal(h.dialog.opens,1);assert.equal(h.dialog.open,true);assert.equal(h.button.disabled,false);
  h.code.value=accessCode;await h.button.fire('click');assert.equal(h.dialog.opens,1);
});

test('the real page has a labelled guide at the top and covers all existing controls',()=>{
  const html=readFileSync(new URL('../index.html',import.meta.url),'utf8');
  assert.match(html,/<button id="guide"[^>]*aria-controls="guideDialog"[^>]*>Guide<\/button>/);
  assert.doesNotMatch(html,/<button id="guide"[^>]*disabled/);
  assert.ok(html.indexOf('id="guide"')<html.indexOf('class="record-panel"'));
  assert.match(html,/<input id="guideCode"[^>]*aria-label="Guide code"/);
  assert.match(html,/<dialog id="guideDialog"[^>]*aria-labelledby="guideTitle"/);
  assert.match(html,/<button id="vadProcess"[^>]*>VAD processing<\/button>/);
  assert.ok(html.indexOf('id="vadProcess"')<html.indexOf('id="transcribe"'));
  assert.match(html,/<input id="secondaryFiles"[^>]*multiple/);
  const guide=html.slice(html.indexOf('<dialog id="guideDialog"'),html.indexOf('<dialog id="driveImportDialog"'));
  for(const text of ['Start','Pause / Resume','Stop','Abort','Keep awake','History','VAD processing','Secondary rec','stop and transcribe','abort recording','Link','Unlink','start','pause','resume','stop','Enable audio here','Disconnect','Refresh','Upload File','Transcribe','Speaker labels','Import Key','Clear','EX.Drive','Imp. Drive','Clear Drive','COMPLETE.txt','Privacy view'])assert.ok(guide.includes(text),text);
  assert.match(html,/<dialog id="secondaryDialog"[^>]*aria-labelledby="secondaryTitle"/);
  assert.match(html,/<input id="secondaryTranscribeOnly" type="checkbox"/);
  assert.match(html,/<input id="secondaryWithDownload" type="checkbox" checked/);
  assert.ok(guide.includes('VAD Silero + transcribe'));assert.ok(guide.includes('VAD Silero + WAV download + transcribe'));
  const ids=[...html.matchAll(/\bid="([^"]+)"/g)].map(match=>match[1]);
  assert.equal(new Set(ids).size,ids.length);
});
