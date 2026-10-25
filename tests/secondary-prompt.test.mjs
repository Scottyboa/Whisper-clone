import test from 'node:test';
import assert from 'node:assert/strict';
import { createSecondaryPrompt } from '../js/secondary-prompt.mjs';
function element() {
  return {checked:false,textContent:'',open:false,listeners:new Map(),classList:{toggle(){}},
    addEventListener(type,fn){this.listeners.set(type,fn);},fire(type,event){return this.listeners.get(type)?.(event);},
    showModal(){assert.equal(this.open,false);this.open=true;},close(){this.open=false;this.fire('close');},focus(){}};
}
function setup() {
  const nodes=Object.fromEntries(['dialog','summary','transcribe','download','apply','cancel','close'].map(name=>[name,element()]));
  return {...nodes,prompt:createSecondaryPrompt(nodes)};
}
test('Secondary rec defaults to VAD plus WAV download plus transcription and returns one chosen mode',async()=>{
  const h=setup(),pending=h.prompt('3 selected files');
  assert.equal(h.dialog.open,true);assert.equal(h.summary.textContent,'3 selected files');
  assert.equal(h.transcribe.checked,false);assert.equal(h.download.checked,true);assert.equal(h.apply.textContent,'Merge and transcribe');
  h.apply.fire('click');assert.deepEqual(await pending,{download:true});assert.equal(h.dialog.open,false);
  const next=h.prompt('Next batch');h.transcribe.checked=true;h.transcribe.fire('change');
  assert.equal(h.download.checked,false);h.apply.fire('click');assert.deepEqual(await next,{download:false});
});
test('checkboxes remain mutually exclusive and no selected mode turns the action into Exit',async()=>{
  const h=setup(),pending=h.prompt('Files');
  h.transcribe.checked=true;h.transcribe.fire('change');assert.equal(h.download.checked,false);
  h.download.checked=true;h.download.fire('change');assert.equal(h.transcribe.checked,false);
  h.download.checked=false;h.download.fire('change');assert.equal(h.apply.textContent,'Exit');
  h.apply.fire('click');assert.equal(await pending,null);
});
test('Cancel, close, Escape and page disposal resolve without work and reopening restores the default',async()=>{
  for(const action of ['cancel','close','escape','dispose','native-close']){
    const h=setup(),pending=h.prompt('Files');h.transcribe.checked=true;h.transcribe.fire('change');
    if(action==='escape'){let prevented=false;h.dialog.fire('cancel',{preventDefault(){prevented=true;}});assert.equal(prevented,true);}
    else if(action==='dispose')h.prompt.cancel();
    else if(action==='native-close')h.dialog.close();
    else h[action].fire('click');
    assert.equal(await pending,null);assert.equal(h.dialog.open,false);
    const reopened=h.prompt('Again');assert.equal(h.transcribe.checked,false);assert.equal(h.download.checked,true);h.cancel.fire('click');await reopened;
  }
});
test('a duplicate prompt does not replace the pending selection or start a second operation',async()=>{
  const h=setup(),first=h.prompt('First');assert.equal(await h.prompt('Second'),null);assert.equal(h.summary.textContent,'First');
  h.apply.fire('click');assert.deepEqual(await first,{download:true});
});

test('a late close event from the previous prompt cannot cancel a newly opened prompt',async()=>{
  const h=setup(),first=h.prompt('First');h.apply.fire('click');await first;
  const second=h.prompt('Second');h.dialog.fire('close');
  assert.equal(h.dialog.open,true);h.transcribe.checked=true;h.transcribe.fire('change');h.apply.fire('click');
  assert.deepEqual(await second,{download:false});
});
