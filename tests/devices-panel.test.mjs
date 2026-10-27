import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { DevicesPanel, createAbortPrompt } from '../js/devices-panel.mjs';
import { RECENT_MS, PRESENCE_TTL } from '../js/device-control.mjs';
function element(){return {
  textContent:'',value:'',disabled:false,hidden:false,open:false,children:[],listeners:{},attributes:{},classList:{add(){},remove(){},toggle(){}},
  addEventListener(type,fn){(this.listeners[type]||=[]).push(fn);},
  async fire(type,event={}){for(const fn of this.listeners[type]||[])await fn(event);},
  append(...nodes){for(const node of nodes){node.parent=this;this.children.push(node);}},
  remove(){if(this.parent)this.parent.children=this.parent.children.filter(node=>node!==this);this.parent=null;},
  replaceChildren(){this.children=[];},setAttribute(key,value){this.attributes[key]=value;},
  showModal(){this.open=true;},close(){this.open=false;this.fire('close');},focus(){this.focused=true;},
};}
function setup({confirmAbort=async()=>true}={}){
  const elements=new Map(),$=id=>{if(!elements.has(id))elements.set(id,element());return elements.get(id);};
  const original=globalThis.document;globalThis.document={createElement:element};
  const rows=[{sessionId:'00000000-0000-4000-8000-111111111111',name:'Work',local:true,state:'idle',audioReady:true,at:1000},
    {sessionId:'00000000-0000-4000-8000-222222222222',name:'Home',local:false,state:'recording',audioReady:true,at:1000}];
  const sent=[],devices={name:'Work',active:true,status:'Connected',rows,pending:new Map(),setName(name){this.name=name;},
    disconnect(){this.active=false;},async refresh(){return this.rows;},async send(target,action){sent.push({target,action});}};
  const panel=new DevicesPanel({devices,$,now:()=>2000,connect:async()=>{devices.active=true;},confirmAbort});
  return {$,panel,devices,sent,restore(){panel.dispose();globalThis.document=original;}};
}

test('Devices panel IDs exist in the real HTML; opening/closing the panel does not disconnect a tab',async()=>{
  const h=setup();try{
    await h.$('devices').fire('click');assert.equal(h.$('devicesDialog').open,true);
    await h.$('devicesClose').fire('click');assert.equal(h.$('devicesDialog').open,false);assert.equal(h.devices.active,true);
    const html=readFileSync(new URL('../index.html',import.meta.url),'utf8');
    for(const id of ['devices','devicesDialog','devicesName','devicesStatus','devicesSummary','deviceRows','devicesConnect','devicesDisconnect','devicesRefresh','devicesEmpty','devicesMessage','devicesResults','device-start','device-pause','device-resume','device-stop','device-stop-and-transcribe','device-abort'])assert.ok(html.includes(`id="${id}"`),id);
    assert.ok(html.indexOf('id="abort"')>html.indexOf('id="stop"'));
  }finally{h.restore();}
});

test('selecting a row enables appropriate controls and only sends to that selected tab',async()=>{
  const h=setup();try{
    assert.equal(h.$('device-stop').disabled,true);
    const homeButton=h.$('deviceRows').children[1].children[0].children[0];await homeButton.fire('click');
    assert.equal(h.$('device-stop').disabled,false);assert.equal(h.$('device-start').disabled,true);
    await h.$('device-stop').fire('click');assert.deepEqual(h.sent,[{target:h.devices.rows[1].sessionId,action:'stop'}]);assert.equal(h.devices.active,true);
    h.devices.rows[1].at=-PRESENCE_TTL;h.panel.render();assert.equal(h.$('device-abort').disabled,true);
  }finally{h.restore();}
});

test('Devices shows local and remote sound clocks, elapsed age, no-sound and unsupported states',()=>{
  const h=setup();try{
    let now=new Date(2026,9,21,16,3,20).getTime();h.panel.now=()=>now;
    const [work,home]=h.devices.rows;
    Object.assign(work,{at:now,inputActivityVersion:1,lastSoundAt:null});
    Object.assign(home,{at:now,inputActivityVersion:1,lastSoundAt:now-8000});
    const sound=index=>h.$('deviceRows').children[index].children[2].textContent;
    h.panel.render();assert.equal(sound(0),'No sound detected yet');assert.equal(sound(1),'16:03:12 · 8s ago');
    now+=1000;h.panel.render();assert.equal(sound(1),'16:03:12 · 9s ago');
    delete home.inputActivityVersion;h.panel.render();assert.equal(sound(1),'Sound activity unavailable');
    home.inputActivityVersion=2;h.panel.render();assert.equal(sound(1),'Sound activity unavailable');
    const html=readFileSync(new URL('../index.html',import.meta.url),'utf8');
    const [outside,devices]=html.split('<dialog id="devicesDialog"');
    assert.equal(outside.includes('Last sound detected'),false);
    assert.match(devices,/<th>Last sound detected<\/th>/);
  }finally{h.restore();}
});

test('delayed tabs remain selectable for two minutes and expired tabs lose their command controls',async()=>{
  const h=setup();try{
    const home=h.devices.rows[1],seen=home.at;h.panel.selected=home.sessionId;
    h.panel.now=()=>seen+RECENT_MS;h.panel.render();
    assert.equal(h.$('deviceRows').children.length,2);assert.equal(h.$('device-stop').disabled,false);
    assert.match(h.$('deviceRows').children[1].children[1].textContent,/Updates delayed · Last reported: Recording/);
    assert.equal(h.panel.selected,home.sessionId);
    await h.panel.command('stop');assert.equal(h.sent[0].target,home.sessionId);
    h.panel.now=()=>seen+PRESENCE_TTL-1;h.panel.render();
    assert.equal(h.$('deviceRows').children.length,2);assert.equal(h.$('device-stop').disabled,false);
    h.panel.now=()=>seen+PRESENCE_TTL;h.panel.render();
    assert.equal(h.$('deviceRows').children.length,0);assert.equal(h.panel.selected,null);
    assert.equal(h.$('devicesEmpty').hidden,false);assert.equal(h.$('device-stop').disabled,true);
    assert.equal(h.devices.active,true);assert.equal(h.$('devicesDisconnect').disabled,false);
    home.at=h.panel.now();h.panel.render();assert.equal(h.$('deviceRows').children.length,1);
  }finally{h.restore();}
});

test('timer and status renders preserve row buttons, focus and selection across delayed updates',async()=>{
  const h=setup();try{
    const home=h.devices.rows[1],seen=home.at,tr=h.$('deviceRows').children[1],button=tr.children[0].children[0];
    button.focus();await button.fire('click');
    for(const age of [2000,10000,RECENT_MS,60000]){
      h.panel.now=()=>seen+age;h.panel.render();
      assert.equal(h.$('deviceRows').children[1],tr);assert.equal(tr.children[0].children[0],button);
      assert.equal(button.focused,true);assert.equal(button.attributes['aria-pressed'],'true');
      assert.equal(h.panel.selected,home.sessionId);
    }
    // A heartbeat clears the delayed label without replacing any clickable nodes.
    home.at=h.panel.now();home.state='paused';h.panel.render();
    assert.equal(tr.children[1].textContent,'Paused');assert.equal(h.$('device-resume').disabled,false);
    assert.equal(tr.children[0].children[0],button);
    await button.fire('click');await h.$('device-resume').fire('click');
    assert.deepEqual(h.sent,[{target:home.sessionId,action:'resume'}]);
  }finally{h.restore();}
});

test('Abort cancellation sends nothing; a confirmation keeps its original selected target',async()=>{
  const h=setup({confirmAbort:async()=>false});try{
    h.panel.selected=h.devices.rows[1].sessionId;await h.panel.command('abort');assert.equal(h.sent.length,0);
    let resolve;h.panel.confirmAbort=()=>new Promise(r=>resolve=r);
    const task=h.panel.command('abort');h.panel.selected=h.devices.rows[0].sessionId;resolve(true);await task;
    assert.deepEqual(h.sent,[{target:h.devices.rows[1].sessionId,action:'abort'}]);
  }finally{h.restore();}
});

test('urgent Abort stays enabled while Start is awaiting acknowledgement',()=>{
  const h=setup();try{
    const row=h.devices.rows[1];row.state='starting';h.panel.selected=row.sessionId;
    h.devices.pending.set('pending',{target:row.sessionId,action:'start',expiresAt:60000});h.panel.render();
    assert.equal(h.$('device-abort').disabled,false);assert.equal(h.$('device-start').disabled,true);
  }finally{h.restore();}
});

test('confirmation resolves Yes, No, Escape and close without running a recording command',async()=>{
  const dialog=element(),text=element(),yes=element(),no=element(),ask=createAbortPrompt({dialog,text,yes,no});
  const first=ask();assert.equal(dialog.open,true);assert.equal(no.focused,true);await no.fire('click');assert.equal(await first,false);
  const second=ask('Home PC');assert.match(text.textContent,/Home PC/);await yes.fire('click');assert.equal(await second,true);
  const third=ask();await dialog.fire('cancel',{preventDefault(){}});assert.equal(await third,false);
  const fourth=ask();dialog.close();assert.equal(await fourth,false);
});

