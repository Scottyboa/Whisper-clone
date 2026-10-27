import { RECENT_MS, PRESENCE_TTL } from './device-control.mjs?v=20261027-devices1';
import { inputActivityLabel } from './input-activity.mjs?v=20261021-sound1';
const labels = {start:'Start',pause:'Pause',resume:'Resume',stop:'Stop','stop-and-transcribe':'Stop and transcribe',abort:'Abort'};
const stateLabels = {idle:'Ready',starting:'Starting…',recording:'Recording',pausing:'Pausing…',paused:'Paused',resuming:'Resuming…',stopping:'Finishing…',aborting:'Discarding…',error:'Audio error'};
const setText = (element, value) => { if (element.textContent !== value) element.textContent = value; };
export function createAbortPrompt({dialog, text, yes, no}) {
  let resolve = null;
  const finish = value => { const done=resolve;resolve=null;dialog.close();done?.(value); };
  yes.addEventListener('click',()=>finish(true));no.addEventListener('click',()=>finish(false));
  dialog.addEventListener('cancel',event=>{event.preventDefault();finish(false);});
  dialog.addEventListener('close',()=>{const done=resolve;resolve=null;done?.(false);});
  return name => {
    if (resolve) return Promise.resolve(false);
    text.textContent=name ? `Are you sure you want to abort the recording on ${name}?` : 'Are you sure you want to abort?';
    return new Promise(done=>{resolve=done;dialog.showModal();no.focus();});
  };
}
export class DevicesPanel {
  constructor({devices,connect,confirmAbort,$ = id=>document.getElementById(id),now=Date.now}) {
    Object.assign(this,{devices,connect,confirmAbort,$,now});this.selected=null;this.busy=false;this.rowViews=new Map();
    $('devicesName').value=devices.name;
    $('devices').addEventListener('click',()=>{ $('devicesDialog').showModal();if(devices.active)this.refresh();else this.render(); });
    $('devicesClose').addEventListener('click',()=>{ $('devicesDialog').close(); });
    $('devicesConnect').addEventListener('click',()=>this.task(async()=>{await connect();await devices.refresh();}));
    $('devicesDisconnect').addEventListener('click',()=>{devices.disconnect();this.render();});
    $('devicesRefresh').addEventListener('click',()=>this.refresh());
    $('devicesName').addEventListener('change',()=>{
      devices.setName($('devicesName').value);$('devicesName').value=devices.name;
      try{localStorage.setItem('whisper-clone.device-name',devices.name);}catch{}
    });
    for (const action of Object.keys(labels)) $(`device-${action}`).addEventListener('click',()=>this.command(action));
    this.timer=setInterval(()=>{if($('devicesDialog').open)this.render();},1000);this.render();
  }
  async task(work) {
    if(this.busy)return;this.busy=true;this.$('devicesMessage').textContent='';this.render();
    try{await work();}catch(error){this.$('devicesMessage').textContent=error.message||'Devices operation failed';}
    finally{this.busy=false;this.render();}
  }
  refresh() { return this.task(()=>this.devices.refresh()); }
  async command(action) {
    const target=this.selected,row=this.devices.rows.find(row=>row.sessionId===target);
    if(!row||this.busy)return;
    if(action==='abort'&&!await this.confirmAbort(row.name))return;
    return this.task(async()=>{
      await this.devices.send(target,action);
      this.$('devicesMessage').textContent=`${labels[action]} sent to ${row.name}. Refresh to check the result.`;
    });
  }
  render() {
    const {$,devices}=this;
    $('devicesStatus').textContent=devices.status;
    $('devicesSummary').textContent=devices.active?'Devices connected':'Devices not connected';
    $('devicesConnect').textContent=devices.active?'Enable audio here':'Connect this tab';
    $('devicesConnect').disabled=this.busy;$('devicesDisconnect').disabled=this.busy||!devices.active;$('devicesRefresh').disabled=this.busy||!devices.active;
    const now=this.now(),rows=devices.rows.filter(row=>now-row.at<PRESENCE_TTL);
    const visible=new Set(rows.map(row=>row.sessionId));
    for(const [id,view] of this.rowViews){
      if(!visible.has(id)){view.tr.remove();this.rowViews.delete(id);}
    }
    if(!rows.some(row=>row.sessionId===this.selected))this.selected=null;
    for(const row of rows){
      let view=this.rowViews.get(row.sessionId);
      if(!view){
        const tr=document.createElement('tr'),name=document.createElement('td'),button=document.createElement('button');
        const status=document.createElement('td'),sound=document.createElement('td'),seen=document.createElement('td');
        button.type='button';button.className='device-select';
        button.addEventListener('click',()=>{this.selected=row.sessionId;this.render();});
        name.append(button);tr.append(name,status,sound,seen);$('deviceRows').append(tr);
        view={tr,button,status,sound,seen};this.rowViews.set(row.sessionId,view);
      }
      const {tr,button,status,sound,seen}=view,age=Math.max(0,now-row.at);
      setText(button,`${row.name}${row.local?' — this tab':''} · ${row.sessionId.slice(0,8)}`);
      button.setAttribute('aria-pressed',String(row.sessionId===this.selected));
      const reported=`${stateLabels[row.state]||row.state}${row.transcribing?' · Transcribing':''}${row.uploading?' · Drive busy':''}${!row.audioReady?' · Enable audio locally':''}`;
      setText(status,`${age>=RECENT_MS?'Updates delayed · Last reported: ':''}${reported}`);
      setText(sound,inputActivityLabel(row,now));setText(seen,`${Math.floor(age/1000)}s ago`);
      tr.classList.toggle('selected',row.sessionId===this.selected);
    }
    $('devicesEmpty').hidden=rows.length>0;
    const row=rows.find(row=>row.sessionId===this.selected),recent=!!row;
    const pending=[...devices.pending.values()].some(p=>p.target===this.selected&&!p.expired&&!['completed','failed'].includes(p.result?.status));
    const allowed={start:row?.state==='idle'&&row.audioReady,pause:row?.state==='recording',resume:row?.state==='paused'&&row.audioReady,
      stop:['recording','paused','error'].includes(row?.state),'stop-and-transcribe':['recording','paused','error'].includes(row?.state),abort:row?.state!=='idle'&&row?.state!=='aborting'};
    for(const action of Object.keys(labels)){
      const repeated=[...devices.pending.values()].some(p=>p.target===this.selected&&p.action===action&&!p.expired&&!['completed','failed'].includes(p.result?.status));
      $(`device-${action}`).disabled=this.busy||!devices.active||!recent||repeated||(pending&&!['stop','abort'].includes(action))||!allowed[action];
    }
    $('devicesResults').replaceChildren();
    for(const pending of [...devices.pending.values()].slice(-10).reverse()){
      const p=document.createElement('p'),name=rows.find(row=>row.sessionId===pending.target)?.name||pending.target.slice(0,8);
      const status=pending.expired?'No final response before expiry':pending.result?.status|| (pending.uncertain?'Delivery uncertain':'Sent');
      p.textContent=`${name} · ${labels[pending.action]} · ${status}${pending.result?.message?`: ${pending.result.message}`:''}`;$('devicesResults').append(p);
    }
  }
  dispose(){clearInterval(this.timer);}
}

