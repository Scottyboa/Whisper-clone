import test from 'node:test';
import assert from 'node:assert/strict';
import { DeviceControl, COMMAND_TTL, RECENT_MS, PRESENCE_TTL, SESSION_FILE_TTL } from '../js/device-control.mjs';
import { TranscriptDrive } from '../js/transcript-drive.mjs';
const json=(body,status=200,headers={})=>new Response(JSON.stringify(body),{status,headers:{'Content-Type':'application/json',...headers}});
const defer=()=>{let resolve;const promise=new Promise(r=>resolve=r);return {promise,resolve};};
const account={homeAccountId:'same-account'};
function network(){
  let clock=Date.parse('2026-10-15T10:00:00Z'),serial=0,ids=0,folder=null,intercept;
  const files=new Map(),calls=[];
  const metadata=file=>({id:file.id,name:file.name,file:{},parentReference:{id:file.parent},size:new TextEncoder().encode(file.text).length,
    eTag:`"${file.version}"`,createdDateTime:file.created,lastModifiedDateTime:file.modified,'@microsoft.graph.downloadUrl':`https://download.example/${file.id}`});
  const write=(name,data,parent='control')=>{
    let file=[...files.values()].find(f=>f.name===name&&f.parent===parent);
    if(!file){file={id:`file-${++serial}`,name,parent,created:new Date(clock).toISOString(),version:0};files.set(file.id,file);}
    file.text=typeof data==='string'?data:JSON.stringify(data);file.version++;file.modified=new Date(clock).toISOString();return file;
  };
  const fetcher=async(input,opts={})=>{
    const url=new URL(input),method=opts.method||'GET',headers=new Headers(opts.headers),path=decodeURIComponent(url.pathname);
    calls.push({url,method,headers,body:opts.body});
    const response=await intercept?.({url,path,method,headers,opts,files,write});if(response)return response;
    if(url.hostname==='download.example'){
      assert.equal(headers.has('Authorization'),false);assert.equal(opts.credentials,'omit');
      return new Response(files.get(path.slice(1))?.text||'');
    }
    assert.equal(url.hostname,'graph.microsoft.com');assert.equal(headers.get('Authorization'),'Bearer test-token');
    if(path.endsWith('/special/approot'))return json({id:'root',folder:{}});
    if(path==='/v1.0/me/drive/items/root:/DeviceControl')return folder?json(folder):json({},404);
    if(path==='/v1.0/me/drive/items/root/children'&&method==='POST'){
      assert.equal(JSON.parse(opts.body).name,'DeviceControl');if(folder)return json({},409);
      folder={id:'control',name:'DeviceControl',folder:{},parentReference:{id:'root'}};return json(folder,201);
    }
    if(path==='/v1.0/me/drive/items/control/children'){
      const select=url.searchParams.get('$select')?.split(',');
      return json({value:[...files.values()].filter(f=>f.parent==='control').map(file=>{
        const item=metadata(file);return select?Object.fromEntries(Object.entries(item).filter(([key])=>select.includes(key))):item;
      })});
    }
    const put=/^\/v1.0\/me\/drive\/items\/control:\/(.+):\/content$/.exec(path);
    if(put&&method==='PUT'){
      const exists=[...files.values()].find(f=>f.name===put[1]&&f.parent==='control');
      if(exists&&url.searchParams.get('@microsoft.graph.conflictBehavior')==='fail')return json({},409);
      return json(metadata(write(put[1],opts.body)),exists?200:201);
    }
    const match=/^\/v1.0\/me\/drive\/items\/(file-\d+)$/.exec(path);
    if(match){
      const file=files.get(match[1]);if(!file)return json({},404);
      if(method==='DELETE'){
        if(headers.get('If-Match')!==metadata(file).eTag)return json({},412);
        files.delete(file.id);return new Response(null,{status:204});
      }
      return json(metadata(file));
    }
    throw new Error(`Unexpected request ${method} ${path}`);
  };
  const now=()=>clock;
  const make=(name,execute,{hostTimers=false}={})=>{
    const authCalls=[],timers=[],actions=[],state={state:'idle',audioReady:true,transcribing:false};
    const auth={getAllAccounts:()=>[account],acquireTokenSilent:async options=>{authCalls.push(options);return {account,accessToken:'test-token'};},
      acquireTokenPopup:()=>assert.fail('Background popup'),loginPopup:()=>assert.fail('Unexpected popup')};
    const drive=new TranscriptDrive({client:async()=>auth,fetcher});
    const device=new DeviceControl({drive,now,name,makeId:()=>`00000000-0000-4000-8000-${String(++ids).padStart(12,'0')}`,
      getStatus:()=>state,execute:async action=>{actions.push(action);if(execute)return execute(action);state.state=action==='start'?'recording':action==='pause'?'paused':'idle';},
      schedule:function(fn,delay){
        if(hostTimers&&this!==globalThis)throw new TypeError('Illegal invocation');
        const timer={fn,delay};timers.push(timer);return timer;
      },cancel:function(timer){
        if(hostTimers&&this!==globalThis)throw new TypeError('Illegal invocation');
        if(timer)timer.cancelled=true;
      }});
    return {device,drive,auth,authCalls,timers,actions,state};
  };
  return {make,files,calls,write,now,advance:ms=>clock+=ms,intercept:fn=>{intercept=fn;},metadata};
}

test('browser timer receivers allow connecting, repeated heartbeats, commands and disconnecting',async()=>{
  const n=network(),a=n.make('Work',undefined,{hostTimers:true});
  await a.device.connect();
  assert.equal(a.device.active,true);assert.equal(a.device.status,'Connected');
  const session=a.device.id;
  for(let cycle=0;cycle<3;cycle++){
    const timer=a.timers.at(-1);assert.equal(timer.delay,5000);
    n.advance(timer.delay);await timer.fn();
    assert.equal(a.device.rows.find(row=>row.sessionId===session).at,n.now());
    const stored=[...n.files.values()].find(file=>file.name===`session-${session}.json`);
    assert.equal(JSON.parse(stored.text).at,n.now());
  }
  await a.device.send(session,'start');
  n.advance(5000);await a.timers.at(-1).fn();
  await Promise.all([...a.device.inflight.values()]);
  assert.deepEqual(a.actions,['start']);
  await a.device.refresh();assert.equal(a.device.rows[0].state,'recording');
  const timer=a.timers.at(-1),writes=n.calls.filter(call=>call.method==='PUT').length;
  a.device.disconnect();assert.equal(timer.cancelled,true);assert.equal(a.device.active,false);
  n.advance(5000);await timer.fn();
  assert.equal(n.calls.filter(call=>call.method==='PUT').length,writes);
  await a.device.connect();assert.equal(a.device.active,true);assert.notEqual(a.device.id,session);
  a.device.disconnect();
});

test('presence lists both tabs under the same account with independent identities and audio status',async()=>{
  const n=network(),a=n.make('Work'),b=n.make('Home');await a.device.connect();await b.device.connect();
  await a.device.refresh();assert.equal(a.device.rows.length,2);assert.equal(a.device.rows[0].name,'Work');assert.equal(a.device.rows[0].local,true);
  assert.notEqual(a.device.id,b.device.id);assert.equal(a.device.rows.find(r=>r.name==='Home').state,'idle');
  b.state.state='recording';n.advance(5000);await b.device.runCycle();await a.device.refresh();
  assert.equal(a.device.rows.find(r=>r.name==='Home').state,'recording');
  assert.equal(b.timers.at(-1).delay,5000);
  const statuses=[...n.files.values()].filter(f=>f.name.startsWith('session-')).map(f=>JSON.parse(f.text));
  assert.ok(statuses.every(s=>!('transcript' in s)&&!('apiKey' in s)&&!('email' in s)));
  assert.ok(n.calls.every(c=>!c.url.pathname.includes('/Transcripts')));
});

test('sound activity shares the existing heartbeat, stays unchanged during silence and supports old tabs',async()=>{
  const n=network(),a=n.make('Work'),b=n.make('Home');
  Object.assign(a.state,{inputActivityVersion:1,lastSoundAt:null});
  Object.assign(b.state,{inputActivityVersion:1,lastSoundAt:null});
  await a.device.connect();await b.device.connect();await a.device.refresh();
  const home=()=>a.device.rows.find(row=>row.sessionId===b.device.id);
  assert.equal(home().lastSoundAt,null);assert.equal(home().inputActivityVersion,1);
  const name=`session-${b.device.id}.json`,file=[...n.files.values()].find(f=>f.name===name);
  b.state.lastSoundAt=n.now();const heard=n.now();
  for(let cycle=0;cycle<3;cycle++){
    n.advance(5000);await b.device.runCycle();await a.device.runCycle();
    assert.equal(home().lastSoundAt,heard);assert.equal(home().at,n.now());
    assert.equal(n.files.size,2);assert.equal([...n.files.values()].find(f=>f.name===name).id,file.id);
  }
  const stored=JSON.parse(file.text);
  assert.deepEqual(Object.keys(stored).sort(),['schema','type','sessionId','name','at','state','transcribing','uploading','audioReady','startedAt','inputActivityVersion','lastSoundAt'].sort());
  delete b.state.inputActivityVersion;delete b.state.lastSoundAt;
  n.advance(5000);await b.device.runCycle();await a.device.runCycle();
  assert.equal(home().state,'idle');assert.equal('inputActivityVersion' in home(),false);assert.equal('lastSoundAt' in home(),false);
  // A malformed optional field must not remove a compatible tab or claim silence.
  n.write(name,{...JSON.parse(file.text),inputActivityVersion:1,lastSoundAt:'bad timestamp'});
  await a.device.refresh();assert.ok(home());assert.equal('inputActivityVersion' in home(),false);
});

test('heartbeats overwrite one file per session and automatically refresh other live tabs',async()=>{
  const n=network(),a=n.make('This computer'),b=n.make('This computer');
  await a.device.connect();await b.device.connect();
  const name=`session-${b.device.id}.json`,file=[...n.files.values()].find(f=>f.name===name);
  for(let cycle=0;cycle<12;cycle++){
    n.advance(5000);b.state.state=cycle%2?'recording':'paused';
    await b.timers.at(-1).fn();await a.timers.at(-1).fn();
    const row=a.device.rows.find(row=>row.sessionId===b.device.id);
    assert.equal(row.at,n.now());assert.equal(row.state,b.state.state);
    assert.equal(a.device.rows.length,2);assert.equal(n.files.size,2);
    assert.equal([...n.files.values()].find(f=>f.name===name).id,file.id);
  }
  assert.equal(file.version,13);assert.equal(a.device.active,true);assert.equal(b.device.active,true);
});

test('presence survives delays for two minutes; cleanup waits five minutes and a returning tab can publish again',async()=>{
  const n=network(),a=n.make('Work'),b=n.make('Home');
  await a.device.connect();await b.device.connect();await a.device.refresh();
  b.state.state='recording';
  const name=`session-${b.device.id}.json`,old=[...n.files.values()].find(f=>f.name===name);
  assert.equal(RECENT_MS,30000);assert.equal(PRESENCE_TTL,120000);assert.equal(SESSION_FILE_TTL,300000);
  n.advance(PRESENCE_TTL-1);await a.device.refresh();
  assert.ok(a.device.rows.some(row=>row.sessionId===b.device.id));assert.ok(n.files.has(old.id));
  n.advance(1);await assert.rejects(a.device.send(b.device.id,'start'),/recently seen/);
  await a.device.refresh();
  assert.equal(a.device.rows.length,1);assert.equal(a.device.rows[0].sessionId,a.device.id);assert.equal(n.files.has(old.id),true);
  n.advance(SESSION_FILE_TTL-PRESENCE_TTL-1);await a.device.refresh();assert.equal(n.files.has(old.id),true);
  n.advance(1);await a.device.refresh();assert.equal(n.files.has(old.id),false);
  assert.equal(b.device.active,true);assert.equal(b.state.state,'recording');assert.deepEqual(b.actions,[]);
  await b.device.runCycle();await a.device.runCycle();
  assert.equal(a.device.rows.find(row=>row.sessionId===b.device.id).state,'recording');
  assert.ok([...n.files.values()].some(f=>f.name===name));
});

test('a delayed target stays listed and can still acknowledge a command',async()=>{
  const n=network(),a=n.make('Work'),b=n.make('Home');
  await a.device.connect();await b.device.connect();await a.device.refresh();
  n.advance(RECENT_MS+1000);await a.device.refresh();
  assert.ok(a.device.rows.some(row=>row.sessionId===b.device.id));
  const id=await a.device.send(b.device.id,'start');
  await b.device.runCycle();await Promise.all([...b.device.inflight.values()]);await b.device.runCycle();await a.device.refresh();
  assert.deepEqual(b.actions,['start']);assert.equal(a.device.pending.get(id).result.status,'completed');
});

test('missing listings and failed reads preserve last-known rows without extending heartbeat expiry',async()=>{
  const n=network(),a=n.make('Work'),b=n.make('Home');
  await a.device.connect();await b.device.connect();await a.device.refresh();
  const file=[...n.files.values()].find(f=>f.name===`session-${b.device.id}.json`),seen=n.now();
  const home=()=>a.device.rows.find(row=>row.sessionId===b.device.id);
  n.advance(15000);
  n.intercept(({method,path})=>method==='GET'&&path.endsWith('/control/children')?json({value:[]}):null);
  await a.device.refresh();assert.equal(home().at,seen);
  n.intercept(({method,path})=>method==='GET'&&path.endsWith(`/items/${file.id}`)?json({},500):null);
  n.advance(15000);await a.device.refresh();assert.equal(home().at,seen);
  n.advance(PRESENCE_TTL-(n.now()-seen)-1);await a.device.refresh();assert.equal(home().at,seen);
  n.advance(1);await a.device.refresh();assert.equal(home(),undefined);assert.equal(n.files.has(file.id),true);
});

test('sequential Drive reads taking longer than the former timeout still list the remote tab',async()=>{
  const n=network(),a=n.make('Work'),b=n.make('Home');await a.device.connect();await b.device.connect();
  const file=[...n.files.values()].find(f=>f.name===`session-${b.device.id}.json`),seen=n.now();
  n.intercept(({url,path,method})=>{
    if(method==='GET'&&(path.endsWith(`/items/${file.id}`)||url.hostname==='download.example'))n.advance(12000);
  });
  await a.device.refresh();
  const home=a.device.rows.find(row=>row.sessionId===b.device.id);
  assert.equal(home.at,seen);assert.equal(n.now()-seen,24000);
});

test('an older overlapping refresh cannot replace a newer remote status',async()=>{
  const n=network(),a=n.make('Work'),b=n.make('Home');
  await a.device.connect();await b.device.connect();await a.device.refresh();
  const file=[...n.files.values()].find(f=>f.name===`session-${b.device.id}.json`),gate=defer();let blocked=false;
  n.intercept(async({url,path})=>{
    if(!blocked&&url.hostname==='download.example'&&path===`/${file.id}`){
      blocked=true;const old=file.text;await gate.promise;return new Response(old);
    }
  });
  const oldRefresh=a.device.refresh();await new Promise(resolve=>setImmediate(resolve));
  assert.equal(blocked,true);n.advance(5000);b.state.state='recording';await b.device.runCycle();await a.device.refresh();
  gate.resolve();await oldRefresh;
  const home=a.device.rows.find(row=>row.sessionId===b.device.id);
  assert.equal(home.state,'recording');assert.equal(home.at,n.now());
});

test('the next connection drains old session files from before the update without touching other data',async()=>{
  const n=network(),stale=[];
  for(let index=0;index<28;index++)stale.push(n.write(`session-99999999-0000-4000-8000-${String(index).padStart(12,'0')}.json`,{old:true}));
  const keep=n.write('keep.json',{unrelated:true}),transcript=n.write('transcript.txt','text','transcripts');
  const folder=n.write('session-99999999-0000-4000-8000-999999999999.json',{});
  n.advance(SESSION_FILE_TTL);
  n.intercept(({method,path})=>method==='GET'&&path.endsWith('/control/children')?json({value:[
    ...[...n.files.values()].filter(f=>f.id!==folder.id&&f.parent==='control').map(n.metadata),
    {...n.metadata(folder),file:undefined,folder:{}},
  ]}):null);
  const a=n.make('New tab');await a.device.connect();
  assert.equal(stale.filter(f=>n.files.has(f.id)).length,3);
  n.advance(5000);await a.timers.at(-1).fn();
  assert.ok(stale.every(f=>!n.files.has(f.id)));
  assert.ok(n.files.has(keep.id));assert.ok(n.files.has(transcript.id));assert.ok(n.files.has(folder.id));
  assert.equal(a.device.rows.length,1);assert.equal(a.device.active,true);
});

test('slow backlog cleanup keeps publishing heartbeats before this tab can expire',async()=>{
  const n=network();
  for(let index=0;index<12;index++)n.write(`session-99999999-0000-4000-8000-${String(index).padStart(12,'0')}.json`,{});
  n.advance(SESSION_FILE_TTL);
  n.intercept(({method,path})=>{
    if((method==='GET'||method==='DELETE')&&/\/items\/file-\d+$/.test(path))n.advance(2000);
  });
  const a=n.make('Work');await a.device.connect();
  const beats=n.calls.filter(call=>call.method==='PUT'&&call.url.pathname.includes('/session-')).map(call=>JSON.parse(call.body).at);
  assert.ok(beats.length>1);
  assert.ok(beats.slice(1).every((at,index)=>at-beats[index]<RECENT_MS));
  assert.equal(n.files.size,1);assert.equal(a.device.rows.length,1);
  assert.ok(n.now()-a.device.rows[0].at<RECENT_MS);
});

for(const phase of ['metadata read','delete'])test(`a new heartbeat during cleanup ${phase} is never deleted`,async()=>{
  const n=network(),a=n.make('Work'),b=n.make('Home');await a.device.connect();await b.device.connect();
  const name=`session-${b.device.id}.json`,file=[...n.files.values()].find(f=>f.name===name);
  n.advance(SESSION_FILE_TTL);let renewed=false;
  n.intercept(({method,path})=>{
    if(!renewed&&path.endsWith(`/items/${file.id}`)&&method===(phase==='delete'?'DELETE':'GET')){
      renewed=true;n.write(name,b.device.snapshot());
    }
  });
  await a.device.refresh();assert.equal(renewed,true);assert.equal(n.files.has(file.id),true);
  await a.device.runCycle();assert.ok(a.device.rows.some(row=>row.sessionId===b.device.id));
  assert.ok(n.calls.filter(call=>call.method==='DELETE').every(call=>call.headers.has('If-Match')));
});

test('cleanup revalidates the folder and name before deleting a previously listed session',async()=>{
  const n=network(),a=n.make('Work'),b=n.make('Home');await a.device.connect();await b.device.connect();
  const file=[...n.files.values()].find(f=>f.name===`session-${b.device.id}.json`);
  n.advance(SESSION_FILE_TTL);
  n.intercept(({method,path})=>{
    if(method==='GET'&&path.endsWith(`/items/${file.id}`))file.parent='transcripts';
  });
  await a.device.refresh();assert.equal(n.files.has(file.id),true);
  assert.equal(n.calls.some(call=>call.method==='DELETE'&&call.url.pathname.endsWith(`/${file.id}`)),false);
});

test('cleanup retries after throttling and disconnecting during validation prevents deletion',async()=>{
  const n=network(),a=n.make('Work'),b=n.make('Home');await a.device.connect();await b.device.connect();
  const file=[...n.files.values()].find(f=>f.name===`session-${b.device.id}.json`);
  n.advance(SESSION_FILE_TTL);
  n.intercept(({method})=>method==='DELETE'?json({},429,{'Retry-After':'12'}):null);
  await a.device.runCycle();assert.equal(n.files.has(file.id),true);assert.equal(a.timers.at(-1).delay,12000);
  const gate=defer();n.intercept(async({method,path})=>{
    if(method==='GET'&&path.endsWith(`/items/${file.id}`))await gate.promise;
  });
  const cycle=a.device.runCycle();await new Promise(resolve=>setImmediate(resolve));a.device.disconnect();gate.resolve();await cycle;
  assert.equal(n.files.has(file.id),true);
  n.intercept(null);await a.device.connect();assert.equal(n.files.has(file.id),false);
});

test('targeted command executes once only on its selected tab and returns acknowledgement',async()=>{
  const n=network(),a=n.make('Work'),b=n.make('Home');await a.device.connect();await b.device.connect();await a.device.refresh();
  const id=await a.device.send(b.device.id,'start');await a.device.runCycle();assert.deepEqual(a.actions,[]);
  await b.device.runCycle();await b.device.runCycle();await a.device.refresh();
  assert.deepEqual(b.actions,['start']);assert.equal(a.device.pending.get(id).result.status,'completed');
  assert.equal(b.device.active,true);assert.equal(a.device.rows.find(r=>r.sessionId===b.device.id).state,'recording');
  await a.device.send(b.device.id,'stop');await b.device.runCycle();await a.device.refresh();
  assert.equal(b.device.active,true);assert.equal(b.state.state,'idle');assert.equal(b.actions.length,2);
});

test('the local tab can be selected and commanded through the same protocol',async()=>{
  const n=network(),a=n.make('Work');await a.device.connect();await a.device.refresh();
  const id=await a.device.send(a.device.id,'start');await a.device.runCycle();await Promise.all([...a.device.inflight.values()]);await a.device.runCycle();await a.device.refresh();
  assert.deepEqual(a.actions,['start']);assert.equal(a.device.pending.get(id).result.status,'completed');
});

test('one outstanding command per target avoids accidental overwrites or double-click replay',async()=>{
  const n=network(),a=n.make('A'),b=n.make('B');await a.device.connect();await b.device.connect();await a.device.refresh();
  await a.device.send(b.device.id,'start');await assert.rejects(a.device.send(b.device.id,'start'),/previous command/);
  assert.equal([...n.files.values()].filter(f=>f.name.startsWith('command-')).length,1);
});

test('expired commands never execute and reconnecting uses a fresh session identity',async()=>{
  const n=network(),a=n.make('A'),b=n.make('B');await a.device.connect();await b.device.connect();await a.device.refresh();
  const old=b.device.id,id=await a.device.send(old,'start');n.advance(COMMAND_TTL+1);
  await b.device.runCycle();await a.device.refresh();assert.deepEqual(b.actions,[]);assert.equal(a.device.pending.get(id).expired,true);
  b.device.disconnect();await b.device.connect();assert.notEqual(b.device.id,old);await b.device.runCycle();assert.deepEqual(b.actions,[]);
});

test('stale targets must be refreshed before sending; old protocol signals are cleaned without touching unrelated files',async()=>{
  const n=network(),a=n.make('A'),b=n.make('B');await a.device.connect();await b.device.connect();await a.device.refresh();
  n.advance(PRESENCE_TTL);await assert.rejects(a.device.send(b.device.id,'start'),/recently seen/);
  n.write('keep.json',{unrelated:true});n.write('transcript.txt','text','transcripts');
  const old=n.write(`ack-${b.device.id}-00000000-0000-4000-8000-999999999999.json`,{});
  n.advance(300001);await a.device.runCycle();assert.equal(n.files.has(old.id),false);
  assert.ok([...n.files.values()].some(f=>f.name==='keep.json'));assert.ok([...n.files.values()].some(f=>f.name==='transcript.txt'));
  assert.ok(n.calls.filter(c=>c.method==='DELETE').every(c=>c.headers.has('If-Match')));
});

test('schema, target, action, creation time and TTL are validated before execution',async()=>{
  const n=network(),b=n.make('B');await b.device.connect();
  const base={schema:'whisper-clone.devices.v1',type:'command',target:b.device.id,sender:'00000000-0000-4000-8000-111111111111',action:'start',createdAt:n.now(),expiresAt:n.now()+60000};
  let serial=10;
  for(const changes of [{schema:'wrong'},{target:'other'},{action:'eval'},{createdAt:n.now()-1},{expiresAt:n.now()+60001},{createdAt:n.now()+10000}, {type:'ack'}]){
    const id=`00000000-0000-4000-8000-${String(serial++).padStart(12,'0')}`;n.write(`command-${b.device.id}-${id}.json`,{...base,...changes,id});
  }
  await b.device.runCycle();assert.deepEqual(b.actions,[]);
});

test('acknowledgement failure before execution retries safely; final ack failure never replays execution',async()=>{
  const n=network(),a=n.make('A'),b=n.make('B');await a.device.connect();await b.device.connect();await a.device.refresh();
  const id=await a.device.send(b.device.id,'start');let failBefore=true,failAfter=true;
  n.intercept(({path,method,opts})=>{
    if(method==='PUT'&&path.includes('/ack-')){
      const body=JSON.parse(opts.body);
      if(body.status==='accepted'&&failBefore){failBefore=false;return json({},503,{'Retry-After':'12'});}
      if(body.status==='completed'&&failAfter){failAfter=false;return json({},503,{'Retry-After':'13'});}
    }
  });
  await b.device.runCycle();assert.equal(b.actions.length,0);assert.equal(b.timers.at(-1).delay,12000);
  await b.device.runCycle();assert.deepEqual(b.actions,['start']);
  await Promise.all([...b.device.inflight.values()]);await b.device.runCycle();
  assert.ok(b.timers.some(timer=>timer.delay===13000));
  await b.device.runCycle();await a.device.refresh();assert.deepEqual(b.actions,['start']);assert.equal(a.device.pending.get(id).result.status,'completed');
});

test('disconnect during an in-flight file read prevents remote execution and does not unlink authentication',async()=>{
  const n=network(),a=n.make('A'),b=n.make('B');await a.device.connect();await b.device.connect();await a.device.refresh();await a.device.send(b.device.id,'start');
  const gate=defer();n.intercept(async({url,path})=>{if(url.hostname==='download.example'&&n.files.get(path.slice(1))?.name.startsWith('command-'))await gate.promise;});
  const cycle=b.device.runCycle();await new Promise(resolve=>setImmediate(resolve));b.device.disconnect();gate.resolve();await cycle;
  assert.deepEqual(b.actions,[]);assert.equal(b.device.active,false);assert.ok(b.drive.account);
  await b.device.connect();assert.equal(b.device.active,true);assert.deepEqual(b.actions,[]);
});

test('expired accepted commands are not executed after a delayed acknowledgement write',async()=>{
  const n=network(),a=n.make('A'),b=n.make('B');await a.device.connect();await b.device.connect();await a.device.refresh();const id=await a.device.send(b.device.id,'start');
  n.intercept(({path,method,opts})=>{if(method==='PUT'&&path.includes('/ack-')&&JSON.parse(opts.body).status==='accepted')n.advance(COMMAND_TTL+1);});
  await b.device.runCycle();await a.device.refresh();assert.deepEqual(b.actions,[]);assert.equal(a.device.pending.get(id).result.status,'failed');
});

test('failed recording command is acknowledged and the receiving tab stays connected',async()=>{
  const n=network(),a=n.make('A'),b=n.make('B',()=>{throw new Error('Microphone unavailable');});await a.device.connect();await b.device.connect();await a.device.refresh();
  const id=await a.device.send(b.device.id,'start');await b.device.runCycle();await Promise.all([...b.device.inflight.values()]);await b.device.runCycle();await a.device.refresh();
  assert.equal(a.device.pending.get(id).result.status,'failed');assert.equal(b.device.active,true);
});

test('OneDrive backoff and authentication failures do not open background sign-in popups',async()=>{
  const n=network(),b=n.make('B');await b.device.connect();
  n.intercept(({method})=>method==='PUT'?json({},429,{'Retry-After':'25'}):null);
  await b.device.runCycle();assert.equal(b.timers.at(-1).delay,25000);assert.equal(b.device.status,'Reconnecting…');
  n.intercept(({method})=>method==='PUT'?json({},401):null);
  await b.device.runCycle();assert.equal(b.device.active,false);assert.equal(b.device.status,'Reconnect Devices');
  assert.ok(b.authCalls.every(c=>c.account.homeAccountId===account.homeAccountId));
});

test('presence and Abort polling continue while a prior Start is waiting on microphone startup',async()=>{
  const gate=defer(),n=network(),a=n.make('A');let b;
  b=n.make('B',async action=>{
    if(action==='start'){b.state.state='starting';await gate.promise;}
    if(action==='abort'){b.state.state='idle';gate.resolve();}
  });
  await a.device.connect();await b.device.connect();await a.device.refresh();
  await a.device.send(b.device.id,'start');await b.device.runCycle();
  assert.equal(b.device.inflight.size,1);n.advance(5000);await b.device.runCycle();await a.device.refresh();
  assert.equal(a.device.rows.find(row=>row.sessionId===b.device.id).state,'starting');
  await a.device.send(b.device.id,'abort');await b.device.runCycle();
  await Promise.all([...b.device.inflight.values()]);await b.device.runCycle();await a.device.refresh();
  assert.deepEqual(b.actions,['start','abort']);assert.equal(b.device.active,true);assert.equal(b.state.state,'idle');
  assert.ok([...a.device.pending.values()].every(p=>p.result.status==='completed'));
});

test('page refresh/disconnect cannot leave a cached old cycle suppressing the new heartbeat',async()=>{
  const gate=defer(),n=network(),b=n.make('B');await b.device.connect();const old=b.device.id;
  let blocked=true;n.intercept(async({path,method})=>{if(blocked&&method==='PUT'&&path.includes('/session-')){blocked=false;await gate.promise;}});
  const oldCycle=b.device.runCycle();await new Promise(resolve=>setImmediate(resolve));b.device.disconnect();
  const reconnect=b.device.connect();gate.resolve();await Promise.all([oldCycle,reconnect]);
  assert.notEqual(b.device.id,old);assert.equal(b.device.active,true);
  assert.ok([...n.files.values()].some(f=>f.name===`session-${b.device.id}.json`));
});

test('a moved command item or changed account cannot cause execution outside the protocol folder',async()=>{
  const n=network(),a=n.make('A'),b=n.make('B');await a.device.connect();await b.device.connect();await a.device.refresh();await a.device.send(b.device.id,'start');
  n.intercept(({path,method,files})=>{
    if(method==='GET'&&path.includes('/items/file-')){
      const f=files.get(path.split('/').at(-1));
      if(f?.name.startsWith('command-'))return json({...n.metadata(f),parentReference:{id:'elsewhere'}});
    }
  });
  await b.device.runCycle();assert.deepEqual(b.actions,[]);
  b.auth.acquireTokenSilent=async()=>({account:{homeAccountId:'wrong-account'},accessToken:'other-token'});
  const count=n.calls.length;await b.device.runCycle();assert.equal(n.calls.length,count);assert.deepEqual(b.actions,[]);
});

