const FOLDER = 'DeviceControl';
const itemPath = id => `/me/drive/items/${encodeURIComponent(id)}`;
const uuid = '[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}';
const idPattern = new RegExp(`^${uuid}$`);
const sessionPattern = new RegExp(`^session-(${uuid})\\.json$`);
const commandPattern = new RegExp(`^command-(${uuid})-(${uuid})\\.json$`);
const ackPattern = new RegExp(`^ack-(${uuid})-(${uuid})\\.json$`);
const ACTIONS = new Set(['start', 'pause', 'resume', 'stop', 'stop-and-transcribe', 'abort']);
const STATES = new Set(['idle','starting','recording','pausing','paused','resuming','stopping','aborting','error']);
const SCHEMA = 'whisper-clone.devices.v1';
export const COMMAND_TTL = 60000;
export const RECENT_MS = 10000;
const MAX_JSON = 16384;
const sameChild = (item, parent, name) => item?.id && item.parentReference?.id === parent && !item.remoteItem &&
  (name == null || item.name === name);
const isFile = item => !!item.file && !item.folder;
const cleanName = value => String(value || '').trim().replace(/[\u0000-\u001f]/g, '').slice(0, 60) || 'This computer';

export class DeviceControl {
  constructor({ drive, execute, getStatus, onChange = () => {}, now = Date.now,
    makeId = () => crypto.randomUUID(), schedule = setTimeout, cancel = clearTimeout, name = 'This computer' }) {
    Object.assign(this, { drive, execute, getStatus, onChange, now, makeId });
    // Browser timer functions require the Window receiver, not this controller.
    this.schedule = schedule.bind(globalThis); this.cancel = cancel.bind(globalThis);
    this.name = cleanName(name); this.active = false; this.generation = 0; this.timer = null;
    this.id = null; this.account = null; this.folderId = null; this.rows = []; this.pending = new Map();
    this.seen = new Set(); this.acks = new Map(); this.inflight = new Map(); this.status = 'Not connected'; this.cycle = null;
  }
  emit() { this.onChange(); }
  setName(name) { this.name = cleanName(name); this.emit(); }
  async folder(token) {
    const root = await (await this.drive.request(token, '/me/drive/special/approot?$select=id,folder')).json();
    if (!root?.id || !root.folder) throw new Error('OneDrive app folder is unavailable.');
    const path = `${itemPath(root.id)}:/${FOLDER}`;
    let folder;
    try { folder = await (await this.drive.request(token, path)).json(); }
    catch (error) {
      if (error.status !== 404) throw error;
      try {
        folder = await (await this.drive.request(token, `${itemPath(root.id)}/children`, { method:'POST',
          headers:{'Content-Type':'application/json'}, body:JSON.stringify({name:FOLDER,folder:{},'@microsoft.graph.conflictBehavior':'fail'}) })).json();
      } catch (error) {
        if (error.status !== 409) throw error;
        folder = await (await this.drive.request(token, path)).json();
      }
    }
    if (!sameChild(folder, root.id, FOLDER) || !folder.folder) throw new Error('Invalid Devices folder.');
    return folder.id;
  }
  async connect({ interactive = true, account } = {}) {
    if (this.active) return;
    const generation = ++this.generation; this.status = 'Connecting…'; this.emit();
    try {
      const token = await this.drive.token({interactive, ...(account ? {account} : {})});
      const selected = account || this.drive.account;
      if (!selected?.homeAccountId) throw new Error('Microsoft did not return an account.');
      const folder = await this.folder(token);
      if (generation !== this.generation) return;
      if (this.cycle) await this.cycle;
      if (generation !== this.generation) return;
      this.account = selected; this.folderId = folder; this.id = this.makeId();
      this.connectedAt = this.now(); this.seen.clear(); this.acks.clear(); this.pending.clear();
      this.active = true; this.status = 'Connected'; this.rows = [];
      await this.runCycle(generation);
    } catch (error) {
      if (generation === this.generation) { this.active = false; this.status = !interactive && /needs sign-in|Link Microsoft/.test(error.message || '') ? 'Not connected — click Connect this tab' : error.message || 'Connection failed'; this.emit(); }
      throw error;
    }
  }
  disconnect() {
    this.active = false; this.generation++; this.cancel(this.timer); this.timer = null;
    this.status = 'Not connected'; this.pending.clear(); this.rows = []; this.emit();
  }
  fresh(generation) { return this.active && generation === this.generation; }
  auth() { return this.drive.token({interactive:false,account:this.account}); }
  snapshot() {
    const raw = this.getStatus();
    return { schema:SCHEMA, type:'session', sessionId:this.id, name:this.name, at:this.now(),
      state:STATES.has(raw.state) ? raw.state : 'error', transcribing:!!raw.transcribing,
      uploading:!!raw.uploading, audioReady:!!raw.audioReady,
      startedAt:Number.isFinite(raw.startedAt) ? raw.startedAt : null };
  }
  async publishPresence(token, generation, force = false) {
    if (!this.fresh(generation)) return;
    const previous = this.rows.find(row=>row.sessionId===this.id);
    if (!force && previous && this.now()-previous.at<5000) return;
    const own = this.snapshot();
    await this.put(token,`session-${this.id}.json`,own);
    if (!this.fresh(generation)) return;
    this.rows = [{...own,local:true},...this.rows.filter(row=>row.sessionId!==this.id)];
    this.emit();
  }
  async put(token, name, data, { create = false } = {}) {
    const response = await this.drive.request(token, `${itemPath(this.folderId)}:/${encodeURIComponent(name)}:/content${create ? '?@microsoft.graph.conflictBehavior=fail' : ''}`, {
      method:'PUT',headers:{'Content-Type':'application/json; charset=utf-8'},body:JSON.stringify(data),
    });
    return response.json();
  }
  async read(token, item, { immutable = false } = {}) {
    if (!sameChild(item, this.folderId) || !isFile(item)) throw new Error('Invalid Devices item.');
    const fresh = await (await this.drive.request(token, itemPath(item.id))).json();
    if (!sameChild(fresh, this.folderId, item.name) || !isFile(fresh) ||
        (immutable && (!item.eTag || fresh.eTag !== item.eTag)) || fresh.size > MAX_JSON) throw new Error('Devices item changed.');
    const url = new URL(fresh['@microsoft.graph.downloadUrl']);
    if (url.protocol !== 'https:' || url.username || url.password) throw new Error('Invalid Devices download link.');
    const response = await this.drive.fetcher(url.href, {cache:'no-store',credentials:'omit',signal:AbortSignal.timeout(15000)});
    if (!response.ok) throw new Error('Devices file could not be read.');
    const text = await response.text();
    if (text.length > MAX_JSON) throw new Error('Devices file is too large.');
    return JSON.parse(text);
  }
  validCommand(value, target, id) {
    const now = this.now();
    return value?.schema === SCHEMA && value.type === 'command' && value.target === target && value.id === id &&
      idPattern.test(value.sender) && ACTIONS.has(value.action) && Number.isFinite(value.createdAt) &&
      value.createdAt >= this.connectedAt && value.createdAt <= now + 5000 &&
      Number.isFinite(value.expiresAt) && value.expiresAt > now && value.expiresAt > value.createdAt &&
      value.expiresAt - value.createdAt <= COMMAND_TTL && now - value.createdAt <= COMMAND_TTL;
  }
  async flushAcks(token) {
    for (const [name, ack] of this.acks) {
      await this.put(token, name, ack);
      // Completion may replace an accepted ack while its write is in flight.
      if (this.acks.get(name) === ack) this.acks.delete(name);
    }
  }
  async processCommands(token, items, generation) {
    const commands = items.filter(item => commandPattern.exec(item.name)?.[1] === this.id);
    commands.sort((a,b) => Date.parse(a.createdDateTime)-Date.parse(b.createdDateTime) || a.name.localeCompare(b.name));
    for (const item of commands) {
      if (!this.fresh(generation)) return;
      const [, target, id] = commandPattern.exec(item.name);
      if (this.seen.has(id)) continue;
      let command;
      try { command = await this.read(token, item, {immutable:true}); }
      catch (error) { if (error.retryMs || error.status === 401 || error.status === 403) throw error; continue; }
      if (!this.fresh(generation) || !this.validCommand(command,target,id)) continue;
      // Acknowledge before executing. Mark as seen immediately before execution,
      // so a failed final acknowledgement can never replay an action.
      const name = `ack-${this.id}-${id}.json`;
      const base = {schema:SCHEMA,type:'ack',id,target:this.id,sender:command.sender,action:command.action};
      this.acks.set(name, {...base,at:this.now(),status:'accepted'});
      await this.flushAcks(token);
      if (!this.fresh(generation)) return;
      if (!this.validCommand(command,target,id)) {
        this.seen.add(id); this.acks.set(name,{...base,at:this.now(),status:'failed',message:'Command expired before execution'});
        await this.flushAcks(token); continue;
      }
      this.seen.add(id);
      const finish = (status, message) => {
        if (this.fresh(generation)) this.acks.set(name,{...base,at:this.now(),status,message});
      };
      // Recorder commands already serialize their transitions. Do not stall
      // presence/polling during microphone startup: a later Abort must reach it.
      const work = Promise.resolve().then(async()=>{
        if (!this.fresh(generation)) return;
        if (!this.validCommand(command,target,id)) { finish('failed','Command expired before execution'); return; }
        try { await this.execute(command.action); finish('completed','Recording command completed'); }
        catch (error) { finish('failed',String(error.message || 'Command failed').slice(0,300)); }
      }).finally(()=>this.inflight.delete(id));
      this.inflight.set(id,work);
    }
  }
  async cleanup(token, items, generation = this.generation) {
    // Protocol files only; never recurse or touch Transcripts/other app data.
    // Prioritize expired presence; bound each pass so old backlogs cannot stall polling indefinitely.
    let count = 0;
    const ordered = [...items].sort((a,b)=>Number(sessionPattern.test(b.name))-Number(sessionPattern.test(a.name)));
    const expired = item => {
      const age = this.now()-Date.parse(item.lastModifiedDateTime);
      return sessionPattern.test(item.name) ? age >= RECENT_MS :
        (commandPattern.test(item.name) || ackPattern.test(item.name)) && age > 300000;
    };
    for (const item of ordered) {
      if (!this.fresh(generation)) return;
      if (!expired(item) || !isFile(item) || !item.eTag || !sameChild(item,this.folderId)) continue;
      try {
        // Keep this tab alive even while an old backlog takes several requests to clear.
        await this.publishPresence(token,generation);
        if (!this.fresh(generation)) return;
        const current = await (await this.drive.request(token,itemPath(item.id))).json();
        if (!this.fresh(generation)) return;
        if (!sameChild(current,this.folderId,item.name) || !isFile(current) || current.eTag !== item.eTag || !expired(current)) continue;
        await this.publishPresence(token,generation);
        if (!this.fresh(generation)) return;
        // A heartbeat arriving after this read must survive the deletion attempt.
        await this.drive.request(token,itemPath(item.id),{method:'DELETE',headers:{'If-Match':current.eTag}});
      }
      catch (error) { if (![404,412].includes(error.status)) throw error; }
      if (++count >= 25) break;
    }
  }
  runCycle(generation = this.generation) {
    if (this.cycle) return this.cycle;
    const work = this.poll(generation).finally(() => { if (this.cycle === work) this.cycle = null; });
    this.cycle = work; return work;
  }
  async poll(generation) {
    if (!this.fresh(generation)) return;
    let delay = 5000;
    try {
      const token = await this.auth(); if (!this.fresh(generation)) return;
      await this.publishPresence(token,generation,true);
      if (!this.fresh(generation)) return;
      await this.flushAcks(token);
      const items = await this.drive.children(token,this.folderId);
      if (!this.fresh(generation)) return;
      await this.processCommands(token,items,generation);
      if (!this.fresh(generation)) return;
      await this.cleanup(token,items,generation);
      if (!this.fresh(generation)) return;
      await this.flushAcks(token);
      await this.syncRows(token,items,generation);
      if (!this.fresh(generation)) return;
      this.status = 'Connected';
    } catch (error) {
      if (!this.fresh(generation)) return;
      if (error.status === 401 || error.status === 403 || /needs sign-in|Link Microsoft|account changed|same Microsoft account/.test(error.message || '')) {
        this.disconnect(); this.status = 'Reconnect Devices'; this.emit(); return;
      }
      delay = Math.max(5000,Math.min(300000,error.retryMs || 10000)); this.status = 'Reconnecting…';
    } finally {
      if (this.fresh(generation)) { this.emit(); this.timer = this.schedule(()=>this.runCycle(generation),delay); }
    }
  }
  async refresh() {
    if (!this.active) throw new Error('Connect this tab to Devices first.');
    const generation = this.generation, token = await this.auth();
    if (!this.fresh(generation)) return [];
    const items = await this.drive.children(token,this.folderId);
    if (!this.fresh(generation)) return [];
    await this.cleanup(token,items,generation);
    return this.syncRows(token,items,generation);
  }
  async syncRows(token, items, generation) {
    const rows = [];
    for (const item of items) {
      await this.publishPresence(token,generation);
      if (!this.fresh(generation)) return [];
      const match = sessionPattern.exec(item.name);
      if (!match || match[1] === this.id || !isFile(item) || this.now()-Date.parse(item.lastModifiedDateTime)>=RECENT_MS) continue;
      try {
        const value = await this.read(token,item);
        if (value?.schema === SCHEMA && value.type === 'session' && value.sessionId === match[1] &&
            Number.isFinite(value.at) && value.at <= this.now()+5000 && this.now()-value.at<RECENT_MS && STATES.has(value.state)) {
          rows.push({...value,name:cleanName(value.name),local:false});
        }
      } catch (error) { if (error.retryMs) throw error; }
    }
    if (!this.fresh(generation)) return [];
    // Include this tab during listing propagation delays, using its last successful heartbeat time.
    const own = this.rows.find(row=>row.sessionId===this.id);
    this.rows = rows.filter(row=>this.now()-row.at<RECENT_MS);
    if (own && this.now()-own.at<RECENT_MS) this.rows.unshift({...this.snapshot(),at:own.at,local:true});
    for (const [id,pending] of this.pending) {
      const item=items.find(item=>item.name===`ack-${pending.target}-${id}.json`);
      if (item && !['completed','failed'].includes(pending.result?.status)) {
        try {
          await this.publishPresence(token,generation);
          if (!this.fresh(generation)) return [];
          const ack=await this.read(token,item);
          if (ack?.schema===SCHEMA && ack.type==='ack' && ack.id===id && ack.target===pending.target && ack.sender===this.id &&
              ack.action===pending.action && ['accepted','completed','failed'].includes(ack.status)) pending.result=ack;
        } catch (error) { if (error.retryMs) throw error; }
      }
      if (this.now()>pending.expiresAt && !['completed','failed'].includes(pending.result?.status)) pending.expired=true;
    }
    if (!this.fresh(generation)) return [];
    this.emit(); return this.rows;
  }
  async send(target, action) {
    if (!this.active || !idPattern.test(target) || !ACTIONS.has(action)) throw new Error('Invalid Devices command.');
    const row=this.rows.find(row=>row.sessionId===target);
    if (!row || this.now()-row.at>=RECENT_MS) throw new Error('Refresh Devices and select a recently seen tab.');
    if ([...this.pending.values()].some(p=>p.target===target && !p.expired && !['completed','failed'].includes(p.result?.status) && (!['stop','abort'].includes(action) || p.action===action))) throw new Error('Wait for the previous command result, then Refresh.');
    const generation=this.generation, token=await this.auth();if(!this.fresh(generation))throw new Error('Devices disconnected.');
    const id=this.makeId(),createdAt=this.now(),expiresAt=createdAt+COMMAND_TTL;
    const command={schema:SCHEMA,type:'command',id,target,sender:this.id,action,createdAt,expiresAt};
    // Register before writing: an uncertain network response must not cause an
    // automatic resend with a second command ID.
    this.pending.set(id,{id,target,action,expiresAt,result:null});this.emit();
    try { await this.put(token,`command-${target}-${id}.json`,command,{create:true}); }
    catch(error){this.pending.get(id).uncertain=true;this.emit();throw error;}
    this.emit();return id;
  }
}
