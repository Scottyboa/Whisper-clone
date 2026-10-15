import test from 'node:test';
import assert from 'node:assert/strict';
import { createRequire } from 'node:module';
import { TranscriptDrive, uploadFilename } from '../js/transcript-drive.mjs';
const JSZip = createRequire(import.meta.url)('../vendor/jszip/jszip.min.js');
const account = { homeAccountId: 'personal-account' };
const root = { id: 'app-root', folder: {} };
const folder = { id: 'transcripts', name: 'Transcripts', folder: {}, parentReference: { id: root.id } };
const file = (id, name, parent = folder.id, extra = {}) => ({
  id, name, file: {}, parentReference: { id: parent }, eTag: `"${id}-1"`,
  createdDateTime: '2026-10-14T10:00:00Z', ...extra,
});
const json = (body, status = 200) => new Response(JSON.stringify(body), { status, headers: { 'Content-Type': 'application/json' } });

function harness({ missing = false, files = [], nested = {}, contents = {}, pages = {}, intercept } = {}) {
  const calls = [], authCalls = [];
  const auth = {
    getAllAccounts: () => [account],
    acquireTokenSilent: async options => { authCalls.push(['silent', options]); return { account, accessToken: 'graph-token' }; },
    acquireTokenPopup: async options => { authCalls.push(['popup', options]); return { account, accessToken: 'graph-token' }; },
    loginPopup: async options => { authCalls.push(['login', options]); return { account, accessToken: 'graph-token' }; },
  };
  const items = new Map([...files, ...Object.values(nested).flat(), ...Object.values(pages).flat()].map(item => [item.id, item]));
  const fetcher = async (input, options = {}) => {
    const url = new URL(input), method = options.method || 'GET', headers = new Headers(options.headers);
    calls.push({ url, method, headers, body: options.body });
    const override = await intercept?.({ url, method, headers, options, calls, items });
    if (override) return override;
    if (url.hostname === 'downloads.example') {
      assert.equal(headers.has('Authorization'), false);
      assert.equal(options.credentials, 'omit');
      return new Response(contents[decodeURIComponent(url.pathname.slice(1))] || '');
    }
    assert.equal(url.hostname, 'graph.microsoft.com');
    assert.equal(headers.get('Authorization'), 'Bearer graph-token');
    const p = decodeURIComponent(url.pathname);
    if (p === '/v1.0/me/drive/special/approot') return json(root);
    if (p === '/v1.0/me/drive/items/app-root:/Transcripts') return missing ? json({}, 404) : json(folder);
    if (p === '/v1.0/me/drive/items/app-root/children' && method === 'POST') { missing = false; return json(folder, 201); }
    if (p.includes(':/content') && method === 'PUT') {
      assert.equal(url.searchParams.get('@microsoft.graph.conflictBehavior'), 'fail');
      return json({ id: 'uploaded' }, 201);
    }
    const list = /^\/v1.0\/me\/drive\/items\/([^/]+)\/children$/.exec(p);
    if (list) {
      const id = list[1];
      if (url.searchParams.has('$skiptoken')) return json({ value: pages[id] || [] });
      const value = id === folder.id ? files : nested[id] || [];
      return json({ value, ...(pages[id] ? { '@odata.nextLink': `${url.origin}${url.pathname}?$skiptoken=next` } : {}) });
    }
    const match = /^\/v1.0\/me\/drive\/items\/([^/]+)$/.exec(p);
    if (match) {
      const item = items.get(match[1]);
      if (!item) return json({}, 404);
      if (method === 'DELETE') { items.delete(item.id); return new Response(null, { status: 204 }); }
      // OneDrive may omit this annotation when $select filters metadata.
      // Mimic that behavior so ZIP tests exercise the actual download request.
      return json({ ...item, ...(!url.searchParams.has('$select') ?
        { '@microsoft.graph.downloadUrl': `https://downloads.example/${encodeURIComponent(item.id)}` } : {}) });
    }
    throw new Error(`Unexpected request: ${method} ${url}`);
  };
  const drive = new TranscriptDrive({ client: async () => auth, fetcher,
    now: () => new Date(2026, 9, 14, 12, 3, 4, 123), zipFactory: () => new JSZip() });
  return { drive, calls, auth, authCalls, items };
}

test('timestamp names include the local upload date, time and milliseconds', () => {
  assert.equal(uploadFilename(new Date(2026, 9, 14, 12, 3, 4, 123)), '2026-10-14_12-03-04-123.txt');
});

test('upload snapshots exact Unicode text, creates only the dedicated folder and refuses replacement', async () => {
  const h = harness({ missing: true });
  assert.equal(await h.drive.upload('日本語\nÆøå\n "quoted" '), '2026-10-14_12-03-04-123.txt');
  const post = h.calls.find(c => c.method === 'POST');
  assert.deepEqual(JSON.parse(post.body), { name: 'Transcripts', folder: {}, '@microsoft.graph.conflictBehavior': 'fail' });
  const put = h.calls.find(c => c.method === 'PUT');
  assert.equal(put.body, '日本語\nÆøå\n "quoted" ');
  assert.equal(put.headers.get('Content-Type'), 'text/plain; charset=utf-8');
  assert.deepEqual(h.authCalls[0][1].scopes, ['Files.ReadWrite.AppFolder']);
  assert.ok(h.calls.every(c => c.url.pathname.includes('/special/approot') || c.url.pathname.includes('/items/app-root') || c.url.pathname.includes('/items/transcripts')));
});

test('empty transcript does not authenticate or write', async () => {
  const h = harness(); await assert.rejects(h.drive.upload(' \n\t '), /empty/);
  assert.equal(h.calls.length, 0); assert.equal(h.authCalls.length, 0);
});

test('existing folder is reused; a racing folder creation is resolved without creating siblings', async () => {
  let reads = 0;
  const h = harness({ intercept: ({url, method}) => {
    if (url.pathname.includes('app-root:/Transcripts') && ++reads === 1) return json({}, 404);
    if (method === 'POST') return json({}, 409);
  } });
  await h.drive.upload('text'); assert.equal(h.calls.filter(c => c.method === 'POST').length, 1);
  assert.equal(h.calls.filter(c => c.method === 'PUT').length, 1);
});

test('ZIP titles text copies, preserves binary files and combines text chronologically', async () => {
  const late = file('late', '2026-10-14_12-00.txt', folder.id, {createdDateTime:'2026-10-14T12:00:00Z'});
  const early = file('early', '2026-10-14_10-00.txt');
  const sub = { id: 'sub', name: 'Subfolder', folder: {}, parentReference: { id: folder.id } };
  const bin = file('binary', 'image.bin');
  const h = harness({ files:[late, sub, bin], pages:{transcripts:[early]},
    nested:{sub:[file('nested', 'nested.txt', 'sub', {createdDateTime:'2026-10-14T11:00:00Z'})]},
    contents:{early:'First\n日本語',nested:'Second',late:'Third',binary:new Uint8Array([0,1,254,255])} });
  const result = await h.drive.exportZip();
  assert.equal(result.count,3);
  const zip = await JSZip.loadAsync(await result.blob.arrayBuffer(), {checkCRC32:true});
  assert.equal(await zip.file('Transcripts/2026-10-14_10-00.txt').async('string'),'2026-10-14_10-00.txt\n\nFirst\n日本語');
  assert.equal(await zip.file('Transcripts/Subfolder/nested.txt').async('string'),'nested.txt\n\nSecond');
  assert.deepEqual([...await zip.file('Transcripts/image.bin').async('uint8array')],[0,1,254,255]);
  assert.equal(await zip.file('Transcripts/COMPLETE.txt').async('string'),'COMPLETE.txt\n\n2026-10-14_10-00.txt\n\nFirst\n日本語\n\n--\n\nnested.txt\n\nSecond\n\n--\n\n2026-10-14_12-00.txt\n\nThird');
  assert.equal(result.completeText,await zip.file('Transcripts/COMPLETE.txt').async('string'));
  assert.equal(h.calls.filter(c=>c.method!=='GET').length,0);
});

test('source COMPLETE.txt is preserved rather than silently overwritten in ZIP', async () => {
  const h = harness({files:[file('complete','COMPLETE.txt'),file('reserved','COMPLETE-original-1.txt')],contents:{complete:'old',reserved:'keep'}});
  const {blob}=await h.drive.exportZip(); const zip=await JSZip.loadAsync(await blob.arrayBuffer());
  assert.equal(await zip.file('Transcripts/COMPLETE-original-2.txt').async('string'),'COMPLETE-original-2.txt\n\nold');
  assert.equal(await zip.file('Transcripts/COMPLETE-original-1.txt').async('string'),'COMPLETE-original-1.txt\n\nkeep');
  assert.match(await zip.file('Transcripts/COMPLETE.txt').async('string'),/old/);
});

test('file downloads request default metadata so OneDrive can include its download annotation', async () => {
  const h=harness({files:[file('text','a.txt')],contents:{text:'Saved transcript'}});
  const {blob}=await h.drive.exportZip();const zip=await JSZip.loadAsync(await blob.arrayBuffer());
  assert.equal(await zip.file('Transcripts/a.txt').async('string'),'a.txt\n\nSaved transcript');
  const metadata=h.calls.find(c=>c.url.pathname.endsWith('/items/text'));
  assert.equal(metadata.url.search,'');
});

test('missing or malformed download links give a useful error without fetching or mutating files', async () => {
  for(const link of [undefined,null,'','   ','not a url']) {
    const h=harness({files:[file('text','a.txt')],intercept:({url,items})=>
      url.pathname.endsWith('/items/text')?json({...items.get('text'),'@microsoft.graph.downloadUrl':link}):null});
    await assert.rejects(h.drive.exportZip(),error=>{
      assert.equal(error.name,'Error');assert.match(error.message,/download link for a\.txt/);return true;
    });
    assert.ok(h.calls.every(c=>c.url.hostname==='graph.microsoft.com'&&c.method==='GET'));
  }
});

test('download links must use HTTPS and contain no embedded credentials', async () => {
  for(const link of ['http://downloads.example/text','javascript:alert(1)','https://user:pass@downloads.example/text']) {
    const h=harness({files:[file('text','a.txt')],intercept:({url,items})=>
      url.pathname.endsWith('/items/text')?json({...items.get('text'),'@microsoft.graph.downloadUrl':link}):null});
    await assert.rejects(h.drive.exportZip(),/Invalid OneDrive download URL/);
    assert.ok(h.calls.every(c=>c.url.hostname==='graph.microsoft.com'&&c.method==='GET'));
  }
});

test('COMPLETE.txt sorts timestamps correctly with different fractional seconds or offsets', async () => {
  const h=harness({files:[
    file('late','a.txt',folder.id,{createdDateTime:'2026-10-14T10:00:00.900Z'}),
    file('early','b.txt',folder.id,{createdDateTime:'2026-10-14T12:00:00+02:00'})
  ],contents:{early:'early',late:'late'}});
  const {blob}=await h.drive.exportZip();const zip=await JSZip.loadAsync(await blob.arrayBuffer());
  assert.equal(await zip.file('Transcripts/COMPLETE.txt').async('string'),'COMPLETE.txt\n\nb.txt\n\nearly\n\n--\n\na.txt\n\nlate');
});

test('empty or missing folder produces a titled COMPLETE.txt without creating Transcripts', async () => {
  const h=harness({missing:true});const {blob,count}=await h.drive.exportZip();
  const zip=await JSZip.loadAsync(await blob.arrayBuffer());
  assert.equal(count,0);assert.equal(await zip.file('Transcripts/COMPLETE.txt').async('string'),'COMPLETE.txt\n\n');
  assert.equal(h.calls.filter(c=>c.method!=='GET').length,0);
});

test('Clear deletes only direct .txt files after confirmation, with version guards', async () => {
  const text=file('text','timestamp.txt');const extra=file('backup','whisper-keys-backup.enc.json');
  const sub={id:'sub',name:'Nested.txt',folder:{},parentReference:{id:folder.id}};
  const h=harness({files:[text,extra,sub],nested:{sub:[file('nested','keep.txt','sub')]}});
  let confirmed=0;const result=await h.drive.clear(count=>{confirmed=count;return true;});
  assert.equal(confirmed,1);assert.deepEqual(result,{count:1,cancelled:false});
  const deletes=h.calls.filter(c=>c.method==='DELETE');assert.equal(deletes.length,1);
  assert.equal(deletes[0].url.pathname,'/v1.0/me/drive/items/text');assert.equal(deletes[0].headers.get('If-Match'),'"text-1"');
  assert.ok(h.items.has('backup'));assert.ok(h.items.has('sub'));assert.ok(h.items.has('nested'));
});

test('cancel or missing folder sends no delete requests', async () => {
  const h=harness({files:[file('text','a.txt')]});
  assert.deepEqual(await h.drive.clear(()=>false),{count:0,cancelled:true});
  assert.equal(h.calls.filter(c=>c.method==='DELETE').length,0);
  const missing=harness({missing:true});assert.deepEqual(await missing.drive.clear(()=>assert.fail()),{count:0,cancelled:false});
});

test('Clear stops if a file is moved, renamed or replaced and reports partial progress', async () => {
  const h=harness({files:[file('first','a.txt'),file('second','b.txt')],intercept:({url,method,items})=>{
    if(url.pathname.endsWith('/second')&&method==='GET')return json({...items.get('second'),parentReference:{id:'other-folder'}});
  }});
  await assert.rejects(h.drive.clear(()=>true),/Deleted 1 of 2/);
  assert.deepEqual(h.calls.filter(c=>c.method==='DELETE').map(c=>c.url.pathname),['/v1.0/me/drive/items/first']);
});

test('pagination cannot leak tokens, list another folder or loop', async () => {
  for(const next of ['https://evil.example/steal','https://graph.microsoft.com/v1.0/me/drive/root/children']) {
    const h=harness({intercept:({url})=>url.pathname.endsWith('/transcripts/children')?json({value:[],'@odata.nextLink':next}):null});
    await assert.rejects(h.drive.clear(()=>true),/pagination/);
    assert.ok(h.calls.every(c=>c.url.hostname==='graph.microsoft.com'));
  }
});

test('folder or listing outside the app folder aborts without mutations', async () => {
  const h=harness({intercept:({url})=>url.pathname.includes('app-root:/Transcripts')?json({...folder,parentReference:{id:'different-root'}}):null});
  await assert.rejects(h.drive.upload('text'),/outside/);assert.equal(h.calls.filter(c=>c.method!=='GET').length,0);
  const listing=harness({files:[file('outside','secret.txt','other-folder')]});
  await assert.rejects(listing.drive.clear(()=>true),/outside/);assert.equal(listing.calls.filter(c=>c.method==='DELETE').length,0);
});

test('archive refuses traversal filenames and does not send Graph token to download hosts', async () => {
  const h=harness({files:[file('unsafe','../secret.txt')]});await assert.rejects(h.drive.exportZip(),/filename/);
  assert.ok(h.calls.every(c=>c.url.hostname==='graph.microsoft.com'));
});

test('consent uses the linked account and only Drive scope; unrelated errors do not open a popup', async () => {
  const h=harness();h.drive.linkedAccount=()=>account;
  h.auth.acquireTokenSilent=async options=>{h.authCalls.push(['silent',options]);throw Object.assign(new Error(),{name:'InteractionRequiredAuthError'});};
  await h.drive.upload('text');assert.deepEqual(h.authCalls.map(c=>c[0]),['silent','popup']);
  assert.equal(h.authCalls[1][1].account,account);assert.deepEqual(h.authCalls[1][1].scopes,['Files.ReadWrite.AppFolder']);
  const failed=harness();failed.auth.acquireTokenSilent=async()=>{throw new Error('network down');};
  await assert.rejects(failed.drive.upload('text'),/network down/);assert.equal(failed.authCalls.length,0);
});

test('unlinked user can sign in for Drive alone; an account mismatch is rejected', async () => {
  const h=harness();h.auth.getAllAccounts=()=>[];await h.drive.upload('text');assert.equal(h.authCalls[0][0],'login');
  const other=harness();other.auth.acquireTokenSilent=async()=>({accessToken:'graph-token',account:{homeAccountId:'different'}});
  await assert.rejects(other.drive.upload('text'),/same Microsoft account/);assert.equal(other.calls.length,0);
});

test('automatic upload keeps its recording filename and never opens a background consent popup', async () => {
  const name='2026-10-15_10-00-00-000_to_2026-10-15_11-00-00-000_VAD-23m45s.txt';
  const h=harness();
  assert.equal(await h.drive.upload('Speaker 1: 日本語', {name,interactive:false,account}),name);
  const put=h.calls.find(c=>c.method==='PUT');
  assert.equal(decodeURIComponent(put.url.pathname),`/v1.0/me/drive/items/transcripts:/${name}:/content`);
  assert.equal(put.body,'Speaker 1: 日本語'); assert.deepEqual(h.authCalls.map(c=>c[0]),['silent']);
  const failed=harness(); failed.auth.acquireTokenSilent=async()=>{throw {name:'InteractionRequiredAuthError'};};
  await assert.rejects(failed.drive.upload('text',{name,interactive:false,account}),/needs sign-in or consent/);
  assert.equal(failed.calls.length,0); assert.equal(failed.authCalls.length,0);
  const noAccount=harness(); noAccount.auth.getAllAccounts=()=>[];
  await assert.rejects(noAccount.drive.upload('text',{interactive:false}),/Link Microsoft/);
  assert.equal(noAccount.authCalls.length,0);
});

test('automatic upload refuses an account switch and invalid filenames before any Drive writes', async () => {
  const h=harness();h.drive.linkedAccount=()=>({homeAccountId:'other-account'});
  await assert.rejects(h.drive.upload('text',{account,interactive:false}),/account changed/);
  assert.equal(h.calls.length,0); assert.equal(h.authCalls.length,0);
  for (const name of ['../outside.txt','folder/file.txt','bad:name.txt','file.json','COMPLETE.txt/child']) {
    await assert.rejects(h.drive.upload('text',{name}),/filename/);
  }
  assert.equal(h.calls.length,0);
});

test('paste-only COMPLETE generation matches ZIP text without constructing ZIP or fetching binary files',async()=>{
  const h=harness({files:[file('text','recording.txt'),file('binary','keep.bin')],contents:{text:'日本語\nSpeaker 1: Hello',binary:'binary bytes'}});
  const zipResult=await h.drive.exportZip();const zip=await JSZip.loadAsync(await zipResult.blob.arrayBuffer());
  h.calls.length=0;h.drive.zipFactory=()=>assert.fail('ZIP should not be constructed for paste-only');
  const pasteResult=await h.drive.exportZip(()=>{},{includeZip:false});
  assert.equal(pasteResult.blob,null);assert.equal(pasteResult.completeText,await zip.file('Transcripts/COMPLETE.txt').async('string'));
  assert.equal(pasteResult.count,1);assert.ok(h.calls.every(c=>!c.url.pathname.endsWith('/binary')));
  assert.ok(h.calls.every(c=>c.method==='GET'));
});
