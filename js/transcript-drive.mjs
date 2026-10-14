const GRAPH = 'https://graph.microsoft.com/v1.0';
const SCOPES = ['Files.ReadWrite.AppFolder'];
export const TRANSCRIPT_FOLDER = 'Transcripts';
const encode = encodeURIComponent;
const itemPath = id => `/me/drive/items/${encode(id)}`;
const isText = item => !!item.file && !item.folder && !item.remoteItem && /\.txt$/i.test(item.name || '');

export function uploadFilename(date = new Date()) {
  const pad = (n, width = 2) => String(n).padStart(width, '0');
  return `${date.getFullYear()}-${pad(date.getMonth() + 1)}-${pad(date.getDate())}_${pad(date.getHours())}-${pad(date.getMinutes())}-${pad(date.getSeconds())}-${pad(date.getMilliseconds(), 3)}.txt`;
}

function interactionRequired(error) {
  return error?.name === 'InteractionRequiredAuthError' ||
    /^(interaction_required|consent_required|login_required|no_tokens_found)$/.test(error?.errorCode || '');
}

function checkChild(item, parentId) {
  if (!item?.id || item.id === parentId || item.parentReference?.id !== parentId || item.remoteItem) {
    throw new Error('OneDrive returned an item outside the expected folder. No further files were changed.');
  }
}

function archiveName(name) {
  // An archive must never contain absolute paths or traversal segments.
  if (typeof name !== 'string' || !name || name === '.' || name === '..' || /[\\/\u0000-\u001f]/.test(name)) {
    throw new Error('OneDrive returned an unsupported filename.');
  }
  return name;
}

export class TranscriptDrive {
  constructor({ client, linkedAccount = () => null, fetcher = fetch, now = () => new Date(),
    zipFactory = () => new globalThis.JSZip() }) {
    this.client = client; this.linkedAccount = linkedAccount;
    this.fetcher = fetcher.bind(globalThis); this.now = now; this.zipFactory = zipFactory;
    this.account = null;
  }

  async token() {
    // Reuse Whisper-clone's MSAL client, but don't link/unlink mail, change its
    // polling timestamps, or request broader access to the user's Drive.
    const auth = await this.client();
    const accounts = auth.getAllAccounts();
    const account = this.linkedAccount() ||
      accounts.find(a => a.homeAccountId === this.account?.homeAccountId) ||
      (accounts.length === 1 ? accounts[0] : null);
    let result;
    if (account) {
      try { result = await auth.acquireTokenSilent({ scopes: SCOPES, account }); }
      catch (error) {
        if (!interactionRequired(error)) throw error;
        result = await auth.acquireTokenPopup({ scopes: SCOPES, account });
      }
    } else {
      result = await auth.loginPopup({ scopes: SCOPES, prompt: 'select_account' });
    }
    if (!result?.accessToken || !result.account) throw new Error('Microsoft sign-in did not complete. Try the Drive button again.');
    if (account && result.account.homeAccountId !== account.homeAccountId) {
      throw new Error('Use the same Microsoft account that is linked to this app.');
    }
    this.account = result.account;
    return result.accessToken;
  }

  async request(token, path, options = {}) {
    const url = new URL(path.startsWith('/') ? `${GRAPH}${path}` : path);
    if (url.origin !== 'https://graph.microsoft.com' || !url.pathname.startsWith('/v1.0/me/drive/')) {
      throw new Error('Invalid OneDrive response URL.');
    }
    const headers = new Headers(options.headers || {});
    headers.set('Authorization', `Bearer ${token}`);
    const response = await this.fetcher(url.href, {
      ...options, headers, cache: 'no-store', signal: AbortSignal.timeout(60000),
    });
    if (!response.ok) {
      const error = new Error(response.status === 403 ?
        'OneDrive access was denied. Approve access to this app’s folder when Microsoft asks.' :
        response.status === 401 ? 'Microsoft sign-in expired. Try the Drive button again.' :
        response.status === 412 ? 'A file changed during the operation. Try again.' :
        `OneDrive request failed (${response.status}). Try again.`);
      error.status = response.status; throw error;
    }
    return response;
  }

  async folder(token, create = false) {
    const root = await (await this.request(token, '/me/drive/special/approot?$select=id,folder')).json();
    if (!root?.id || !root.folder) throw new Error('This Microsoft account has no available OneDrive app folder.');
    const path = `${itemPath(root.id)}:/${TRANSCRIPT_FOLDER}?$select=id,name,folder,remoteItem,parentReference`;
    const read = async () => (await this.request(token, path)).json();
    let folder;
    try { folder = await read(); }
    catch (error) {
      if (error.status !== 404) throw error;
      if (!create) return null;
      try {
        folder = await (await this.request(token, `${itemPath(root.id)}/children`, {
          method: 'POST', headers: { 'Content-Type': 'application/json' },
          body: JSON.stringify({ name: TRANSCRIPT_FOLDER, folder: {}, '@microsoft.graph.conflictBehavior': 'fail' }),
        })).json();
      } catch (error) {
        // Another tab/device may have created the folder in the meantime.
        if (error.status !== 409) throw error;
        folder = await read();
      }
    }
    checkChild(folder, root.id);
    if (!folder.folder || folder.name !== TRANSCRIPT_FOLDER) throw new Error('The OneDrive Transcripts location is not a folder.');
    return folder;
  }

  async children(token, folderId) {
    const endpoint = `${GRAPH}${itemPath(folderId)}/children`;
    let next = `${endpoint}?$select=id,name,file,folder,remoteItem,parentReference,createdDateTime,eTag&$top=200`;
    const result = [], pages = new Set(), ids = new Set();
    while (next) {
      const url = new URL(next);
      // Paging cannot redirect our token or broaden the listing to another folder.
      if (url.origin !== 'https://graph.microsoft.com' || url.pathname !== new URL(endpoint).pathname || pages.has(next)) {
        throw new Error('Invalid OneDrive folder pagination.');
      }
      pages.add(next);
      const page = await (await this.request(token, next)).json();
      if (!Array.isArray(page.value)) throw new Error('Invalid OneDrive folder listing.');
      for (const item of page.value) {
        checkChild(item, folderId);
        if (ids.has(item.id)) throw new Error('A OneDrive folder changed while being listed. Try again.');
        ids.add(item.id); result.push(item);
      }
      next = page['@odata.nextLink'];
    }
    return result;
  }

  async upload(text) {
    if (typeof text !== 'string' || !text.trim()) throw new Error('The transcript is empty.');
    const token = await this.token();
    const folder = await this.folder(token, true);
    // Use the upload time, local to this computer, with milliseconds to avoid
    // collisions. Explicitly fail rather than overwrite an existing file.
    const name = uploadFilename(this.now());
    await this.request(token, `${itemPath(folder.id)}:/${encode(name)}:/content?@microsoft.graph.conflictBehavior=fail`, {
      method: 'PUT', headers: { 'Content-Type': 'text/plain; charset=utf-8' }, body: text,
    });
    return name;
  }

  async fileBytes(token, item, parentId) {
    const fresh = await (await this.request(token, `${itemPath(item.id)}?$select=id,name,file,folder,remoteItem,parentReference,eTag,@microsoft.graph.downloadUrl`)).json();
    checkChild(fresh, parentId);
    if (!fresh.file || fresh.folder || fresh.name !== item.name || (item.eTag && fresh.eTag !== item.eTag)) {
      throw new Error('A OneDrive file changed during the download. Try Imp. Drive again.');
    }
    const url = new URL(fresh['@microsoft.graph.downloadUrl']);
    if (url.protocol !== 'https:' || url.username || url.password) throw new Error('Invalid OneDrive download URL.');
    // Browser /content requests redirect after a CORS preflight. Microsoft's
    // preauthenticated URL avoids that; never send the Graph token to it.
    const response = await this.fetcher(url.href, { cache: 'no-store', credentials: 'omit', signal: AbortSignal.timeout(60000) });
    if (!response.ok) throw new Error(`OneDrive file download failed (${response.status}). Try Imp. Drive again.`);
    return new Uint8Array(await response.arrayBuffer());
  }

  async exportZip(onProgress = () => {}) {
    const token = await this.token();
    const folder = await this.folder(token);
    const zip = this.zipFactory(), texts = [], seen = new Set();
    const archiveRoot = zip.folder(TRANSCRIPT_FOLDER);
    const visit = async (folderId, prefix = '') => {
      if (seen.has(folderId)) throw new Error('Invalid OneDrive folder hierarchy.');
      seen.add(folderId);
      const items = await this.children(token, folderId);
      // Reserve COMPLETE.txt for the generated combination; preserve an existing
      // same-named source file under a distinct name inside the downloaded copy.
      const names = new Set(items.map(item => item.name.toLowerCase()));
      for (const item of items) {
        let name = archiveName(item.name);
        if (!prefix && name.toLowerCase() === 'complete.txt') {
          let index = 1;
          do { name = `COMPLETE-original-${index++}.txt`; } while (names.has(name.toLowerCase()));
        }
        const path = `${prefix}${name}`;
        if (item.folder) {
          archiveRoot.folder(path);
          await visit(item.id, `${path}/`);
        } else if (item.file) {
          onProgress(`Downloading ${item.name}…`);
          const bytes = await this.fileBytes(token, item, folderId);
          archiveRoot.file(path, bytes);
          if (isText(item)) texts.push({ path, created: Date.parse(item.createdDateTime) || 0, text: new TextDecoder().decode(bytes) });
        } else { throw new Error('The Transcripts folder contains an unsupported OneDrive item.'); }
      }
    };
    if (folder) await visit(folder.id);
    texts.sort((a, b) => a.created - b.created || a.path.localeCompare(b.path));
    archiveRoot.file('COMPLETE.txt', texts.map((entry, index) => `text ${index + 1}:\n"${entry.text}"`).join('\n\n--\n\n'));
    onProgress('Creating ZIP…');
    const blob = await zip.generateAsync({ type: 'blob', compression: 'DEFLATE', compressionOptions: { level: 6 } });
    return { blob, name: `${TRANSCRIPT_FOLDER}_${uploadFilename(this.now()).replace(/\.txt$/, '')}.zip`, count: texts.length };
  }

  async clear(confirm, onProgress = () => {}) {
    const token = await this.token();
    const folder = await this.folder(token);
    if (!folder) return { count: 0, cancelled: false };
    // Only direct .txt files qualify. Never delete the folder, subfolders,
    // non-text files, or anything else in the application's root.
    const files = (await this.children(token, folder.id)).filter(isText);
    if (!files.length) return { count: 0, cancelled: false };
    if (!await confirm(files.length)) return { count: 0, cancelled: true };
    let count = 0;
    try {
      for (const item of files) {
        if (!item.eTag) throw new Error('A OneDrive file has no version information. Try again.');
        const fresh = await (await this.request(token, `${itemPath(item.id)}?$select=id,name,file,folder,remoteItem,parentReference,eTag`)).json();
        checkChild(fresh, folder.id);
        if (!isText(fresh) || fresh.name !== item.name || fresh.eTag !== item.eTag) {
          throw new Error('A file changed during clearing. Try Clear Drive again.');
        }
        onProgress(`Deleting ${count + 1} of ${files.length}…`);
        await this.request(token, itemPath(item.id), { method: 'DELETE', headers: { 'If-Match': item.eTag } });
        count++;
      }
    } catch (error) { throw new Error(`Deleted ${count} of ${files.length} text files. ${error.message}`); }
    return { count, cancelled: false };
  }
}
