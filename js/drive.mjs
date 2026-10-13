import { CONFIG } from './config.mjs';
const SCOPE = 'https://www.googleapis.com/auth/drive.appdata';
const SCHEMA = 'whisper.keys.google-drive.encrypted';
let googleReady;

export function loadGoogle() {
  if (globalThis.google?.accounts?.oauth2) return Promise.resolve();
  if (!googleReady) googleReady = new Promise((resolve, reject) => {
    const script = document.createElement('script');
    script.src = 'https://accounts.google.com/gsi/client'; script.async = true;
    const timer = setTimeout(() => { googleReady = null; script.remove(); reject(new Error('Drive sign-in could not be loaded.')); }, 20000);
    script.onload = () => { clearTimeout(timer); resolve(); };
    script.onerror = () => { clearTimeout(timer); googleReady = null; script.remove(); reject(new Error('Drive sign-in could not be loaded.')); };
    document.head.append(script);
  });
  return googleReady;
}

function googleToken() {
  if (!globalThis.google?.accounts?.oauth2) throw new Error('Drive sign-in is still loading. Try Import again.');
  return new Promise((resolve, reject) => {
    let finished = false;
    const timer = setTimeout(() => finish(new Error('Drive sign-in timed out.')), 120000);
    const finish = (error, token) => {
      if (finished) return; finished = true; clearTimeout(timer);
      error ? reject(error) : resolve(token);
    };
    const client = google.accounts.oauth2.initTokenClient({
      client_id: CONFIG.googleClientId, scope: SCOPE, prompt: 'select_account',
      callback: response => {
        if (response.error || !response.access_token) return finish(new Error('Drive sign-in failed.'));
        if (google.accounts.oauth2.hasGrantedAllScopes && !google.accounts.oauth2.hasGrantedAllScopes(response, SCOPE)) {
          return finish(new Error('Drive permission was not granted.'));
        }
        finish(null, response.access_token);
      },
      error_callback: () => finish(new Error('Drive sign-in was closed or blocked. Try Import again.')),
    });
    client.requestAccessToken();
  });
}

function bytes(value) { return Uint8Array.from(atob(value), char => char.charCodeAt(0)); }
export async function decryptKeyBackup(container, password) {
  if (container?.schema !== SCHEMA || container.version !== 1 || !container.encryption) {
    throw new Error('Unsupported key backup.');
  }
  const enc = container.encryption, iterations = Number(enc.iterations);
  if (enc.algorithm !== 'AES-256-GCM' || enc.kdf !== 'PBKDF2-SHA-256' ||
      !Number.isInteger(iterations) || iterations < 100000 || iterations > 1000000) {
    throw new Error('Invalid key backup encryption.');
  }
  try {
    const salt = bytes(enc.salt), iv = bytes(enc.iv), ciphertext = bytes(container.ciphertext);
    if (salt.length !== 16 || iv.length !== 12 || ciphertext.length > 2000000) throw new Error();
    const material = await crypto.subtle.importKey('raw', new TextEncoder().encode(password), 'PBKDF2', false, ['deriveKey']);
    const key = await crypto.subtle.deriveKey({ name: 'PBKDF2', hash: 'SHA-256', salt, iterations }, material, { name: 'AES-GCM', length: 256 }, false, ['decrypt']);
    const plain = await crypto.subtle.decrypt({ name: 'AES-GCM', iv, additionalData: new TextEncoder().encode(`${SCHEMA}:1`) }, key, ciphertext);
    const bundle = JSON.parse(new TextDecoder().decode(plain));
    const soniox = (bundle.data || bundle).soniox_api_key;
    if (typeof soniox !== 'string' || !soniox.trim()) throw new Error('No Soniox key in this backup.');
    return soniox.trim();
  } catch (error) {
    if (error.message === 'No Soniox key in this backup.') throw error;
    throw new Error('Incorrect password or damaged key backup.');
  }
}

export async function importSonioxKey(password) {
  // Called directly by the Import click so Google's popup retains activation.
  let token = await googleToken();
  const request = async url => {
    const response = await fetch(url, { headers: { Authorization: `Bearer ${token}` }, cache: 'no-store', signal: AbortSignal.timeout(30000) });
    if (!response.ok) throw new Error(`Drive request failed (${response.status}).`);
    return response;
  };
  try {
    const params = new URLSearchParams({ spaces: 'appDataFolder', q: "name = 'whisper-keys-backup.enc.json' and trashed = false", fields: 'files(id)', orderBy: 'modifiedTime desc', pageSize: '1' });
    const data = await (await request(`https://www.googleapis.com/drive/v3/files?${params}`)).json();
    const id = data.files?.[0]?.id;
    if (!id) throw new Error('No key backup found in Drive.');
    const raw = await (await request(`https://www.googleapis.com/drive/v3/files/${encodeURIComponent(id)}?alt=media`)).text();
    if (raw.length > 2000000) throw new Error('Key backup is too large.');
    return await decryptKeyBackup(JSON.parse(raw), password);
  } finally { token = ''; }
}
