import { CONFIG } from './config.mjs';
const SCOPES = ['User.Read', 'Mail.Read'];
const GRAPH = 'https://graph.microsoft.com/v1.0';
const ageLimit = 120000;
const normalize = value => String(value || '').trim().toLowerCase();

export function parseCommand(message, ownAddresses, linkedAt, now = Date.now()) {
  const received = Date.parse(message.receivedDateTime);
  if (!message.id || !Number.isFinite(received) || received < linkedAt ||
      received < now - ageLimit || received > now + 30000 || String(message.subject || '').trim()) return null;
  const from = normalize(message.from?.emailAddress?.address);
  const sender = normalize(message.sender?.emailAddress?.address || from);
  const recipients = message.toRecipients || [];
  if (!ownAddresses.has(from) || !ownAddresses.has(sender) ||
      !recipients.some(recipient => ownAddresses.has(normalize(recipient.emailAddress?.address)))) return null;
  let body = message.body?.content || '';
  if (normalize(message.body?.contentType) === 'html') {
    body = new DOMParser().parseFromString(body, 'text/html').body.textContent;
  }
  const command = normalize(body).replace(/\s+/g, ' ');
  const match = /^(start|pause|resume|stop)(?: recording)?$/.exec(command);
  return match?.[1] || null;
}

export class MailControl {
  constructor({ onStatus = () => {}, onCommand, auth, fetcher = fetch, now = Date.now } = {}) {
    this.onStatus = onStatus; this.onCommand = onCommand;
    this.auth = auth; this.fetcher = fetcher; this.now = now;
    this.account = null; this.addresses = new Set(); this.seen = new Map();
    this.active = false; this.generation = 0; this.timer = null;
    this.abort = null; this.releaseLock = null; this.clientPromise = null;
  }
  client() {
    if (this.auth) return Promise.resolve(this.auth);
    if (!this.clientPromise) this.clientPromise = (async () => {
      if (!globalThis.msal?.PublicClientApplication) throw new Error('Microsoft sign-in could not be loaded. Reload the page.');
      const auth = new msal.PublicClientApplication({
        auth: { clientId: CONFIG.microsoftClientId, authority: CONFIG.microsoftAuthority,
          redirectUri: new URL('../', import.meta.url).href, navigateToLoginRequestUrl: false },
        cache: { cacheLocation: 'sessionStorage', temporaryCacheLocation: 'sessionStorage',
          storeAuthStateInCookie: false, cacheMigrationEnabled: false },
        system: { loggerOptions: { piiLoggingEnabled: false, loggerCallback: () => {} } },
      });
      await auth.initialize(); return auth;
    })().catch(error => { this.clientPromise = null; throw error; });
    return this.clientPromise;
  }
  async token() {
    const auth = await this.client();
    return (await auth.acquireTokenSilent({ scopes: SCOPES, account: this.account })).accessToken;
  }
  async request(path, token) {
    const url = new URL(path, `${GRAPH}/`);
    // Pagination links cannot redirect the account's token to another host.
    if (url.origin !== 'https://graph.microsoft.com' || !url.pathname.startsWith('/v1.0/')) throw new Error('Invalid mailbox response.');
    const response = await this.fetcher(url.href, {
      cache: 'no-store', signal: this.abort ? AbortSignal.any([this.abort.signal, AbortSignal.timeout(30000)]) : AbortSignal.timeout(30000),
      headers: { Authorization: `Bearer ${token}`, Prefer: 'outlook.body-content-type="text", IdType="ImmutableId"' },
    });
    if (!response.ok) {
      const error = new Error(`Email connection failed (${response.status}).`);
      error.status = response.status;
      const retry = response.headers.get('Retry-After');
      error.retryMs = retry && Number.isFinite(Number(retry)) ? Math.max(2000, Number(retry) * 1000) : 10000;
      throw error;
    }
    return response.json();
  }
  async link() {
    if (this.active) return;
    const generation = ++this.generation;
    this.onStatus('Linking…');
    const auth = await this.client();
    const login = await auth.loginPopup({ scopes: SCOPES, prompt: 'select_account' });
    if (generation !== this.generation) return;
    this.account = login.account;
    if (!this.account) throw new Error('Microsoft did not return an account.');
    this.abort = new AbortController();
    const profile = await this.request('me?$select=id,mail,userPrincipalName', login.accessToken);
    if (generation !== this.generation) return;
    this.addresses = new Set([profile.mail, profile.userPrincipalName, this.account.username].map(normalize).filter(address => address.includes('@')));
    if (!this.addresses.size) throw new Error('This account has no email address.');
    if (navigator.locks) {
      // Only one linked tab per mailbox on this origin. No persistent lease.
      const obtained = await new Promise((resolve, reject) => {
        navigator.locks.request(`whisper-clone-mail-${profile.id}`, { ifAvailable: true }, async lock => {
          if (!lock) { resolve(false); return; }
          if (generation !== this.generation) { resolve(false); return; }
          await new Promise(release => { this.releaseLock = release; resolve(true); });
        }).catch(reject);
      });
      if (!obtained) throw new Error('Email monitoring is already linked in another tab.');
    }
    // Start at consent completion; historical email never starts the recorder.
    this.linkedAt = this.now(); this.seen.clear(); this.active = true;
    this.onStatus('Linked'); this.schedule(0, generation);
  }
  schedule(delay, generation) {
    if (this.active && generation === this.generation) this.timer = setTimeout(() => this.poll(generation), delay);
  }
  async poll(generation = this.generation) {
    if (!this.active || generation !== this.generation) return;
    let delay = CONFIG.emailPollMs;
    const fresh = () => this.active && generation === this.generation;
    try {
      const token = await this.token();
      if (!fresh()) return;
      const cutoff = Math.max(this.linkedAt, this.now() - ageLimit);
      const params = new URLSearchParams({
        '$filter': `receivedDateTime ge ${new Date(cutoff).toISOString()}`,
        '$orderby': 'receivedDateTime desc', '$top': '50',
        '$select': 'id,subject,body,from,sender,toRecipients,receivedDateTime',
      });
      let next = `${GRAPH}/me/mailFolders/inbox/messages?${params}`, messages = [];
      while (next && fresh()) {
        const page = await this.request(next, token);
        messages.push(...(page.value || [])); next = page['@odata.nextLink'];
      }
      // Apply commands in receipt order, including commands received during
      // an earlier recording transition. The next poll never overlaps this one.
      messages.sort((a, b) => Date.parse(a.receivedDateTime) - Date.parse(b.receivedDateTime));
      let commandFailed = false;
      for (const message of messages) {
        if (!fresh()) return;
        if (this.seen.has(message.id)) continue;
        const action = parseCommand(message, this.addresses, this.linkedAt, this.now());
        this.seen.set(message.id, Date.parse(message.receivedDateTime));
        if (action) {
          try { await this.onCommand(action); }
          catch { commandFailed = true; this.onStatus('Command failed'); }
        }
      }
      for (const [id, time] of this.seen) if (time < cutoff) this.seen.delete(id);
      if (fresh() && !commandFailed) this.onStatus('Linked');
    } catch (error) {
      if (!fresh()) return;
      if (error.status === 401 || error.status === 403 || error.name === 'InteractionRequiredAuthError' || /interaction_required|login_required|consent_required/.test(error.errorCode || '')) {
        this.unlink(); this.onStatus('Link again'); return;
      }
      delay = error.retryMs || 10000;
      this.onStatus('Reconnecting…');
    } finally { this.schedule(delay, generation); }
  }
  unlink() {
    this.active = false; this.generation++;
    clearTimeout(this.timer); this.abort?.abort(); this.abort = null;
    this.releaseLock?.(); this.releaseLock = null;
    this.account = null; this.addresses.clear(); this.seen.clear();
    this.onStatus('Not linked');
    // Clear this app's MSAL tokens/accounts, without clearing any other app.
    this.clientPromise?.then(auth => auth.clearCache()).catch(() => {});
  }
}
