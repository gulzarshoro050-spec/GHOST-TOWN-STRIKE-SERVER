#!/usr/bin/env node
'use strict';
/* =====================================================================================================
   GHOST TOWN STRIKE - MULTIPLAYER + MATCHMAKING SERVER
   Zero dependencies (plain Node 16+). Own tiny WebSocket implementation, so there is nothing to install.

   RUN IT          node mp-server.js                      (listens on :3001, WebSocket path /mp)
   ADD TO server.js  require('./mp-server').attach(httpServer)   (then it shares your port 3000, path /mp)

   ENVIRONMENT (all optional)
     MP_PORT=3001            port when started on its own (hosts that set PORT, like Render, are picked up automatically)
     ACCOUNT_URL=http://127.0.0.1:3000   your existing account server (used to check the login token and
                                          to read which paid guns the player really owns: GET /api/save)
     MP_FILL_SECONDS=30      how long matchmaking searches for real players before bots fill empty slots
     MP_COUNTDOWN_SECONDS=5  countdown once a lobby is full / the search time is up (votes lock at 0)
     MP_DEV=1                skip the account check (testing only: any token is accepted)

   WHAT IT DOES
     * matchmaking: players queue into a lobby; it runs until 10 players are found, and if the search time
       runs out the remaining slots are filled with the game's original AI bots (real players keep theirs)
     * map + mode voting: most votes wins; no votes or a tie -> the server picks randomly among the leaders
     * rooms: 10 slots (two teams of 5, or 10 solo fighters in Free For All), one human is the room "host"
       and runs the bots + round/objective flow; the server relays everything else and enforces who may
       send what. A player who leaves is replaced by a bot; if the host leaves, another human takes over.
     * paid guns: the loadout is checked against the account's real purchases before every round
   ===================================================================================================== */
const http = require('http'), https = require('https'), crypto = require('crypto');

const CFG = {
  port: +process.env.MP_PORT || +process.env.PORT || 3001,   // PORT: set by hosts like Render / Railway
  host: process.env.MP_HOST || '0.0.0.0',
  account: (process.env.ACCOUNT_URL || 'http://127.0.0.1:3000').replace(/\/+$/, ''),
  dev: process.env.MP_DEV === '1',
  fillMs: Math.max(2, +process.env.MP_FILL_SECONDS || 30) * 1000,
  countMs: Math.max(1, +process.env.MP_COUNTDOWN_SECONDS || 5) * 1000,
  loadoutFirstMs: Math.max(5, +process.env.MP_LOADOUT_SECONDS || 80) * 1000,   // first round: includes the loading screen
  loadoutNextMs: Math.max(5, +process.env.MP_NEXT_LOADOUT_SECONDS || 35) * 1000,
  proto: 1
};
const MAX = 10;
const MAPS = ['ghost', 'farm', 'old', 'facility'];
const MODES = ['cls', 'cap', 'bomb', 'ffa'];
const ROUNDS = { cls: 3, bomb: 3, ffa: 2, cap: 1 };
const PAID = [19, 12, 8, 18];                       // guns that must be bought (Crossbow, USP Silenced, Bolt Sniper, M82)
const DEF_LOADOUT = [4, 0, 1];                      // AK-47, Pistol G17, frag grenade
const NWEAP = 21, NGREN = 4;
const BOT_NAMES = ['you', 'alex', 'ben', 'cody', 'dana', 'rex', 'vic', 'ivan', 'mara', 'zed', 'finn', 'c4'];
const log = (...a) => console.log(new Date().toISOString().slice(11, 19), ...a);

// ------------------------------------------------------------------------------------------ WebSocket
class WS {
  constructor(sock) {
    this.s = sock; this.buf = Buffer.alloc(0); this.open = true; this.frag = []; this.fragLen = 0; this.onmsg = null; this.onclose = null;
    sock.setNoDelay(true); sock.setTimeout(0);
    sock.on('data', d => this._data(d)); sock.on('close', () => this._closed()); sock.on('error', () => this._closed());
  }
  _data(d) {
    this.buf = this.buf.length ? Buffer.concat([this.buf, d]) : d;
    while (this.open) {
      const b = this.buf; if (b.length < 2) return;
      const fin = !!(b[0] & 128), op = b[0] & 15, masked = !!(b[1] & 128); let len = b[1] & 127, o = 2;
      if (len === 126) { if (b.length < 4) return; len = b.readUInt16BE(2); o = 4; }
      else if (len === 127) { if (b.length < 10) return; if (b.readUInt32BE(2) !== 0) return this.close(1009); len = b.readUInt32BE(6); o = 10; }
      if (len > 65536) return this.close(1009);
      if (!masked) return this.close(1002);
      if (b.length < o + 4 + len) return;
      const mk = b.subarray(o, o + 4), p = Buffer.allocUnsafe(len);
      for (let i = 0; i < len; i++) p[i] = b[o + 4 + i] ^ mk[i & 3];
      this.buf = b.subarray(o + 4 + len);
      if (op >= 8) {                                  // control frames
        if (op === 8) { this.close(1000); return; }
        if (op === 9) this._frame(10, p);
        continue;
      }
      if (op === 1 || op === 2) { this.frag = []; this.fragLen = 0; this.fragOp = op; }
      if (op === 0 || op === 1 || op === 2) {
        this.frag.push(p); this.fragLen += len;
        if (this.fragLen > 131072) return this.close(1009);
        if (fin) { const all = this.frag.length === 1 ? this.frag[0] : Buffer.concat(this.frag); this.frag = []; this.fragLen = 0; if (this.fragOp === 1 && this.onmsg) { try { this.onmsg(all.toString('utf8')); } catch (e) { log('handler error', e && e.stack || e); } } }
      }
    }
  }
  _frame(op, p) {
    if (!this.open && op !== 8) return;
    const n = p.length; let h;
    if (n < 126) { h = Buffer.alloc(2); h[1] = n; } else if (n < 65536) { h = Buffer.alloc(4); h[1] = 126; h.writeUInt16BE(n, 2); } else { h = Buffer.alloc(10); h[1] = 127; h.writeUInt32BE(n, 6); }
    h[0] = 128 | op; try { this.s.write(Buffer.concat([h, p])); } catch (e) { }
  }
  send(str, critical) {
    if (!this.open) return;
    if (!critical && this.s.writableLength > 262144) return;   // slow client: drop snapshots, never block the room
    this._frame(1, Buffer.from(str));
  }
  close(code) { if (this.open) { const p = Buffer.alloc(2); p.writeUInt16BE(code || 1000); this._frame(8, p); this.open = false; try { this.s.end(); } catch (e) { } setTimeout(() => { try { this.s.destroy(); } catch (e) { } }, 500); this._closed(true); } }
  _closed(already) { if (this.dead) return; this.dead = true; this.open = false; if (this.onclose) { try { this.onclose(); } catch (e) { log('close handler error', e && e.stack || e); } } }
}

// ------------------------------------------------------------------------------------------ world state
let NEXT_ID = 1;
const PL = new Map();               // id -> player
const NAMES = new Map();            // lower-case account name -> player (one live connection per account)
const LOBBIES = new Set();
const ROOMS = new Map();
let NEXT_ROOM = 1;

const J = o => JSON.stringify(o);
const rnd = n => crypto.randomInt(n);
const pick = a => a[rnd(a.length)];
const shuffle = a => { for (let i = a.length - 1; i > 0; i--) { const j = rnd(i + 1);[a[i], a[j]] = [a[j], a[i]]; } return a; };
const send = (p, o, critical) => { if (p && p.ws) p.ws.send(J(o), critical); };

function httpJSON(urlStr, headers, timeout) {
  return new Promise(res => {
    let u; try { u = new URL(urlStr); } catch (e) { return res({ err: 'badurl' }); }
    const lib = u.protocol === 'https:' ? https : http;
    const rq = lib.request(u, { method: 'GET', headers: headers || {}, timeout: timeout || 9000 }, r => {
      let b = ''; r.setEncoding('utf8'); r.on('data', d => { b += d; if (b.length > 4e6) rq.destroy(); });
      r.on('end', () => { let j = null; try { j = JSON.parse(b); } catch (e) { } res({ status: r.statusCode, json: j }); });
    });
    rq.on('error', () => res({ err: 'unreachable' })); rq.on('timeout', () => { rq.destroy(); });
    rq.end();
  });
}

// Check the login token with the existing account server and read the purchases (GET /api/save).
async function checkAccount(token) {
  if (CFG.dev) return { ok: true, own: null };
  const r = await httpJSON(CFG.account + '/api/save', { Authorization: 'Bearer ' + token });
  if (r.err) return { ok: false, why: 'The account server cannot be reached (' + CFG.account + ').' };
  if (r.status === 401 || r.status === 403) return { ok: false, why: 'Login expired. Log in again.' };
  if (r.status !== 200) return { ok: false, why: 'Account server error ' + r.status };
  const own = r.json && r.json.save && Array.isArray(r.json.save.own) ? r.json.save.own.filter(n => Number.isInteger(n)) : [];
  return { ok: true, own };
}

function displayName(raw, taken) {
  let n = String(raw || '').replace(/[^\w .\-]/g, '').trim().slice(0, 16) || 'Player';
  if (BOT_NAMES.includes(n.toLowerCase())) n += '_';
  let out = n, k = 2;
  while (taken.has(out.toLowerCase())) out = n.slice(0, 13) + '_' + k++;
  return out;
}

// ------------------------------------------------------------------------------------------ lobbies / matchmaking
class Lobby {
  constructor() { this.id = 'L' + (NEXT_ROOM++); this.players = []; this.created = Date.now(); this.joined = Date.now(); this.count = 0; this.dead = false; LOBBIES.add(this); }
  deadline() { return Math.max(this.created + CFG.fillMs, this.players.length < MAX ? this.joined + Math.min(8000, CFG.fillMs) : 0); }
}
function tally(lobby) {
  const m = {}, d = {};
  for (const x of MAPS) m[x] = 0; for (const x of MODES) d[x] = 0;
  for (const p of lobby.players) { if (p.vote.map && p.vote.map in m) m[p.vote.map]++; if (p.vote.mode && p.vote.mode in d) d[p.vote.mode]++; }
  return { maps: m, modes: d };
}
function winner(counts) {            // most votes; a tie (or nobody voting) is settled randomly among the leaders
  const mx = Math.max(...Object.values(counts)), lead = Object.keys(counts).filter(k => counts[k] === mx);
  return pick(lead);
}
function lobbyInfo(l, p) {
  const now = Date.now(), t = tally(l);
  return { t: 'lobby', id: l.id, n: l.players.length, max: MAX, el: now - l.created, fill: l.count ? 0 : Math.max(0, l.deadline() - now), cd: l.count ? Math.max(0, l.count - now) : 0,
    st: l.count ? 'count' : 'search', votes: t, my: p ? { map: p.vote.map, mode: p.vote.mode } : null, names: l.players.map(x => x.name), online: PL.size };
}
function pushLobby(l) { for (const p of l.players) send(p, lobbyInfo(l, p), true); }
function leaveLobby(p) {
  const l = p.lobby; if (!l) return; p.lobby = null;
  l.players = l.players.filter(x => x !== p);
  if (!l.players.length) { l.dead = true; LOBBIES.delete(l); } else { if (l.count && l.players.length < MAX && false) l.count = 0; pushLobby(l); }
}
function findLobby(p, vote) {
  if (p.lobby || p.room) return;
  p.vote = { map: vote && MAPS.includes(vote.map) ? vote.map : null, mode: vote && MODES.includes(vote.mode) ? vote.mode : null };
  let l = null;
  for (const x of LOBBIES) if (!x.dead && x.players.length < MAX && (!x.count || x.count - Date.now() > 1200) && (!l || x.created < l.created)) l = x;
  if (!l) l = new Lobby();
  l.players.push(p); p.lobby = l; l.joined = Date.now();
  if (l.players.length >= MAX && !l.count) l.count = Date.now() + CFG.countMs;
  log('queue', p.name, '->', l.id, l.players.length + '/' + MAX);
  pushLobby(l);
}

// ------------------------------------------------------------------------------------------ rooms
function startMatch(l) {
  LOBBIES.delete(l); l.dead = true;
  const humans = shuffle(l.players.slice()).slice(0, MAX); humans.forEach(p => p.lobby = null);
  const t = tally(l), map = winner(t.maps), mode = winner(t.modes);
  // humans alternate between the two teams so both sides get the same number of real players (+/-1)
  const slots = []; for (let i = 0; i < MAX; i++) slots.push({ slot: i, k: 'b', team: i < 5 ? 0 : 1, id: 0, name: '' });
  const aSlots = [0, 1, 2, 3, 4], bSlots = [5, 6, 7, 8, 9];
  humans.forEach((p, i) => { const s = (i % 2 === 0 ? aSlots : bSlots).shift(); slots[s] = { slot: s, k: 'h', team: s < 5 ? 0 : 1, id: p.id, name: p.name }; p.slot = s; });
  const room = { id: 'R' + (NEXT_ROOM++), map, mode, slots, host: -1, round: 0, rounds: ROUNDS[mode], phase: 'loadout', ready: new Set(), deadline: Date.now() + CFG.loadoutFirstMs, created: Date.now(), over: false };
  humans.forEach(p => { p.room = room; p.ld = null; });
  room.host = Math.min(...humans.map(p => p.slot));
  ROOMS.set(room.id, room);
  log('match', room.id, map, mode, humans.length + ' humans + ' + (MAX - humans.length) + ' bots');
  const pub = slots.map(s => ({ slot: s.slot, k: s.k, team: s.team, name: s.name, id: s.id }));
  for (const p of humans) send(p, { t: 'match', room: room.id, map, mode, you: p.slot, host: room.host, slots: pub, votes: t, rounds: room.rounds, dl: room.deadline - Date.now(), ts: Date.now() }, true);
}
const hostPlayer = r => { const s = r.slots[r.host]; return s && s.k === 'h' ? PL.get(s.id) : null; };
const humansOf = r => r.slots.filter(s => s.k === 'h').map(s => PL.get(s.id)).filter(Boolean);
function roomBroadcast(r, o, except, critical) { const m = J(o); for (const p of humansOf(r)) if (p !== except) p.ws.send(m, critical); }

function sanitizeLoadout(p, ld, own) {
  let m = ld && Number.isInteger(ld[0]) ? ld[0] : DEF_LOADOUT[0], s = ld && Number.isInteger(ld[1]) ? ld[1] : DEF_LOADOUT[1], g = ld && Number.isInteger(ld[2]) ? ld[2] : DEF_LOADOUT[2];
  if (m < 0 || m >= NWEAP) m = DEF_LOADOUT[0]; if (s < 0 || s >= NWEAP) s = DEF_LOADOUT[1]; if (g < 0 || g >= NGREN) g = DEF_LOADOUT[2];
  if (own) {   // null = dev mode, everything allowed
    if (PAID.includes(m) && !own.includes(m)) m = DEF_LOADOUT[0];
    if (PAID.includes(s) && !own.includes(s)) s = DEF_LOADOUT[1];
  }
  return [m, s, g];
}
function tryGo(r) {
  if (r.phase !== 'loadout') return;
  const hs = humansOf(r);
  if (hs.length && !(hs.every(p => r.ready.has(p.id)) || Date.now() >= r.deadline)) return;
  r.phase = 'play'; r.round++;
  const ld = {}; for (const p of hs) ld[p.slot] = p.ld || DEF_LOADOUT;
  roomBroadcast(r, { t: 'go', rd: r.round, ld, ts: Date.now() }, null, true);
}
function dropFromRoom(p) {
  const r = p.room; if (!r) return; p.room = null;
  const s = r.slots[p.slot]; if (s && s.id === p.id) { s.k = 'b'; s.id = 0; s.name = ''; }
  const hs = humansOf(r);
  if (!hs.length) { ROOMS.delete(r.id); log('room', r.id, 'closed'); return; }
  roomBroadcast(r, { t: 'slot', slot: p.slot, k: 'b' }, null, true);
  if (r.host === p.slot) { r.host = Math.min(...hs.map(x => x.slot)); roomBroadcast(r, { t: 'host', slot: r.host }, null, true); log('room', r.id, 'new host slot', r.host); }
  tryGo(r);
}

// who may send what inside a room. 'own' = about the sender's own slot (the host may also speak for the bots)
const REL = { s: 'own', f: 'own', k: 'own', rs: 'own', gr: 'own', bs: 'host', ob: 'host', bev: 'host', bm: 'host', cap: 'host', sp: 'host', rd: 'host', ffc: 'host', ffs: 'host' };
function relay(p, m) {
  const r = p.room; if (!r || r.over && m.t !== 'k') return;
  const mode = REL[m.t]; if (!mode) return;
  const isHost = r.host === p.slot;
  if (mode === 'host' && !isHost) return;
  if (mode === 'own') { if (m.f === undefined) m.f = p.slot; const sl = r.slots[m.f]; if (!sl || !(m.f === p.slot || (isHost && sl.k === 'b'))) return; }
  roomBroadcast(r, m, p, false);
}

function onMessage(p, raw) {
  let m; try { m = JSON.parse(raw); } catch (e) { return; }
  if (!m || typeof m.t !== 'string') return;
  p.msgs = (p.msgs || 0) + 1;
  switch (m.t) {
    case 'ping': send(p, { t: 'pong', n: m.n, ts: Date.now(), online: PL.size }); return;
    case 'find': findLobby(p, m); return;
    case 'cancel': leaveLobby(p); send(p, { t: 'idle' }, true); return;
    case 'vote': {
      if (!p.lobby || p.lobby.count && p.lobby.count - Date.now() < 300) return;
      if (m.map !== undefined) p.vote.map = MAPS.includes(m.map) ? m.map : null;
      if (m.mode !== undefined) p.vote.mode = MODES.includes(m.mode) ? m.mode : null;
      pushLobby(p.lobby); return;
    }
    case 'leave': leaveLobby(p); dropFromRoom(p); send(p, { t: 'idle' }, true); return;
    case 'ready': {
      const r = p.room; if (!r || r.phase !== 'loadout') return;
      checkAccount(p.token).then(a => {
        if (!r || p.room !== r) return;
        p.own = a.ok ? a.own : (p.own || []);
        p.ld = sanitizeLoadout(p, m.ld, CFG.dev ? null : p.own);
        r.ready.add(p.id); send(p, { t: 'ld', ld: p.ld }, true); tryGo(r);
      });
      return;
    }
    case 'h': {   // damage claim: shooter -> owner of the victim. The shooter's own client does the hit detection.
      const r = p.room; if (!r || r.phase !== 'play') return;
      const by = r.slots[m.by | 0], v = r.slots[m.v | 0]; if (!by || !v || by === v) return;
      if (!((m.by | 0) === p.slot || (r.host === p.slot && by.k === 'b'))) return;
      const a = +m.a; if (!(a > 0) || a > 400) return;
      const now = Date.now(); if (!p.dmgT || now - p.dmgT > 1000) { p.dmgT = now; p.dmgS = 0; } p.dmgS += a; if (p.dmgS > 4000) return;
      const target = v.k === 'h' ? PL.get(v.id) : hostPlayer(r); if (!target || target === p) return;
      send(target, { t: 'h', v: m.v | 0, by: m.by | 0, a, hd: m.hd ? 1 : 0, w: m.w | 0, hy: +m.hy || 0, kl: typeof m.kl === 'string' ? m.kl.slice(0, 24) : undefined }); return;
    }
    case 'rend': {
      const r = p.room; if (!r || r.host !== p.slot || r.phase !== 'play') return;
      if (m.last) { r.phase = 'over'; r.over = true; }
      else { r.phase = 'loadout'; r.ready.clear(); r.deadline = Date.now() + CFG.loadoutNextMs + 3000; }
      m.dl = r.deadline - Date.now(); roomBroadcast(r, m, p, true); return;
    }
    default: relay(p, m);
  }
}

// ------------------------------------------------------------------------------------------ connection handling
function onConnect(ws) {
  const p = { id: NEXT_ID++, ws, name: '', acct: '', token: '', own: [], lobby: null, room: null, slot: -1, vote: { map: null, mode: null }, authed: false, ld: null, seen: Date.now() };
  const authTimer = setTimeout(() => { if (!p.authed) ws.close(1008); }, 8000);
  ws.onmsg = async raw => {
    p.seen = Date.now();
    if (!p.authed) {
      if (p.authing) return;
      let m; try { m = JSON.parse(raw); } catch (e) { return ws.close(1008); }
      if (!m || m.t !== 'hello') return ws.close(1008);
      p.authing = true;
      const u = String(m.u || '').trim(), k = String(m.k || '');
      if (!u || (!k && !CFG.dev)) { ws.send(J({ t: 'err', why: 'Sign in to play online.' }), true); return ws.close(1008); }
      if (+m.v !== CFG.proto) { ws.send(J({ t: 'err', why: 'Game and server versions differ. Update both files.' }), true); return ws.close(1008); }
      const a = await checkAccount(k);
      if (ws.dead) return;
      if (!a.ok) { ws.send(J({ t: 'err', why: a.why }), true); return ws.close(1008); }
      const key = u.toLowerCase(), old = NAMES.get(key);
      if (old && old !== p) { send(old, { t: 'err', why: 'Signed in from another device.' }, true); old.ws.close(1000); }
      p.acct = u; p.token = k; p.own = a.own || []; p.authed = true; clearTimeout(authTimer);
      const taken = new Set([...PL.values()].filter(x => x !== old).map(x => x.name.toLowerCase()));
      p.name = displayName(u, taken); PL.set(p.id, p); NAMES.set(key, p);
      log('hello', p.name, '(' + PL.size + ' online)');
      send(p, { t: 'welcome', id: p.id, name: p.name, v: CFG.proto, online: PL.size, fill: CFG.fillMs, maps: MAPS, modes: MODES }, true);
      return;
    }
    onMessage(p, raw);
  };
  ws.onclose = () => {
    clearTimeout(authTimer);
    if (!p.authed) return;
    leaveLobby(p); dropFromRoom(p); PL.delete(p.id);
    if (NAMES.get(p.acct.toLowerCase()) === p) NAMES.delete(p.acct.toLowerCase());
    log('bye', p.name, '(' + PL.size + ' online)');
  };
}

// 1 Hz housekeeping: lobby countdowns, loadout deadlines, idle clients
setInterval(() => {
  const now = Date.now();
  for (const l of [...LOBBIES]) {
    if (l.dead) continue;
    if (!l.count && (l.players.length >= MAX || now >= l.deadline())) l.count = now + CFG.countMs;
    if (l.count && now >= l.count) { startMatch(l); continue; }
    pushLobby(l);
  }
  for (const r of ROOMS.values()) {
    if (r.phase === 'loadout' && now >= r.deadline) tryGo(r);
    if (r.over && now - (r.overAt || (r.overAt = now)) > 120000) { for (const p of humansOf(r)) { p.room = null; } ROOMS.delete(r.id); }
  }
  for (const p of PL.values()) if (now - p.seen > 45000) p.ws.close(1001);
}, 1000).unref();

// ------------------------------------------------------------------------------------------ http / upgrade
function attach(server, opts) {
  opts = opts || {}; const path = opts.path || '/mp';
  server.on('upgrade', (req, socket) => {
    const p = (req.url || '').split('?')[0];
    if (p !== path && p !== '/') return;                      // leave other upgrade paths to whoever owns them
    const key = req.headers['sec-websocket-key'];
    if (!key || String(req.headers.upgrade || '').toLowerCase() !== 'websocket') { socket.destroy(); return; }
    const acc = crypto.createHash('sha1').update(key + '258EAFA5-E914-47DA-95CA-C5AB0DC85B11').digest('base64');
    socket.write('HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: ' + acc + '\r\n\r\n');
    onConnect(new WS(socket));
  });
  return server;
}
function stats() { return { ok: true, proto: CFG.proto, online: PL.size, lobbies: LOBBIES.size, rooms: ROOMS.size, fillSeconds: CFG.fillMs / 1000, account: CFG.dev ? 'dev (unchecked)' : CFG.account }; }
function createServer() {
  const server = http.createServer((req, res) => {
    const u = (req.url || '').split('?')[0];
    res.setHeader('Access-Control-Allow-Origin', '*');
    if (u === '/health' || u === '/stats') { res.writeHead(200, { 'Content-Type': 'application/json' }); return res.end(J(stats())); }
    res.writeHead(200, { 'Content-Type': 'text/plain' }); res.end('Ghost Town Strike multiplayer server. WebSocket path: /mp\n' + J(stats()) + '\n');
  });
  return attach(server);
}
module.exports = { attach, createServer, stats, CFG };

if (require.main === module) {
  const server = createServer();
  server.listen(CFG.port, CFG.host, () => {
    log('Ghost Town Strike multiplayer server on ' + CFG.host + ':' + CFG.port + '  (ws path /mp)');
    log('account server:', CFG.dev ? 'DEV MODE - tokens are not checked' : CFG.account, '| bot fill after', CFG.fillMs / 1000 + 's');
  });
}
