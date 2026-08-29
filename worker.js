//name
/* =====================================================================================
 *  حکم آنلاین  —  Hokm Online (Telegram Mini App)
 *  Single-file Cloudflare Worker  +  Durable Objects  +  D1
 *  -------------------------------------------------------------------------------------
 *  Modes      : 4-player (classic Iranian Hokm, teams)  |  2-player (custom draft rules)
 *  Real-time  : Durable Object + WebSocket Hibernation API
 *  Storage    : D1 (users / rooms / games / rounds / stats)  + DO storage (live state)
 *  AI         : local heuristic engine  +  optional OpenAI-compatible LLM (multi-key pool)
 *  Config     : see config.txt  (Variables vs Secrets, D1 setup, deploy steps)
 * =====================================================================================*/

/* =====================================================================================
 * SECTION 1 — CONSTANTS & SMALL UTILS
 * ===================================================================================*/

const SUITS = ['S', 'H', 'D', 'C'];                       // spade, heart, diamond, club
const SUIT_FA = { S: 'پیک', H: 'دل', D: 'خشت', C: 'خاج' }; // ♠ پیک | ♥ دل | ♦ خشت | ♣ خاج
const RANKS = ['2', '3', '4', '5', '6', '7', '8', '9', 'T', 'J', 'Q', 'K', 'A'];
const RANK_VAL = RANKS.reduce((m, r, i) => (m[r] = i + 2, m), {});

const PHASE = {
  LOBBY: 'lobby',
  DEAL_HAKEM: 'deal_hakem',   // 4p: revealing cards to find the Ace
  TRUMP: 'trump',             // hakem picks hokm
  DISCARD: 'discard',         // 2p only
  DRAW: 'draw',               // 2p only
  PLAYING: 'playing',
  ROUND_END: 'round_end',
  GAME_END: 'game_end',
  PAUSED: 'paused',
};

const DEFAULTS = {
  targetPoints4: 7,
  targetPoints2: 5,
  turnSeconds: 30,
  botDelayMs: 1100,
  offlineGraceSeconds: 20,
  revealRejected: true,       // 2p: a rejected drawn card is shown to both players
  kotRule: true,              // 7-0 (4p) / 3-0 (2p) => kot
  hakemMethod: 'ace',         // 4p: 'ace' | 'random'
};

const now = () => Date.now();
const clamp = (n, a, b) => Math.max(a, Math.min(b, n));
const uid8 = () => crypto.randomUUID().replace(/-/g, '').slice(0, 12);
const jsonSafe = (s, d) => { try { return JSON.parse(s); } catch { return d; } };

function json(data, init = {}) {
  return new Response(JSON.stringify(data), {
    status: init.status || 200,
    headers: {
      'content-type': 'application/json; charset=utf-8',
      'cache-control': 'no-store',
      'access-control-allow-origin': '*',
      ...(init.headers || {}),
    },
  });
}
const bad = (msg, status = 400) => json({ ok: false, error: msg }, { status });

function shuffle(arr, rnd = Math.random) {
  for (let i = arr.length - 1; i > 0; i--) {
    const j = Math.floor(rnd() * (i + 1));
    const t = arr[i]; arr[i] = arr[j]; arr[j] = t;
  }
  return arr;
}
function newDeck() {
  const d = [];
  for (const s of SUITS) for (const r of RANKS) d.push(s + r);
  return shuffle(d);
}
const suitOf = (c) => c[0];
const rankOf = (c) => c.slice(1);
const valOf = (c) => RANK_VAL[c.slice(1)];

/** Room code: 5 chars, no ambiguous glyphs. */
function roomCode() {
  const A = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789';
  let s = '';
  const b = crypto.getRandomValues(new Uint8Array(5));
  for (let i = 0; i < 5; i++) s += A[b[i] % A.length];
  return s;
}

function sanitizeName(n, fallback = 'بازیکن') {
  if (!n) return fallback;
  return String(n).replace(/[\u0000-\u001f<>]/g, '').trim().slice(0, 24) || fallback;
}

/* Telegram-safe crypto helpers -------------------------------------------------------*/
const te = new TextEncoder();

async function hmacKey(secret, usage = ['sign', 'verify']) {
  return crypto.subtle.importKey('raw', typeof secret === 'string' ? te.encode(secret) : secret,
    { name: 'HMAC', hash: 'SHA-256' }, false, usage);
}
async function hmacHex(secret, msg) {
  const k = await hmacKey(secret, ['sign']);
  const sig = await crypto.subtle.sign('HMAC', k, te.encode(msg));
  return [...new Uint8Array(sig)].map(b => b.toString(16).padStart(2, '0')).join('');
}
async function hmacRaw(secretRaw, msg) {
  const k = await crypto.subtle.importKey('raw', secretRaw, { name: 'HMAC', hash: 'SHA-256' }, false, ['sign']);
  return new Uint8Array(await crypto.subtle.sign('HMAC', k, te.encode(msg)));
}
function b64url(bytes) {
  let s = btoa(String.fromCharCode(...bytes));
  return s.replace(/\+/g, '-').replace(/\//g, '_').replace(/=+$/, '');
}
function b64urlToBytes(s) {
  s = s.replace(/-/g, '+').replace(/_/g, '/');
  while (s.length % 4) s += '=';
  const raw = atob(s);
  return Uint8Array.from(raw, c => c.charCodeAt(0));
}
function timingSafeEqual(a, b) {
  if (a.length !== b.length) return false;
  let r = 0;
  for (let i = 0; i < a.length; i++) r |= a.charCodeAt(i) ^ b.charCodeAt(i);
  return r === 0;
}
async function sha256Hex(s) {
  const h = await crypto.subtle.digest('SHA-256', te.encode(s));
  return [...new Uint8Array(h)].map(b => b.toString(16).padStart(2, '0')).join('');
}

/* =====================================================================================
 * SECTION 2 — AUTH  (Telegram initData validation + stateless session tokens)
 * ===================================================================================*/

/**
 * Validate Telegram WebApp initData (HMAC-SHA256 per Telegram spec).
 * Returns the parsed user object or null.
 */
async function verifyInitData(initData, botToken, maxAgeSec = 86400) {
  if (!initData || !botToken) return null;
  const params = new URLSearchParams(initData);
  const hash = params.get('hash');
  if (!hash) return null;
  params.delete('hash');
  params.delete('signature'); // Ed25519 signature is not part of the HMAC payload
  const pairs = [...params.entries()].map(([k, v]) => k + '=' + v).sort();
  const dcs = pairs.join('\n');

  const secretRaw = await hmacRaw(te.encode('WebAppData'), botToken); // key = "WebAppData"
  const calcBytes = await hmacRaw(secretRaw, dcs);
  const calc = [...calcBytes].map(b => b.toString(16).padStart(2, '0')).join('');
  if (!timingSafeEqual(calc, hash)) return null;

  const authDate = Number(params.get('auth_date') || 0);
  if (maxAgeSec > 0 && authDate && (Date.now() / 1000 - authDate) > maxAgeSec) return null;

  const user = jsonSafe(params.get('user'), null);
  if (!user || !user.id) return null;
  return {
    user,
    startParam: params.get('start_param') || '',
    chatInstance: params.get('chat_instance') || '',
  };
}

/** Compact signed session token: base64url(payload).base64url(hmac) */
async function signSession(secret, payload) {
  const body = b64url(te.encode(JSON.stringify(payload)));
  const mac = await hmacHex(secret, body);
  return body + '.' + mac.slice(0, 32);
}
async function readSession(secret, token) {
  if (!token || token.indexOf('.') < 0) return null;
  const [body, mac] = token.split('.');
  const expect = (await hmacHex(secret, body)).slice(0, 32);
  if (!timingSafeEqual(expect, mac || '')) return null;
  const p = jsonSafe(new TextDecoder().decode(b64urlToBytes(body)), null);
  if (!p || (p.exp && p.exp < Math.floor(Date.now() / 1000))) return null;
  return p;
}

function sessionSecret(env) {
  return env.SESSION_SECRET || env.TELEGRAM_BOT_TOKEN || 'dev-insecure-secret-change-me';
}

/* =====================================================================================
 * SECTION 3 — D1 DATA LAYER (idempotent auto-migration + repositories)
 * ===================================================================================*/

const SCHEMA = [
  `CREATE TABLE IF NOT EXISTS users (
     uid TEXT PRIMARY KEY,
     tg_id TEXT, username TEXT, first_name TEXT, last_name TEXT, photo_url TEXT,
     lang TEXT, is_guest INTEGER DEFAULT 0,
     created_at INTEGER, last_seen INTEGER,
     prefs TEXT DEFAULT '{}'
   )`,
  `CREATE TABLE IF NOT EXISTS rooms (
     code TEXT PRIMARY KEY,
     mode INTEGER NOT NULL,
     host_uid TEXT,
     status TEXT DEFAULT 'lobby',
     settings TEXT DEFAULT '{}',
     players TEXT DEFAULT '[]',
     is_private INTEGER DEFAULT 0,
     created_at INTEGER, updated_at INTEGER
   )`,
  `CREATE INDEX IF NOT EXISTS idx_rooms_status ON rooms(status, updated_at)`,
  `CREATE TABLE IF NOT EXISTS games (
     id TEXT PRIMARY KEY,
     code TEXT, mode INTEGER,
     settings TEXT, scores TEXT, winner TEXT,
     rounds_played INTEGER DEFAULT 0,
     started_at INTEGER, ended_at INTEGER
   )`,
  `CREATE INDEX IF NOT EXISTS idx_games_code ON games(code, started_at)`,
  `CREATE TABLE IF NOT EXISTS game_players (
     game_id TEXT, uid TEXT, seat INTEGER, team INTEGER,
     name TEXT, is_bot INTEGER DEFAULT 0,
     PRIMARY KEY (game_id, seat)
   )`,
  `CREATE INDEX IF NOT EXISTS idx_gp_uid ON game_players(uid)`,
  `CREATE TABLE IF NOT EXISTS rounds (
     id TEXT PRIMARY KEY,
     game_id TEXT, round_no INTEGER,
     hakem_seat INTEGER, trump TEXT,
     tricks TEXT, points TEXT, kot INTEGER DEFAULT 0,
     ended_at INTEGER
   )`,
  `CREATE INDEX IF NOT EXISTS idx_rounds_game ON rounds(game_id, round_no)`,
  `CREATE TABLE IF NOT EXISTS moves (
     id INTEGER PRIMARY KEY AUTOINCREMENT,
     game_id TEXT, round_no INTEGER, trick_no INTEGER,
     seat INTEGER, card TEXT, ts INTEGER
   )`,
  `CREATE TABLE IF NOT EXISTS stats (
     uid TEXT PRIMARY KEY,
     games INTEGER DEFAULT 0, wins INTEGER DEFAULT 0, losses INTEGER DEFAULT 0,
     rounds_won INTEGER DEFAULT 0, tricks_won INTEGER DEFAULT 0,
     kots INTEGER DEFAULT 0, points INTEGER DEFAULT 0,
     rating INTEGER DEFAULT 1000, updated_at INTEGER
   )`,
  `CREATE INDEX IF NOT EXISTS idx_stats_rating ON stats(rating DESC)`,
  `CREATE TABLE IF NOT EXISTS ai_key_health (
     key_hash TEXT PRIMARY KEY,
     ok INTEGER DEFAULT 0, fail INTEGER DEFAULT 0,
     cooldown_until INTEGER DEFAULT 0,
     last_error TEXT, updated_at INTEGER
   )`,
  `CREATE TABLE IF NOT EXISTS chat_log (
     id INTEGER PRIMARY KEY AUTOINCREMENT,
     code TEXT, uid TEXT, name TEXT, text TEXT, ts INTEGER
   )`,
];

let _schemaReady = false;
async function ensureSchema(env) {
  if (_schemaReady || !env.DB) return;
  try {
    for (const stmt of SCHEMA) await env.DB.prepare(stmt).run();
    _schemaReady = true;
  } catch (e) {
    console.log('schema error', e && e.message);
  }
}

const DB = {
  async upsertUser(env, u) {
    if (!env.DB) return;
    await ensureSchema(env);
    const t = now();
    await env.DB.prepare(
      `INSERT INTO users (uid, tg_id, username, first_name, last_name, photo_url, lang, is_guest, created_at, last_seen)
       VALUES (?,?,?,?,?,?,?,?,?,?)
       ON CONFLICT(uid) DO UPDATE SET
         username=excluded.username, first_name=excluded.first_name, last_name=excluded.last_name,
         photo_url=excluded.photo_url, lang=excluded.lang, last_seen=excluded.last_seen`
    ).bind(u.uid, u.tg_id || null, u.username || null, u.first_name || null, u.last_name || null,
      u.photo_url || null, u.lang || null, u.is_guest ? 1 : 0, t, t).run();
  },

  async touchRoom(env, r) {
    if (!env.DB) return;
    await ensureSchema(env);
    const t = now();
    await env.DB.prepare(
      `INSERT INTO rooms (code, mode, host_uid, status, settings, players, is_private, created_at, updated_at)
       VALUES (?,?,?,?,?,?,?,?,?)
       ON CONFLICT(code) DO UPDATE SET
         mode=excluded.mode, host_uid=excluded.host_uid, status=excluded.status,
         settings=excluded.settings, players=excluded.players, is_private=excluded.is_private,
         updated_at=excluded.updated_at`
    ).bind(r.code, r.mode, r.host_uid || null, r.status || 'lobby',
      JSON.stringify(r.settings || {}), JSON.stringify(r.players || []),
      r.is_private ? 1 : 0, t, t).run();
  },

  async getRoom(env, code) {
    if (!env.DB) return null;
    await ensureSchema(env);
    return await env.DB.prepare(`SELECT * FROM rooms WHERE code=?`).bind(code).first();
  },

  async publicRooms(env, limit = 24) {
    if (!env.DB) return [];
    await ensureSchema(env);
    const cutoff = now() - 3 * 3600 * 1000;
    const r = await env.DB.prepare(
      `SELECT code, mode, status, players, updated_at FROM rooms
       WHERE is_private=0 AND status IN ('lobby','playing') AND updated_at > ?
       ORDER BY updated_at DESC LIMIT ?`
    ).bind(cutoff, limit).all();
    return (r.results || []).map(x => ({
      code: x.code, mode: x.mode, status: x.status,
      players: jsonSafe(x.players, []), updated_at: x.updated_at,
    }));
  },

  async saveGameStart(env, g) {
    if (!env.DB) return;
    await ensureSchema(env);
    await env.DB.prepare(
      `INSERT OR REPLACE INTO games (id, code, mode, settings, scores, winner, rounds_played, started_at, ended_at)
       VALUES (?,?,?,?,?,?,?,?,?)`
    ).bind(g.id, g.code, g.mode, JSON.stringify(g.settings || {}), JSON.stringify(g.scores || []),
      null, 0, now(), null).run();
    const batch = (g.players || []).map((p, seat) => env.DB.prepare(
      `INSERT OR REPLACE INTO game_players (game_id, uid, seat, team, name, is_bot) VALUES (?,?,?,?,?,?)`
    ).bind(g.id, p ? p.uid : null, seat, g.mode === 4 ? seat % 2 : seat, p ? p.name : 'خالی', p && p.isBot ? 1 : 0));
    if (batch.length) await env.DB.batch(batch);
  },

  async saveRound(env, r) {
    if (!env.DB) return;
    await ensureSchema(env);
    await env.DB.prepare(
      `INSERT OR REPLACE INTO rounds (id, game_id, round_no, hakem_seat, trump, tricks, points, kot, ended_at)
       VALUES (?,?,?,?,?,?,?,?,?)`
    ).bind(uid8(), r.game_id, r.round_no, r.hakem_seat, r.trump,
      JSON.stringify(r.tricks || []), JSON.stringify(r.points || []), r.kot ? 1 : 0, now()).run();
  },

  async saveGameEnd(env, g) {
    if (!env.DB) return;
    await ensureSchema(env);
    await env.DB.prepare(
      `UPDATE games SET scores=?, winner=?, rounds_played=?, ended_at=? WHERE id=?`
    ).bind(JSON.stringify(g.scores || []), String(g.winner), g.rounds_played || 0, now(), g.id).run();
  },

  async bumpStats(env, uid, delta) {
    if (!env.DB || !uid || String(uid).startsWith('bot:')) return;
    await ensureSchema(env);
    const t = now();
    await env.DB.prepare(
      `INSERT INTO stats (uid, games, wins, losses, rounds_won, tricks_won, kots, points, rating, updated_at)
       VALUES (?,?,?,?,?,?,?,?,?,?)
       ON CONFLICT(uid) DO UPDATE SET
         games=games+excluded.games, wins=wins+excluded.wins, losses=losses+excluded.losses,
         rounds_won=rounds_won+excluded.rounds_won, tricks_won=tricks_won+excluded.tricks_won,
         kots=kots+excluded.kots, points=points+excluded.points,
         rating=MAX(100, rating+excluded.rating-1000), updated_at=excluded.updated_at`
    ).bind(uid, delta.games || 0, delta.wins || 0, delta.losses || 0, delta.rounds_won || 0,
      delta.tricks_won || 0, delta.kots || 0, delta.points || 0, 1000 + (delta.rating || 0), t).run();
  },

  async leaderboard(env, limit = 30) {
    if (!env.DB) return [];
    await ensureSchema(env);
    const r = await env.DB.prepare(
      `SELECT s.uid, s.games, s.wins, s.rating, s.points, s.kots,
              COALESCE(u.first_name,'بازیکن') AS name, u.username, u.photo_url
       FROM stats s LEFT JOIN users u ON u.uid = s.uid
       WHERE s.games > 0 ORDER BY s.rating DESC, s.wins DESC LIMIT ?`
    ).bind(limit).all();
    return r.results || [];
  },

  async myHistory(env, uid, limit = 20) {
    if (!env.DB) return [];
    await ensureSchema(env);
    const r = await env.DB.prepare(
      `SELECT g.id, g.code, g.mode, g.scores, g.winner, g.rounds_played, g.started_at, g.ended_at,
              gp.seat, gp.team
       FROM game_players gp JOIN games g ON g.id = gp.game_id
       WHERE gp.uid = ? ORDER BY g.started_at DESC LIMIT ?`
    ).bind(uid, limit).all();
    return (r.results || []).map(x => ({ ...x, scores: jsonSafe(x.scores, []) }));
  },

  async myStats(env, uid) {
    if (!env.DB) return null;
    await ensureSchema(env);
    return await env.DB.prepare(`SELECT * FROM stats WHERE uid=?`).bind(uid).first();
  },

  async keyHealth(env) {
    if (!env.DB) return {};
    await ensureSchema(env);
    const r = await env.DB.prepare(`SELECT * FROM ai_key_health`).all();
    const m = {};
    for (const row of (r.results || [])) m[row.key_hash] = row;
    return m;
  },
  async markKey(env, hash, ok, errMsg, cooldownMs) {
    if (!env.DB) return;
    await ensureSchema(env);
    const t = now();
    await env.DB.prepare(
      `INSERT INTO ai_key_health (key_hash, ok, fail, cooldown_until, last_error, updated_at)
       VALUES (?,?,?,?,?,?)
       ON CONFLICT(key_hash) DO UPDATE SET
         ok=ok+excluded.ok, fail=fail+excluded.fail,
         cooldown_until=MAX(cooldown_until, excluded.cooldown_until),
         last_error=COALESCE(excluded.last_error, last_error), updated_at=excluded.updated_at`
    ).bind(hash, ok ? 1 : 0, ok ? 0 : 1, cooldownMs ? t + cooldownMs : 0,
      errMsg ? String(errMsg).slice(0, 200) : null, t).run();
  },

  async chat(env, code, uid, name, text) {
    if (!env.DB) return;
    await ensureSchema(env);
    await env.DB.prepare(`INSERT INTO chat_log (code, uid, name, text, ts) VALUES (?,?,?,?,?)`)
      .bind(code, uid, name, String(text).slice(0, 300), now()).run();
  },
};

/* =====================================================================================
 * SECTION 4 — AI LAYER
 *   4.1 Key pool  : round-robin over N OpenAI-compatible keys, with failure cooldown.
 *   4.2 Heuristic : pure-JS Hokm expert player (always available, zero latency/cost).
 *   4.3 LLM bot   : optional; asked to choose among *legal* cards, hard timeout,
 *                   any failure silently falls back to the heuristic engine.
 * ===================================================================================*/

/** Parse keys from several env shapes: AI_API_KEYS (comma/newline), AI_API_KEY_1..N */
function collectKeys(env) {
  const out = [];
  const push = (v) => {
    if (!v) return;
    String(v).split(/[\s,;]+/).forEach(k => { k = k.trim(); if (k.length > 8) out.push(k); });
  };
  push(env.AI_API_KEYS);
  push(env.AI_API_KEY);
  for (let i = 1; i <= 20; i++) push(env['AI_API_KEY_' + i]);
  return [...new Set(out)];
}

class KeyPool {
  constructor(env) {
    this.env = env;
    this.keys = collectKeys(env);
    this.cursor = Math.floor(Math.random() * Math.max(1, this.keys.length));
    this.local = new Map(); // hash -> cooldownUntil (in-isolate fast path)
  }
  get enabled() { return this.keys.length > 0 && String(this.env.AI_ENABLED ?? 'true') !== 'false'; }

  async pick(healthMap) {
    const n = this.keys.length;
    if (!n) return null;
    const t = now();
    for (let i = 0; i < n; i++) {
      const idx = (this.cursor + i) % n;
      const key = this.keys[idx];
      const h = await sha256Hex(key).then(x => x.slice(0, 16));
      const localCd = this.local.get(h) || 0;
      const dbCd = healthMap && healthMap[h] ? healthMap[h].cooldown_until : 0;
      if (localCd > t || dbCd > t) continue;
      this.cursor = (idx + 1) % n;   // advance => load spread across keys
      return { key, hash: h, index: idx };
    }
    // everything cooling down: use the least-recently-failed one anyway
    const key = this.keys[this.cursor % n];
    this.cursor = (this.cursor + 1) % n;
    return { key, hash: (await sha256Hex(key)).slice(0, 16), index: this.cursor };
  }

  cool(hash, ms) { this.local.set(hash, now() + ms); }
}

/**
 * Chat-completion call against any OpenAI-compatible endpoint, with key rotation
 * and per-attempt timeout. Returns string content or null.
 */
async function llmComplete(env, messages, { maxTokens = 120, temperature = 0.3, timeoutMs, retries } = {}) {
  const pool = new KeyPool(env);
  if (!pool.enabled) return null;
  const base = (env.AI_BASE_URL || 'https://api.openai.com/v1').replace(/\/+$/, '');
  const model = env.AI_MODEL || 'gpt-4o-mini';
  const tmo = Number(timeoutMs || env.AI_TIMEOUT_MS || 6000);
  const tries = Number(retries || Math.min(3, pool.keys.length || 1));
  const health = await DB.keyHealth(env).catch(() => ({}));

  for (let attempt = 0; attempt < tries; attempt++) {
    const chosen = await pool.pick(health);
    if (!chosen) return null;
    const ac = new AbortController();
    const timer = setTimeout(() => ac.abort(), tmo);
    try {
      const res = await fetch(base + '/chat/completions', {
        method: 'POST',
        signal: ac.signal,
        headers: {
          'content-type': 'application/json',
          'authorization': 'Bearer ' + chosen.key,
          ...(env.AI_EXTRA_HEADER_NAME && env.AI_EXTRA_HEADER_VALUE
            ? { [env.AI_EXTRA_HEADER_NAME]: env.AI_EXTRA_HEADER_VALUE } : {}),
        },
        body: JSON.stringify({
          model, messages, temperature,
          max_tokens: maxTokens,
          stream: false,
        }),
      });
      clearTimeout(timer);
      if (res.status === 429 || res.status === 402 || res.status === 401 || res.status === 403) {
        const cd = res.status === 429 ? 60_000 : 15 * 60_000;
        pool.cool(chosen.hash, cd);
        DB.markKey(env, chosen.hash, false, 'HTTP ' + res.status, cd).catch(() => {});
        continue;
      }
      if (!res.ok) {
        pool.cool(chosen.hash, 20_000);
        DB.markKey(env, chosen.hash, false, 'HTTP ' + res.status, 20_000).catch(() => {});
        continue;
      }
      const data = await res.json();
      const content = data?.choices?.[0]?.message?.content;
      DB.markKey(env, chosen.hash, true, null, 0).catch(() => {});
      if (content) return String(content);
    } catch (e) {
      clearTimeout(timer);
      pool.cool(chosen.hash, 30_000);
      DB.markKey(env, chosen.hash, false, (e && e.name === 'AbortError') ? 'timeout' : (e && e.message), 30_000).catch(() => {});
    }
  }
  return null;
}

/* ---------- 4.2 Heuristic Hokm engine ---------------------------------------------- */

/** Legal moves: must follow suit if possible (classic Hokm — no trump obligation). */
function legalCards(hand, trick, trump) {
  if (!trick.length) return hand.slice();
  const lead = suitOf(trick[0].card);
  const follow = hand.filter(c => suitOf(c) === lead);
  return follow.length ? follow : hand.slice();
}

/**
 * Who wins the current (possibly partial) trick: index into the trick array.
 * Rule: highest trump wins; if no trump was played, highest card of the lead suit wins.
 * (Off-suit non-trump discards can never win.)
 */
function trickWinnerIdx(trick, trump) {
  const lead = suitOf(trick[0].card);
  let best = 0;
  for (let i = 1; i < trick.length; i++) {
    const c = trick[i].card, b = trick[best].card;
    const cT = suitOf(c) === trump, bT = suitOf(b) === trump;
    if (cT && !bT) { best = i; continue; }              // first trump takes over
    if (!cT && bT) continue;                            // trump still leads
    if (cT && bT) { if (valOf(c) > valOf(b)) best = i; continue; }
    // neither is trump: only lead-suit cards can compete
    const cL = suitOf(c) === lead, bL = suitOf(b) === lead;
    if (cL && !bL) { best = i; continue; }
    if (cL && bL && valOf(c) > valOf(b)) best = i;
  }
  return best;
}

/** Choose hokm (trump) from a hand — weighted by length + high-card strength. */
function chooseTrump(hand) {
  let best = SUITS[0], bestScore = -1;
  for (const s of SUITS) {
    const cs = hand.filter(c => suitOf(c) === s);
    const len = cs.length;
    const high = cs.reduce((a, c) => a + Math.max(0, valOf(c) - 9), 0);   // T..A weighted
    const aces = cs.filter(c => rankOf(c) === 'A').length;
    const score = len * 2.6 + high * 1.15 + aces * 1.4 + (len >= 4 ? 1.5 : 0);
    if (score > bestScore) { bestScore = score; best = s; }
  }
  return best;
}

/**
 * Heuristic card choice.
 * ctx = { hand, trick, trump, seat, mode, partnerSeat, played:Set, tricksLeft }
 * Difficulty: 'easy' (noisy) | 'normal' | 'hard'
 */
function heuristicPlay(ctx, difficulty = 'normal') {
  const { hand, trick, trump, seat, partnerSeat } = ctx;
  const legal = legalCards(hand, trick, trump);
  if (legal.length === 1) return legal[0];
  if (difficulty === 'easy' && Math.random() < 0.35) return legal[Math.floor(Math.random() * legal.length)];

  const played = ctx.played || new Set();
  const trumpsGone = [...played].filter(c => suitOf(c) === trump).length + hand.filter(c => suitOf(c) === trump).length;
  const trumpsOut = 13 - trumpsGone;

  const lowest = (cards) => cards.slice().sort((a, b) => valOf(a) - valOf(b))[0];
  const highest = (cards) => cards.slice().sort((a, b) => valOf(b) - valOf(a))[0];

  /* --- Leading the trick ------------------------------------------------------- */
  if (!trick.length) {
    const nonTrump = legal.filter(c => suitOf(c) !== trump);
    const myTrumps = legal.filter(c => suitOf(c) === trump);

    // 1) cash certain winners (Ace, or King when Ace already played)
    for (const c of nonTrump) {
      if (rankOf(c) === 'A') return c;
      if (rankOf(c) === 'K' && played.has(suitOf(c) + 'A')) return c;
    }
    // 2) if we hold a dominant trump pile, draw out opponents' trumps
    if (myTrumps.length >= 4 && trumpsOut - myTrumps.length <= 3) return highest(myTrumps);
    // 3) otherwise lead a short-suit low card (probe) — keep trumps as control
    if (nonTrump.length) {
      const bySuit = {};
      nonTrump.forEach(c => (bySuit[suitOf(c)] = bySuit[suitOf(c)] || []).push(c));
      const suits = Object.keys(bySuit).sort((a, b) => bySuit[a].length - bySuit[b].length);
      const target = bySuit[suits[0]];
      return difficulty === 'hard' ? lowest(target) : target[Math.floor(Math.random() * target.length)];
    }
    return lowest(legal);
  }

  /* --- Following ---------------------------------------------------------------- */
  const wIdx = trickWinnerIdx(trick, trump);
  const winner = trick[wIdx];
  const partnerWinning = partnerSeat != null && winner.seat === partnerSeat;
  const lead = suitOf(trick[0].card);
  const isLast = trick.length === (ctx.mode === 2 ? 1 : 3);

  // partner already winning → duck (throw away lowest junk), unless we can safely overtake nothing
  if (partnerWinning) {
    const junk = legal.filter(c => suitOf(c) !== trump);
    return lowest(junk.length ? junk : legal);
  }

  // can we win in-suit?
  const inSuit = legal.filter(c => suitOf(c) === lead);
  const trumped = suitOf(winner.card) === trump;
  if (!trumped && inSuit.length) {
    const beat = inSuit.filter(c => valOf(c) > valOf(winner.card));
    if (beat.length) {
      // if last to play, win as cheaply as possible; else win convincingly
      return isLast ? lowest(beat) : (difficulty === 'hard' ? lowest(beat) : highest(beat));
    }
  }
  // must/can we trump in?
  const myTrumps = legal.filter(c => suitOf(c) === trump);
  const canTrump = myTrumps.length && (!inSuit.length || lead === trump);
  if (canTrump) {
    const beat = myTrumps.filter(c => !trumped || valOf(c) > valOf(winner.card));
    if (beat.length) {
      const trickValue = trick.reduce((a, x) => a + (valOf(x.card) > 11 ? 1 : 0), 0);
      // Don't burn a big trump on a worthless trick unless we're last / late in the round
      if (isLast || trickValue > 0 || (ctx.tricksLeft || 13) <= 5 || difficulty !== 'hard') return lowest(beat);
    }
  }
  // cannot win → dump cheapest non-trump
  const dump = legal.filter(c => suitOf(c) !== trump);
  return lowest(dump.length ? dump : legal);
}

/** 2-player mode: which 2 cards to discard from 5, given a trump. */
function heuristicDiscard(hand, trump, count = 2) {
  const scored = hand.map(c => {
    let s = valOf(c);
    if (suitOf(c) === trump) s += 40;                 // never dump trumps
    if (rankOf(c) === 'A') s += 12;
    if (rankOf(c) === 'K') s += 6;
    return { c, s };
  }).sort((a, b) => a.s - b.s);
  return scored.slice(0, count).map(x => x.c);
}

/** 2-player mode: keep a drawn card? */
function heuristicKeepDraw(card, hand, trump) {
  if (suitOf(card) === trump) return true;
  if (valOf(card) >= 13) return true;                 // K or A
  const worst = heuristicDiscard(hand, trump, 1)[0];
  return worst ? valOf(card) > valOf(worst) + 1 : valOf(card) >= 11;
}

/** LLM-assisted play: returns a legal card or null (caller falls back to heuristic). */
async function llmPlay(env, ctx, publicLog) {
  const legal = legalCards(ctx.hand, ctx.trick, ctx.trump);
  if (legal.length <= 1) return legal[0] || null;
  const sys = 'You are an expert Iranian Hokm card player. Reply with ONLY one card code from the allowed list. No explanation.';
  const user = [
    'Trump (hokm): ' + ctx.trump,
    'Your hand: ' + ctx.hand.join(' '),
    'Current trick (in order): ' + (ctx.trick.map(t => 'seat' + t.seat + ':' + t.card).join(' ') || '(you lead)'),
    ctx.partnerSeat != null ? 'Your partner is seat ' + ctx.partnerSeat + '. You are seat ' + ctx.seat + '.' : 'Heads-up (2 players). You are seat ' + ctx.seat + '.',
    'Cards already played this round: ' + (publicLog || []).join(' '),
    'Tricks won — us: ' + (ctx.myTricks || 0) + ', them: ' + (ctx.oppTricks || 0),
    'ALLOWED CARDS: ' + legal.join(' '),
    'Answer with exactly one of ALLOWED CARDS.',
  ].join('\n');
  const out = await llmComplete(env, [
    { role: 'system', content: sys }, { role: 'user', content: user },
  ], { maxTokens: 8, temperature: 0.2 });
  if (!out) return null;
  const m = out.toUpperCase().match(/\b([SHDC])\s?(10|[2-9]|T|J|Q|K|A)\b/);
  if (m) {
    const card = m[1] + (m[2] === '10' ? 'T' : m[2]);
    if (legal.includes(card)) return card;
  }
  return null;
}
/* =====================================================================================
 * SECTION 5 — GAME RULES CORE (pure functions, mode-aware)
 * ===================================================================================*/

const HOKM = {
  seatsFor(mode) { return mode === 2 ? 2 : 4; },
  teamOf(mode, seat) { return mode === 2 ? seat : seat % 2; },
  partnerOf(mode, seat) { return mode === 2 ? null : (seat + 2) % 4; },
  handSize(mode) { return mode === 2 ? 5 : 13; },
  tricksToWin(mode) { return mode === 2 ? 3 : 7; },
  nextSeat(mode, seat) { return (seat + 1) % (mode === 2 ? 2 : 4); },

  /** points for a finished round */
  roundPoints(mode, settings, winnerTeam, loserTricks, hakemTeam) {
    if (!settings.kotRule) return 1;
    if (loserTricks > 0) return 1;
    // kot
    if (mode === 4 && winnerTeam !== hakemTeam) return 3;   // کت حاکم
    return 2;                                                // کت معمولی
  },
};

/* =====================================================================================
 * SECTION 6 — DURABLE OBJECT: GameRoom
 *   - authoritative state machine
 *   - WebSocket Hibernation API (survives isolate eviction, no cost while idle)
 *   - alarm()-driven bot turns / turn timeouts / offline auto-play
 * ===================================================================================*/

export class GameRoom {
  constructor(ctx, env) {
    this.ctx = ctx;
    this.env = env;
    this.s = null;                       // live state
    this.loading = null;
    this.busy = Promise.resolve();       // serialize mutations
  }

  /* ---------- lifecycle -------------------------------------------------------- */

  async load() {
    if (this.s) return this.s;
    if (!this.loading) {
      this.loading = (async () => {
        const st = await this.ctx.storage.get('state');
        this.s = st || null;
        return this.s;
      })();
    }
    await this.loading;
    this.loading = null;
    return this.s;
  }

  async save() {
    if (this.s) {
      this.s.updatedAt = now();
      await this.ctx.storage.put('state', this.s);
    }
  }

  blank(code, mode, settings) {
    const n = HOKM.seatsFor(mode);
    return {
      code, mode,
      seq: 0,
      phase: PHASE.LOBBY,
      hostUid: null,
      createdAt: now(),
      updatedAt: now(),
      settings: {
        targetPoints: mode === 2 ? DEFAULTS.targetPoints2 : DEFAULTS.targetPoints4,
        turnSeconds: DEFAULTS.turnSeconds,
        botLevel: 'normal',
        useLLM: false,
        revealRejected: DEFAULTS.revealRejected,
        kotRule: DEFAULTS.kotRule,
        hakemMethod: DEFAULTS.hakemMethod,
        autoFillBots: true,
        isPrivate: false,
        ...(settings || {}),
      },
      seats: new Array(n).fill(null),
      spectators: [],
      scores: mode === 2 ? [0, 0] : [0, 0],
      gameId: null,
      roundNo: 0,
      hakemSeat: null,
      trump: null,
      turnSeat: null,
      hands: {},
      deck: [],
      trick: [],
      trickNo: 0,
      tricksWon: [0, 0],
      trickHistory: [],
      lastTrick: null,
      playedLog: [],
      reveal: null,        // {cards:[{seat,card}], seat}
      draft: null,         // 2p draft state
      turnDeadline: 0,
      roundSummary: null,
      gameSummary: null,
      chat: [],
      events: [],
      pausedBy: null,
    };
  }

  /* ---------- HTTP entry (from Worker) ---------------------------------------- */

  async fetch(req) {
    const url = new URL(req.url);
    const path = url.pathname;

    if (req.headers.get('Upgrade') === 'websocket') return this.handleUpgrade(req, url);

    if (path === '/do/init') {
      const body = await req.json();
      await this.load();
      if (!this.s) {
        this.s = this.blank(body.code, body.mode, body.settings);
        this.s.hostUid = body.host?.uid || null;
        await this.save();
      }
      return json({ ok: true, snapshot: this.publicInfo() });
    }
    if (path === '/do/info') {
      await this.load();
      return json({ ok: true, exists: !!this.s, info: this.s ? this.publicInfo() : null });
    }
    if (path === '/do/admin') {
      const body = await req.json();
      await this.load();
      if (!this.s) return json({ ok: false, error: 'no_room' });
      await this.serialized(() => this.applyAction(body.actor, body.action));
      return json({ ok: true, info: this.publicInfo() });
    }
    return json({ ok: false, error: 'not_found' }, { status: 404 });
  }

  publicInfo() {
    const s = this.s;
    return {
      code: s.code, mode: s.mode, phase: s.phase, hostUid: s.hostUid,
      scores: s.scores, roundNo: s.roundNo,
      settings: s.settings,
      players: s.seats.map((p, i) => p ? {
        seat: i, uid: p.uid, name: p.name, photo: p.photo,
        isBot: !!p.isBot, online: !!p.online,
      } : null),
      count: s.seats.filter(p => p && !p.isBot).length,
      updatedAt: s.updatedAt,
    };
  }

  /* ---------- WebSocket ------------------------------------------------------- */

  async handleUpgrade(req, url) {
    await this.load();
    if (!this.s) return new Response('room not found', { status: 404 });

    const uid = url.searchParams.get('uid');
    const name = sanitizeName(url.searchParams.get('name'));
    const photo = url.searchParams.get('photo') || '';
    const asSpectator = url.searchParams.get('spectate') === '1';
    if (!uid) return new Response('uid required', { status: 400 });

    const pair = new WebSocketPair();
    const [client, server] = Object.values(pair);
    this.ctx.acceptWebSocket(server, [uid]);
    server.serializeAttachment({ uid, name, photo });

    await this.serialized(async () => {
      await this.attachPlayer({ uid, name, photo }, asSpectator);
      this.emit({ t: 'join', uid, name });
      await this.pushAll();
      await this.scheduleTick();
    });

    return new Response(null, { status: 101, webSocket: client });
  }

  async webSocketMessage(ws, raw) {
    let msg;
    try { msg = JSON.parse(raw); } catch { return; }
    const att = ws.deserializeAttachment() || {};
    if (msg.t === 'ping') { try { ws.send(JSON.stringify({ t: 'pong', ts: now() })); } catch {} return; }
    await this.serialized(async () => {
      await this.load();
      if (!this.s) return;
      try {
        await this.applyAction({ uid: att.uid, name: att.name, photo: att.photo }, msg, ws);
      } catch (e) {
        try { ws.send(JSON.stringify({ t: 'error', m: (e && e.message) || 'خطا' })); } catch {}
      }
    });
  }

  async webSocketClose(ws) { await this.onGone(ws); }
  async webSocketError(ws) { await this.onGone(ws); }

  async onGone(ws) {
    const att = ws.deserializeAttachment() || {};
    await this.serialized(async () => {
      await this.load();
      if (!this.s || !att.uid) return;
      const stillOpen = this.ctx.getWebSockets(att.uid).filter(w => {
        try { return w.readyState === WebSocket.READY_STATE_OPEN || w.readyState === 1; } catch { return false; }
      });
      if (stillOpen.length) return;                     // another tab still connected
      const seat = this.seatOfUid(att.uid);
      if (seat != null) {
        this.s.seats[seat].online = false;
        this.s.seats[seat].lastSeen = now();
        this.emit({ t: 'offline', seat, name: this.s.seats[seat].name });
      }
      this.s.spectators = (this.s.spectators || []).filter(x => x.uid !== att.uid);
      await this.save();
      await this.pushAll();
      await this.scheduleTick();
    });
  }

  sockets() {
    return this.ctx.getWebSockets().filter(w => {
      try { return w.readyState === 1 || w.readyState === WebSocket.READY_STATE_OPEN; } catch { return false; }
    });
  }

  /** Serialize all mutations to avoid interleaved state writes. */
  serialized(fn) {
    const run = this.busy.then(() => fn()).catch(e => console.log('room error', e && e.stack || e));
    this.busy = run.catch(() => {});
    return run;
  }

  emit(e) {
    if (!this.s.events) this.s.events = [];
    this.s.events.push({ ...e, ts: now(), id: (this.s.seq || 0) + 1 });
    if (this.s.events.length > 24) this.s.events = this.s.events.slice(-24);
  }

  /* ---------- snapshots (per-player masking) ---------------------------------- */

  snapshotFor(uid) {
    const s = this.s;
    const mySeat = this.seatOfUid(uid);
    const hand = mySeat != null ? (s.hands[mySeat] || []) : [];
    const legal = (mySeat != null && s.phase === PHASE.PLAYING && s.turnSeat === mySeat)
      ? legalCards(hand, s.trick, s.trump) : [];

    return {
      t: 'state',
      seq: ++s.seq,
      code: s.code, mode: s.mode, phase: s.phase,
      hostUid: s.hostUid, isHost: s.hostUid === uid,
      mySeat, uid,
      settings: s.settings,
      seats: s.seats.map((p, i) => p ? {
        seat: i, uid: p.uid, name: p.name, photo: p.photo,
        isBot: !!p.isBot, botLevel: p.botLevel || null,
        online: !!p.online, afk: !!p.afk, team: HOKM.teamOf(s.mode, i),
        cards: (s.hands[i] || []).length,
        ready: !!p.ready,
      } : null),
      spectators: (s.spectators || []).map(x => ({ uid: x.uid, name: x.name })),
      scores: s.scores,
      roundNo: s.roundNo,
      hakemSeat: s.hakemSeat,
      trump: s.trump,
      turnSeat: s.turnSeat,
      turnDeadline: s.turnDeadline,
      turnSeconds: s.settings.turnSeconds,
      hand: this.sortHand(hand, s.trump),
      legal,
      trick: s.trick,
      trickNo: s.trickNo,
      tricksWon: s.tricksWon,
      lastTrick: s.lastTrick,
      reveal: s.reveal,
      draft: this.maskDraft(mySeat),
      roundSummary: s.roundSummary,
      gameSummary: s.gameSummary,
      chat: (s.chat || []).slice(-30),
      events: (s.events || []).slice(-8),
      pausedBy: s.pausedBy,
      serverTime: now(),
    };
  }

  sortHand(hand, trump) {
    const order = trump ? [trump, ...SUITS.filter(x => x !== trump)] : SUITS;
    return hand.slice().sort((a, b) => {
      const d = order.indexOf(suitOf(a)) - order.indexOf(suitOf(b));
      return d !== 0 ? d : valOf(b) - valOf(a);
    });
  }

  maskDraft(mySeat) {
    const d = this.s.draft;
    if (!d) return null;
    return {
      stage: d.stage,
      need: d.need,
      discardCount: d.discardCount,
      discarded: Object.fromEntries(Object.entries(d.discarded || {}).map(([k, v]) => [k, v.length])),
      drawSeat: d.drawSeat,
      // pending card only visible to the drawer
      pending: (d.pending && d.drawSeat === mySeat) ? d.pending : (d.pending ? 'XX' : null),
      forced: !!d.forced,
      rejectedPublic: this.s.settings.revealRejected ? (d.rejectedPublic || []) : [],
      drawsLeft: d.drawsLeft || {},
      deckLeft: this.s.deck.length,
      done: d.done || {},
    };
  }

  async pushAll() {
    await this.save();
    for (const ws of this.sockets()) {
      const att = ws.deserializeAttachment() || {};
      try { ws.send(JSON.stringify(this.snapshotFor(att.uid))); } catch {}
    }
  }
  sendTo(uid, payload) {
    for (const ws of this.ctx.getWebSockets(uid)) {
      try { ws.send(JSON.stringify(payload)); } catch {}
    }
  }

  /* ---------- players / seats -------------------------------------------------- */

  seatOfUid(uid) {
    const i = this.s.seats.findIndex(p => p && p.uid === uid);
    return i < 0 ? null : i;
  }
  humanCount() { return this.s.seats.filter(p => p && !p.isBot).length; }
  freeSeat() { return this.s.seats.findIndex(p => !p); }

  async attachPlayer(u, asSpectator) {
    const s = this.s;
    if (!s.hostUid) s.hostUid = u.uid;

    let seat = this.seatOfUid(u.uid);
    if (seat != null) {                          // reconnect
      s.seats[seat] = { ...s.seats[seat], name: u.name, photo: u.photo, online: true, isBot: false, lastSeen: now(), afk: false, misses: 0 };
      this.emit({ t: 'reconnect', seat, name: u.name });
      await this.save();
      return seat;
    }
    if (asSpectator) {
      s.spectators = (s.spectators || []).filter(x => x.uid !== u.uid);
      s.spectators.push({ uid: u.uid, name: u.name });
      await this.save();
      return null;
    }
    // take an empty seat, else replace a bot, else spectate
    let idx = this.freeSeat();
    if (idx < 0) idx = s.seats.findIndex(p => p && p.isBot);
    if (idx < 0) {
      s.spectators = (s.spectators || []).filter(x => x.uid !== u.uid);
      s.spectators.push({ uid: u.uid, name: u.name });
      await this.save();
      return null;
    }
    const takenFromBot = s.seats[idx] && s.seats[idx].isBot;
    s.seats[idx] = {
      uid: u.uid, name: u.name, photo: u.photo, isBot: false,
      online: true, joinedAt: now(), lastSeen: now(), ready: false,
    };
    if (takenFromBot) this.emit({ t: 'bot_replaced', seat: idx, name: u.name });
    await this.save();
    await this.syncRoomToD1();
    return idx;
  }

  makeBot(seat, level) {
    const names = ['رستم', 'سهراب', 'بهرام', 'کاوه', 'آرش', 'دارا', 'پرویز', 'مهرداد'];
    return {
      uid: 'bot:' + seat + ':' + uid8().slice(0, 4),
      name: '🤖 ' + names[(seat + Math.floor(Math.random() * names.length)) % names.length],
      photo: '', isBot: true, botLevel: level || this.s.settings.botLevel || 'normal',
      online: true, ready: true, joinedAt: now(),
    };
  }

  fillBots() {
    const s = this.s;
    for (let i = 0; i < s.seats.length; i++) if (!s.seats[i]) s.seats[i] = this.makeBot(i, s.settings.botLevel);
  }

  requireHost(actor) {
    if (this.s.hostUid !== actor.uid) throw new Error('فقط میزبان می‌تواند این کار را انجام دهد');
  }

  async syncRoomToD1() {
    const s = this.s;
    await DB.touchRoom(this.env, {
      code: s.code, mode: s.mode, host_uid: s.hostUid,
      status: s.phase === PHASE.LOBBY ? 'lobby' : (s.phase === PHASE.GAME_END ? 'ended' : 'playing'),
      settings: s.settings,
      players: s.seats.map(p => p ? { name: p.name, isBot: !!p.isBot, online: !!p.online } : null),
      is_private: s.settings.isPrivate ? 1 : 0,
    }).catch(() => {});
  }

  /* ---------- action router ---------------------------------------------------- */

  async applyAction(actor, msg, ws) {
    const s = this.s;
    const uid = actor.uid;
    const seat = this.seatOfUid(uid);
    const isHost = s.hostUid === uid;

    // Any deliberate interaction proves the player is back at the table.
    if (seat != null && s.seats[seat] && msg.t !== 'sync' && msg.t !== 'ping') {
      const p = s.seats[seat];
      p.lastSeen = now();
      if (p.afk) { p.afk = false; p.misses = 0; this.emit({ t: 'back', seat, name: p.name }); }
    }

    switch (msg.t) {
      /* --- lobby / host controls ------------------------------------------------ */
      case 'sync':
        this.sendTo(uid, this.snapshotFor(uid));
        return;

      case 'ready': {
        if (seat == null) return;
        s.seats[seat].ready = !!msg.v;
        this.emit({ t: 'ready', seat, v: !!msg.v });
        break;
      }

      case 'settings': {
        this.requireHost(actor);
        const allow = ['targetPoints', 'turnSeconds', 'botLevel', 'useLLM', 'revealRejected',
          'kotRule', 'hakemMethod', 'autoFillBots', 'isPrivate'];
        for (const k of allow) if (msg.v && k in msg.v) s.settings[k] = msg.v[k];
        s.settings.targetPoints = clamp(Number(s.settings.targetPoints) || 7, 1, 21);
        s.settings.turnSeconds = clamp(Number(s.settings.turnSeconds) || 30, 10, 180);
        // propagate bot level to existing bots
        s.seats.forEach(p => { if (p && p.isBot) p.botLevel = s.settings.botLevel; });
        this.emit({ t: 'settings' });
        await this.syncRoomToD1();
        break;
      }

      case 'add_bot': {
        this.requireHost(actor);
        const idx = (msg.seat != null && !s.seats[msg.seat]) ? msg.seat : this.freeSeat();
        if (idx < 0) throw new Error('صندلی خالی موجود نیست');
        s.seats[idx] = this.makeBot(idx, msg.level || s.settings.botLevel);
        if (s.phase !== PHASE.LOBBY) s.hands[idx] = s.hands[idx] || [];
        this.emit({ t: 'bot_added', seat: idx });
        break;
      }

      case 'kick': {
        this.requireHost(actor);
        const t = Number(msg.seat);
        if (!s.seats[t]) return;
        if (s.seats[t].uid === s.hostUid) throw new Error('میزبان قابل حذف نیست');
        const wasName = s.seats[t].name;
        if (s.phase === PHASE.LOBBY) s.seats[t] = null;
        else s.seats[t] = this.makeBot(t, s.settings.botLevel);  // replace by bot so the game can continue
        this.emit({ t: 'kick', seat: t, name: wasName });
        break;
      }

      case 'to_bot': {              // host converts a seat to bot (player stays as spectator)
        this.requireHost(actor);
        const t = Number(msg.seat);
        if (!s.seats[t]) return;
        const p = s.seats[t];
        if (!p.isBot) s.spectators.push({ uid: p.uid, name: p.name });
        s.seats[t] = this.makeBot(t, s.settings.botLevel);
        this.emit({ t: 'to_bot', seat: t });
        break;
      }

      case 'sit': {                 // spectator claims an empty / bot seat
        const t = Number(msg.seat);
        if (t < 0 || t >= s.seats.length) return;
        const cur = s.seats[t];
        if (cur && !cur.isBot && cur.uid !== uid) throw new Error('این صندلی پر است');
        if (!isHost && cur && cur.isBot && s.phase !== PHASE.LOBBY && !s.settings.allowTakeover !== false) {
          /* allowed: taking over a bot is how substitutes join */
        }
        const old = this.seatOfUid(uid);
        if (old != null) s.seats[old] = s.phase === PHASE.LOBBY ? null : this.makeBot(old, s.settings.botLevel);
        s.seats[t] = {
          uid, name: sanitizeName(actor.name), photo: actor.photo || '',
          isBot: false, online: true, joinedAt: now(), lastSeen: now(), ready: false,
        };
        s.spectators = (s.spectators || []).filter(x => x.uid !== uid);
        this.emit({ t: 'sit', seat: t, name: s.seats[t].name });
        break;
      }

      case 'swap': {                 // host swaps two seats (players + hands together)
        this.requireHost(actor);
        const a = Number(msg.a), b = Number(msg.b);
        if (a === b || a == null || b == null) return;
        if (a < 0 || b < 0 || a >= s.seats.length || b >= s.seats.length) return;
        const tmp = s.seats[a]; s.seats[a] = s.seats[b]; s.seats[b] = tmp;
        if (msg.withCards !== false) {
          const h = s.hands[a]; s.hands[a] = s.hands[b] || []; s.hands[b] = h || [];
          // seat-bound game references must follow the cards
        } else {
          // players move but cards stay with the seat → hakem/turn unchanged
        }
        this.emit({ t: 'swap', a, b });
        break;
      }

      case 'transfer_host': {
        this.requireHost(actor);
        const t = Number(msg.seat);
        if (s.seats[t] && !s.seats[t].isBot) { s.hostUid = s.seats[t].uid; this.emit({ t: 'host', seat: t }); }
        break;
      }

      case 'start': {
        this.requireHost(actor);
        if (s.phase !== PHASE.LOBBY && s.phase !== PHASE.GAME_END) throw new Error('بازی در جریان است');
        if (s.settings.autoFillBots) this.fillBots();
        if (s.seats.some(p => !p)) throw new Error('صندلی خالی وجود دارد — ربات اضافه کنید');
        await this.startGame();
        return;
      }

      case 'pause': {
        this.requireHost(actor);
        if (s.phase === PHASE.PAUSED) return;
        s.resumePhase = s.phase; s.phase = PHASE.PAUSED; s.pausedBy = actor.name;
        this.emit({ t: 'pause' });
        break;
      }
      case 'resume': {
        this.requireHost(actor);
        if (s.phase !== PHASE.PAUSED) return;
        s.phase = s.resumePhase || PHASE.PLAYING; s.pausedBy = null;
        this.touchTurn();
        this.emit({ t: 'resume' });
        break;
      }

      case 'next_round': {
        if (!isHost && s.phase !== PHASE.ROUND_END) return;
        if (s.phase !== PHASE.ROUND_END) throw new Error('دست تمام نشده');
        await this.startRound();
        return;
      }

      case 'restart': {
        this.requireHost(actor);
        s.scores = [0, 0]; s.roundNo = 0; s.gameSummary = null; s.roundSummary = null;
        await this.startGame();
        return;
      }

      case 'back_to_lobby': {
        this.requireHost(actor);
        Object.assign(s, {
          phase: PHASE.LOBBY, hands: {}, trick: [], trickNo: 0, tricksWon: [0, 0],
          trump: null, hakemSeat: null, turnSeat: null, reveal: null, draft: null,
          roundSummary: null, gameSummary: null, playedLog: [], roundNo: 0, scores: [0, 0],
        });
        s.seats.forEach(p => { if (p) p.ready = false; });
        this.emit({ t: 'lobby' });
        break;
      }

      /* --- gameplay ------------------------------------------------------------- */

      case 'trump': {
        if (s.phase !== PHASE.TRUMP) return;
        if (seat !== s.hakemSeat) throw new Error('فقط حاکم حکم را تعیین می‌کند');
        if (!SUITS.includes(msg.suit)) return;
        await this.setTrump(msg.suit);
        return;
      }

      case 'play': {
        if (s.phase !== PHASE.PLAYING) return;
        if (seat == null || seat !== s.turnSeat) throw new Error('نوبت شما نیست');
        await this.playCard(seat, msg.card);
        return;
      }

      case 'discard': {              // 2p draft
        if (s.phase !== PHASE.DISCARD || seat == null) return;
        await this.doDiscard(seat, msg.cards || []);
        return;
      }

      case 'draw_decide': {          // 2p draft: keep / reject the drawn card
        if (s.phase !== PHASE.DRAW || seat == null) return;
        await this.drawDecide(seat, !!msg.keep);
        return;
      }
      case 'draw_take': {            // 2p draft: request the next card
        if (s.phase !== PHASE.DRAW || seat == null) return;
        await this.drawTake(seat);
        return;
      }

      /* --- social ---------------------------------------------------------------*/
      case 'chat': {
        const text = String(msg.text || '').slice(0, 200).trim();
        if (!text) return;
        s.chat = s.chat || [];
        s.chat.push({ uid, name: sanitizeName(actor.name), text, ts: now(), seat });
        if (s.chat.length > 60) s.chat = s.chat.slice(-60);
        DB.chat(this.env, s.code, uid, actor.name, text).catch(() => {});
        break;
      }
      case 'emoji': {
        this.emit({ t: 'emoji', seat, e: String(msg.e || '👍').slice(0, 4) });
        break;
      }

      default: return;
    }

    await this.pushAll();
    await this.scheduleTick();
  }

  /* ---------- game flow -------------------------------------------------------- */

  async startGame() {
    const s = this.s;
    s.gameId = uid8();
    s.scores = [0, 0];
    s.roundNo = 0;
    s.gameSummary = null;
    s.roundSummary = null;
    s.hakemSeat = null;
    await DB.saveGameStart(this.env, {
      id: s.gameId, code: s.code, mode: s.mode, settings: s.settings,
      scores: s.scores, players: s.seats,
    }).catch(() => {});
    await this.startRound(true);
  }

  async startRound(firstRound = false) {
    const s = this.s;
    s.roundNo += 1;
    s.deck = newDeck();
    s.hands = {};
    s.trick = [];
    s.trickNo = 0;
    s.tricksWon = [0, 0];
    s.trickHistory = [];
    s.lastTrick = null;
    s.playedLog = [];
    s.trump = null;
    s.reveal = null;
    s.draft = null;
    s.roundSummary = null;
    for (let i = 0; i < s.seats.length; i++) s.hands[i] = [];

    const needHakem = s.hakemSeat == null || !s.keepHakem;
    if (s.hakemSeat == null) {
      // first hakem
      if (s.mode === 4 && s.settings.hakemMethod === 'ace') {
        await this.revealForHakem();
        return;
      }
      s.hakemSeat = Math.floor(Math.random() * s.seats.length);
      this.emit({ t: 'hakem_random', seat: s.hakemSeat });
    }
    await this.dealAndAskTrump();
  }

  /** 4p: flip cards one by one until the first Ace → that seat is hakem. */
  async revealForHakem() {
    const s = this.s;
    s.phase = PHASE.DEAL_HAKEM;
    const cards = [];
    let seat = Math.floor(Math.random() * s.seats.length);
    const deck = newDeck();
    let hakem = null;
    for (let i = 0; i < deck.length; i++) {
      const c = deck[i];
      cards.push({ seat, card: c });
      if (rankOf(c) === 'A') { hakem = seat; break; }
      seat = HOKM.nextSeat(s.mode, seat);
    }
    s.reveal = { cards, hakem };
    s.hakemSeat = hakem;
    this.emit({ t: 'reveal', hakem });
    await this.pushAll();
    // let the animation play out, then deal
    await this.ctx.storage.put('pendingDeal', true);
    s.turnDeadline = now() + Math.min(6000, 700 + cards.length * 380);
    await this.pushAll();
    await this.scheduleTick(s.turnDeadline - now());
  }

  async dealAndAskTrump() {
    const s = this.s;
    await this.ctx.storage.delete('pendingDeal');
    const n = s.seats.length;
    s.deck = newDeck();
    const initial = s.mode === 2 ? 5 : 5;          // 4p: hakem sees 5 before choosing hokm
    for (let i = 0; i < n; i++) s.hands[i] = [];
    for (let k = 0; k < initial; k++) {
      for (let i = 0; i < n; i++) {
        const seat = (s.hakemSeat + i) % n;
        s.hands[seat].push(s.deck.pop());
      }
    }
    s.phase = PHASE.TRUMP;
    s.turnSeat = s.hakemSeat;
    s.reveal = s.reveal ? { ...s.reveal, done: true } : null;
    this.touchTurn();
    this.emit({ t: 'ask_trump', seat: s.hakemSeat });
    await this.pushAll();
    await this.scheduleTick();
  }

  async setTrump(suit) {
    const s = this.s;
    s.trump = suit;
    this.emit({ t: 'trump', suit, seat: s.hakemSeat });

    if (s.mode === 4) {
      // deal remaining cards: 4 + 4 (classic pacing)
      for (const chunk of [4, 4]) {
        for (let k = 0; k < chunk; k++) {
          for (let i = 0; i < s.seats.length; i++) {
            const seat = (s.hakemSeat + i) % s.seats.length;
            s.hands[seat].push(s.deck.pop());
          }
        }
      }
      s.phase = PHASE.PLAYING;
      s.turnSeat = s.hakemSeat;
      s.trickNo = 1;
      this.touchTurn();
      this.emit({ t: 'deal_rest' });
    } else {
      // 2-player custom draft
      s.draft = {
        stage: 'discard',
        discardCount: 2,
        need: [s.hakemSeat, HOKM.nextSeat(2, s.hakemSeat)],
        discarded: {},
        drawSeat: null,
        pending: null,
        forced: false,
        rejectedPublic: [],
        drawsLeft: { [s.hakemSeat]: 2, [HOKM.nextSeat(2, s.hakemSeat)]: 2 },
        done: {},
      };
      s.phase = PHASE.DISCARD;
      s.turnSeat = s.hakemSeat;      // hakem discards first
      this.touchTurn();
      this.emit({ t: 'draft_start' });
    }
    await this.pushAll();
    await this.scheduleTick();
  }

  /* --- 2-player draft --------------------------------------------------------- */

  async doDiscard(seat, cards) {
    const s = this.s, d = s.draft;
    if (!d || d.stage !== 'discard') return;
    if (s.turnSeat !== seat) throw new Error('نوبت شما نیست');
    if (d.discarded[seat]) return;
    const hand = s.hands[seat] || [];
    const uniq = [...new Set(cards)].filter(c => hand.includes(c));
    if (uniq.length !== d.discardCount) throw new Error('باید دقیقاً ' + d.discardCount + ' کارت بیندازید');
    d.discarded[seat] = uniq;
    s.hands[seat] = hand.filter(c => !uniq.includes(c));
    this.emit({ t: 'discard', seat, n: uniq.length });

    const other = HOKM.nextSeat(2, seat);
    if (!d.discarded[other]) {
      s.turnSeat = other;
      this.touchTurn();
    } else {
      // both discarded → draw phase, hakem first
      d.stage = 'draw';
      d.drawSeat = s.hakemSeat;
      d.pending = null;
      d.forced = false;
      s.phase = PHASE.DRAW;
      s.turnSeat = s.hakemSeat;
      this.touchTurn();
      this.emit({ t: 'draw_phase', seat: s.hakemSeat });
    }
    await this.pushAll();
    await this.scheduleTick();
  }

  /** Draw a card face-up (to the drawer only). */
  async drawTake(seat) {
    const s = this.s, d = s.draft;
    if (!d || d.stage !== 'draw' || d.drawSeat !== seat) return;
    if (d.pending) return;                            // already holding one
    if ((d.drawsLeft[seat] || 0) <= 0) return this.advanceDraw();
    if (!s.deck.length) return this.advanceDraw(true);
    d.pending = s.deck.pop();
    this.touchTurn();
    this.emit({ t: 'draw', seat });
    await this.pushAll();
    await this.scheduleTick();
  }

  /**
   * Decision on the pending card.
   *  keep=true  → card enters the hand, this draw is consumed.
   *  keep=false → card is thrown away; the NEXT card must be taken unconditionally.
   */
  async drawDecide(seat, keep) {
    const s = this.s, d = s.draft;
    if (!d || d.stage !== 'draw' || d.drawSeat !== seat || !d.pending) return;
    const card = d.pending;

    if (keep || d.forced) {
      s.hands[seat].push(card);
      d.pending = null;
      d.forced = false;
      d.drawsLeft[seat] = (d.drawsLeft[seat] || 1) - 1;
      this.emit({ t: 'kept', seat, card: d.forcedShow ? card : null });
      if ((d.drawsLeft[seat] || 0) <= 0) { await this.advanceDraw(); return; }
      // still has a draw left → auto-take next
      await this.pushAll();
      await this.scheduleTick();
      return;
    }

    // rejected → discard it, next card is forced
    d.rejectedPublic.push({ seat, card });
    d.pending = null;
    d.forced = true;
    this.emit({ t: 'rejected', seat, card: s.settings.revealRejected ? card : null });

    if (!s.deck.length) {
      d.drawsLeft[seat] = 0;
      await this.advanceDraw(true);
      return;
    }
    // immediately take the forced card (must accept whatever it is)
    d.pending = s.deck.pop();
    d.forced = true;
    this.touchTurn();
    this.emit({ t: 'forced', seat });
    await this.pushAll();
    await this.scheduleTick();
  }

  async advanceDraw(deckEmpty = false) {
    const s = this.s, d = s.draft;
    d.done[d.drawSeat] = true;
    d.pending = null;
    d.forced = false;
    const other = HOKM.nextSeat(2, d.drawSeat);
    if (!d.done[other] && !deckEmpty) {
      d.drawSeat = other;
      s.turnSeat = other;
      this.touchTurn();
      this.emit({ t: 'draw_phase', seat: other });
      await this.pushAll();
      await this.scheduleTick();
      return;
    }
    // draft complete → play
    d.stage = 'done';
    s.phase = PHASE.PLAYING;
    s.turnSeat = s.hakemSeat;
    s.trickNo = 1;
    this.touchTurn();
    this.emit({ t: 'play_start' });
    await this.pushAll();
    await this.scheduleTick();
  }

  /* --- trick play ------------------------------------------------------------- */

  async playCard(seat, card) {
    const s = this.s;
    const hand = s.hands[seat] || [];
    if (!hand.includes(card)) throw new Error('این کارت را ندارید');
    const legal = legalCards(hand, s.trick, s.trump);
    if (!legal.includes(card)) throw new Error('باید از خال زمین بازی کنید');

    s.hands[seat] = hand.filter(c => c !== card);
    s.trick.push({ seat, card });
    s.playedLog.push(card);
    this.emit({ t: 'play', seat, card });

    const full = s.trick.length >= s.seats.length;
    if (!full) {
      s.turnSeat = HOKM.nextSeat(s.mode, seat);
      this.touchTurn();
      await this.pushAll();
      await this.scheduleTick();
      return;
    }
    await this.resolveTrick();
  }

  async resolveTrick() {
    const s = this.s;
    const wIdx = trickWinnerIdx(s.trick, s.trump);
    const winner = s.trick[wIdx].seat;
    const team = HOKM.teamOf(s.mode, winner);
    s.tricksWon[team] += 1;
    s.lastTrick = { cards: s.trick.slice(), winner, trickNo: s.trickNo };
    s.trickHistory.push(s.lastTrick);
    this.emit({ t: 'trick', winner, team, cards: s.trick.slice() });

    s.trick = [];
    s.trickNo += 1;
    s.turnSeat = winner;
    this.touchTurn(1500);                            // small pause to show the won trick
    await this.pushAll();

    const need = HOKM.tricksToWin(s.mode);
    const handsEmpty = Object.values(s.hands).every(h => !h.length);
    if (s.tricksWon[0] >= need || s.tricksWon[1] >= need || handsEmpty) {
      await this.endRound();
      return;
    }
    await this.scheduleTick(900);
  }

  async endRound() {
    const s = this.s;
    const winnerTeam = s.tricksWon[0] > s.tricksWon[1] ? 0 : 1;
    const loserTeam = 1 - winnerTeam;
    const hakemTeam = HOKM.teamOf(s.mode, s.hakemSeat);
    const pts = HOKM.roundPoints(s.mode, s.settings, winnerTeam, s.tricksWon[loserTeam], hakemTeam);
    s.scores[winnerTeam] += pts;
    const kot = s.tricksWon[loserTeam] === 0;

    s.roundSummary = {
      roundNo: s.roundNo, winnerTeam, points: pts, kot,
      kotHakem: kot && s.mode === 4 && winnerTeam !== hakemTeam,
      tricks: s.tricksWon.slice(), trump: s.trump, hakemSeat: s.hakemSeat,
      scores: s.scores.slice(),
    };
    s.phase = PHASE.ROUND_END;
    s.turnSeat = null;
    this.emit({ t: 'round_end', ...s.roundSummary });

    DB.saveRound(this.env, {
      game_id: s.gameId, round_no: s.roundNo, hakem_seat: s.hakemSeat, trump: s.trump,
      tricks: s.tricksWon, points: s.scores, kot,
    }).catch(() => {});
    for (let i = 0; i < s.seats.length; i++) {
      const p = s.seats[i];
      if (!p || p.isBot) continue;
      const t = HOKM.teamOf(s.mode, i);
      DB.bumpStats(this.env, p.uid, {
        rounds_won: t === winnerTeam ? 1 : 0,
        tricks_won: s.tricksWon[t],
        kots: (kot && t === winnerTeam) ? 1 : 0,
        points: t === winnerTeam ? pts : 0,
      }).catch(() => {});
    }

    // hakem rule: winner side keeps/gains the hakem seat
    if (winnerTeam === hakemTeam) {
      s.keepHakem = true;                                  // hakem stays
    } else {
      s.keepHakem = false;
      // new hakem = next player of the winning team (classic: player to hakem's right in winning team)
      let cand = HOKM.nextSeat(s.mode, s.hakemSeat);
      for (let i = 0; i < s.seats.length; i++) {
        if (HOKM.teamOf(s.mode, cand) === winnerTeam) break;
        cand = HOKM.nextSeat(s.mode, cand);
      }
      s.hakemSeat = cand;
    }

    if (s.scores[winnerTeam] >= s.settings.targetPoints) {
      await this.endGame(winnerTeam);
      return;
    }
    await this.pushAll();
    await this.scheduleTick(1200);                          // auto-continue after a beat
  }

  async endGame(winnerTeam) {
    const s = this.s;
    s.phase = PHASE.GAME_END;
    s.gameSummary = {
      winnerTeam, scores: s.scores.slice(), rounds: s.roundNo,
      players: s.seats.map((p, i) => p ? { seat: i, name: p.name, team: HOKM.teamOf(s.mode, i), isBot: !!p.isBot } : null),
    };
    this.emit({ t: 'game_end', winnerTeam });
    DB.saveGameEnd(this.env, { id: s.gameId, scores: s.scores, winner: winnerTeam, rounds_played: s.roundNo }).catch(() => {});
    for (let i = 0; i < s.seats.length; i++) {
      const p = s.seats[i];
      if (!p || p.isBot) continue;
      const t = HOKM.teamOf(s.mode, i);
      const won = t === winnerTeam;
      DB.bumpStats(this.env, p.uid, {
        games: 1, wins: won ? 1 : 0, losses: won ? 0 : 1,
        rating: won ? 18 : -12,
      }).catch(() => {});
    }
    s.hakemSeat = null;
    s.keepHakem = false;
    await this.syncRoomToD1();
    await this.pushAll();
  }

  /* ---------- turn clock, alarms, bots ---------------------------------------- */

  touchTurn(extraMs) {
    const s = this.s;
    const base = (s.settings.turnSeconds || 30) * 1000;
    s.turnDeadline = now() + (extraMs != null ? extraMs : base);
  }

  /** Decide when we next need to act and set the DO alarm accordingly. */
  async scheduleTick(inMs) {
    const s = this.s;
    if (!s) return;
    let delay = inMs;
    if (delay == null) {
      const seatObj = s.turnSeat != null ? s.seats[s.turnSeat] : null;
      const isBotTurn = seatObj && seatObj.isBot;
      if (s.phase === PHASE.ROUND_END) delay = 3000;
      else if (s.phase === PHASE.DEAL_HAKEM) delay = Math.max(400, s.turnDeadline - now());
      else if (s.phase === PHASE.PAUSED || s.phase === PHASE.LOBBY || s.phase === PHASE.GAME_END) {
        await this.ctx.storage.deleteAlarm().catch(() => {});
        return;
      } else if (isBotTurn) {
        delay = seatObj.isBot
          ? (Number(this.env.BOT_DELAY_MS) || DEFAULTS.botDelayMs)
          : (s.settings.offlineGraceSeconds || DEFAULTS.offlineGraceSeconds) * 1000;
      } else if (seatObj && seatObj.afk) {
        // Player is present but repeatedly timed out: don't stall every trick for the
        // full turn timer — act at bot speed until they touch the table again.
        delay = Number(this.env.BOT_DELAY_MS) || DEFAULTS.botDelayMs;
      } else {
        delay = Math.max(500, s.turnDeadline - now());
      }
    }
    const at = now() + clamp(delay, 150, 120000);
    const cur = await this.ctx.storage.getAlarm().catch(() => null);
    if (cur == null || cur > at + 120 || cur < now() - 1000) {
      await this.ctx.storage.setAlarm(at).catch(() => {});
    }
  }

  async alarm() {
    await this.serialized(async () => {
      await this.load();
      if (!this.s) return;
      const s = this.s;
      try {
        await this.tick();
      } catch (e) {
        console.log('tick error', e && e.stack || e);
      }
      await this.pushAll();
      await this.scheduleTick();
    });
  }

  async tick() {
    const s = this.s;

    if (s.phase === PHASE.DEAL_HAKEM) {
      if (now() >= s.turnDeadline - 100) await this.dealAndAskTrump();
      return;
    }
    if (s.phase === PHASE.ROUND_END) {
      if (s.scores.some(v => v >= s.settings.targetPoints)) return;
      await this.startRound();
      return;
    }
    if (s.phase === PHASE.PAUSED || s.phase === PHASE.LOBBY || s.phase === PHASE.GAME_END) return;

    const seat = s.turnSeat;
    if (seat == null) return;
    const p = s.seats[seat];
    if (!p) return;

    const isBot = !!p.isBot;
    const expired = now() >= s.turnDeadline - 120;

    if (!isBot) {
      if (!p.online) {
        // Offline human: honour a short grace period, then auto-play. Never kick.
        const grace = (s.settings.offlineGraceSeconds || DEFAULTS.offlineGraceSeconds) * 1000;
        if (now() - (p.lastSeen || 0) < grace && !expired) return;
        this.emit({ t: 'autoplay', seat, name: p.name });
      } else if (p.afk) {
        // Flagged as away → keep the table moving at bot pace.
        if (!expired && now() < (s.turnDeadline - (s.settings.turnSeconds || 30) * 1000 + 900)) return;
      } else if (!expired) {
        return;                                    // still has time on the clock
      } else {
        p.misses = (p.misses || 0) + 1;
        if (p.misses >= 2) {
          p.afk = true;
          this.emit({ t: 'afk', seat, name: p.name });
        }
        this.emit({ t: 'timeout', seat, name: p.name });
      }
    }

    await this.autoAct(seat, isBot ? (p.botLevel || 'normal') : 'normal', isBot);
  }

  /** Perform the move for `seat` automatically (bot or timed-out/offline human). */
  async autoAct(seat, level, allowLLM) {
    const s = this.s;
    const hand = s.hands[seat] || [];

    if (s.phase === PHASE.TRUMP && seat === s.hakemSeat) {
      let suit = null;
      if (allowLLM && s.settings.useLLM) suit = await this.llmTrump(hand);
      await this.setTrump(suit || chooseTrump(hand));
      return;
    }

    if (s.phase === PHASE.DISCARD) {
      const cards = heuristicDiscard(hand, s.trump, s.draft ? s.draft.discardCount : 2);
      await this.doDiscard(seat, cards);
      return;
    }

    if (s.phase === PHASE.DRAW) {
      const d = s.draft;
      if (!d) return;
      if (!d.pending) { await this.drawTake(seat); return; }
      if (d.forced) { await this.drawDecide(seat, true); return; }
      const keep = heuristicKeepDraw(d.pending, hand, s.trump);
      await this.drawDecide(seat, keep);
      return;
    }

    if (s.phase === PHASE.PLAYING) {
      const ctx = {
        hand, trick: s.trick, trump: s.trump, seat, mode: s.mode,
        partnerSeat: HOKM.partnerOf(s.mode, seat),
        played: new Set(s.playedLog),
        tricksLeft: hand.length,
        myTricks: s.tricksWon[HOKM.teamOf(s.mode, seat)],
        oppTricks: s.tricksWon[1 - HOKM.teamOf(s.mode, seat)],
      };
      let card = null;
      if (allowLLM && s.settings.useLLM && level === 'ai') {
        card = await llmPlay(this.env, ctx, s.playedLog).catch(() => null);
      }
      if (!card) card = heuristicPlay(ctx, level === 'ai' ? 'hard' : level);
      if (!card) return;
      await this.playCard(seat, card);
      return;
    }
  }

  async llmTrump(hand) {
    const out = await llmComplete(this.env, [
      { role: 'system', content: 'You are an expert Iranian Hokm player. Choose the best trump suit. Reply with exactly one letter: S, H, D or C.' },
      { role: 'user', content: 'Your 5 cards: ' + hand.join(' ') + '\nSuits: S=Spades H=Hearts D=Diamonds C=Clubs. Answer one letter.' },
    ], { maxTokens: 4, temperature: 0.2 }).catch(() => null);
    if (!out) return null;
    const m = out.toUpperCase().match(/\b([SHDC])\b/);
    return m ? m[1] : null;
  }
}

/* =====================================================================================
 * SECTION 7 — WORKER ENTRY: routing, REST API, Telegram webhook, WS proxy
 * ===================================================================================*/

function roomStub(env, code) {
  const id = env.GAME_ROOM.idFromName('room:' + code.toUpperCase());
  return env.GAME_ROOM.get(id);
}

async function authFrom(req, env) {
  // Priority: Authorization Bearer session token → X-Init-Data → ?initData → guest
  const secret = sessionSecret(env);
  const auth = req.headers.get('authorization') || '';
  if (auth.startsWith('Bearer ')) {
    const p = await readSession(secret, auth.slice(7));
    if (p) return p;
  }
  const initData = req.headers.get('x-init-data') || new URL(req.url).searchParams.get('initData');
  if (initData) {
    const v = await verifyInitData(initData, env.TELEGRAM_BOT_TOKEN, Number(env.INITDATA_MAX_AGE || 86400));
    if (v) return tgToUser(v.user, v.startParam);
  }
  return null;
}

function tgToUser(u, startParam) {
  return {
    uid: 'tg:' + u.id,
    tg_id: String(u.id),
    name: sanitizeName([u.first_name, u.last_name].filter(Boolean).join(' ') || u.username),
    username: u.username || '',
    photo: u.photo_url || '',
    lang: u.language_code || 'fa',
    startParam: startParam || '',
    is_guest: 0,
  };
}

async function tgApi(env, method, payload) {
  if (!env.TELEGRAM_BOT_TOKEN) return null;
  try {
    const r = await fetch(`https://api.telegram.org/bot${env.TELEGRAM_BOT_TOKEN}/${method}`, {
      method: 'POST',
      headers: { 'content-type': 'application/json' },
      body: JSON.stringify(payload),
    });
    return await r.json();
  } catch (e) { return null; }
}

const APP_NAME = 'حکم آنلاین';

export default {
  async fetch(req, env, ctx) {
    const url = new URL(req.url);
    const path = url.pathname;

    if (req.method === 'OPTIONS') {
      return new Response(null, {
        headers: {
          'access-control-allow-origin': '*',
          'access-control-allow-methods': 'GET,POST,OPTIONS',
          'access-control-allow-headers': 'content-type,authorization,x-init-data',
          'access-control-max-age': '86400',
        },
      });
    }

    try {
      /* ---- WebSocket ---- */
      if (path === '/ws') {
        const code = (url.searchParams.get('code') || '').toUpperCase();
        if (!/^[A-Z0-9]{4,8}$/.test(code)) return new Response('bad code', { status: 400 });
        const tok = url.searchParams.get('token') || '';
        const sess = await readSession(sessionSecret(env), tok);
        if (!sess) return new Response('unauthorized', { status: 401 });
        const stub = roomStub(env, code);
        const fwd = new URL(req.url);
        fwd.searchParams.set('uid', sess.uid);
        fwd.searchParams.set('name', sess.name || 'بازیکن');
        fwd.searchParams.set('photo', sess.photo || '');
        return stub.fetch(new Request(fwd.toString(), req));
      }

      /* ---- Telegram webhook ---- */
      if (path === '/telegram/webhook' && req.method === 'POST') {
        if (env.TELEGRAM_WEBHOOK_SECRET &&
            req.headers.get('x-telegram-bot-api-secret-token') !== env.TELEGRAM_WEBHOOK_SECRET) {
          return json({ ok: false }, { status: 403 });
        }
        const update = await req.json().catch(() => ({}));
        ctx.waitUntil(handleTelegramUpdate(env, update, url));
        return json({ ok: true });
      }

      /* ---- API ---- */
      if (path.startsWith('/api/')) return await api(req, env, ctx, url);

      /* ---- static-ish assets + app shell ---- */
      if (path === '/health') return json({ ok: true, ts: now(), name: APP_NAME });
      if (path === '/manifest.webmanifest') return manifest();
      if (path === '/icon.svg') return svgIcon();
      if (path === '/' || path === '/index.html' || path === '/app') {
        return new Response(APP_HTML(env), {
          headers: { 'content-type': 'text/html; charset=utf-8', 'cache-control': 'no-cache' },
        });
      }
      return new Response('Not found', { status: 404 });
    } catch (e) {
      console.log('worker error', e && e.stack || e);
      return json({ ok: false, error: 'server_error', detail: String(e && e.message) }, { status: 500 });
    }
  },

  /** Optional cron: cleanup old rooms. Configure [triggers] only for BYOK deploys. */
  async scheduled(event, env, ctx) {
    ctx.waitUntil((async () => {
      await ensureSchema(env);
      if (!env.DB) return;
      const cutoff = now() - 24 * 3600 * 1000;
      await env.DB.prepare(`DELETE FROM rooms WHERE updated_at < ?`).bind(cutoff).run().catch(() => {});
      await env.DB.prepare(`DELETE FROM chat_log WHERE ts < ?`).bind(cutoff).run().catch(() => {});
    })());
  },
};

/* ---------- REST API ---------------------------------------------------------- */

async function api(req, env, ctx, url) {
  const path = url.pathname.replace(/^\/api/, '');
  await ensureSchema(env);

  /* POST /api/auth — exchange Telegram initData (or guest) for a session token */
  if (path === '/auth' && req.method === 'POST') {
    const body = await req.json().catch(() => ({}));
    let user = null;

    if (body.initData) {
      const v = await verifyInitData(body.initData, env.TELEGRAM_BOT_TOKEN, Number(env.INITDATA_MAX_AGE || 86400));
      if (v) user = tgToUser(v.user, v.startParam);
      else if (String(env.ALLOW_GUEST || 'true') !== 'true') return bad('initData نامعتبر است', 401);
    }
    if (!user) {
      if (String(env.ALLOW_GUEST || 'true') !== 'true') return bad('ورود فقط از تلگرام', 401);
      const gid = (body.guestId && /^[a-zA-Z0-9_-]{6,40}$/.test(body.guestId)) ? body.guestId : uid8();
      user = {
        uid: 'g:' + gid, tg_id: null, name: sanitizeName(body.name, 'مهمان'),
        username: '', photo: '', lang: 'fa', is_guest: 1, startParam: body.startParam || '',
      };
    }

    ctx.waitUntil(DB.upsertUser(env, {
      uid: user.uid, tg_id: user.tg_id, username: user.username,
      first_name: user.name, photo_url: user.photo, lang: user.lang, is_guest: user.is_guest,
    }).catch(() => {}));

    const token = await signSession(sessionSecret(env), {
      uid: user.uid, name: user.name, photo: user.photo,
      guest: !!user.is_guest,
      exp: Math.floor(Date.now() / 1000) + 30 * 86400,
    });
    return json({
      ok: true, token, user: { uid: user.uid, name: user.name, photo: user.photo, guest: !!user.is_guest },
      startParam: user.startParam || '',
      aiAvailable: collectKeys(env).length > 0,
      botUsername: env.TELEGRAM_BOT_USERNAME || '',
      miniAppName: env.TELEGRAM_MINIAPP_NAME || '',
    });
  }

  const sess = await authFrom(req, env);
  if (!sess) return bad('unauthorized', 401);

  /* POST /api/rooms — create */
  if (path === '/rooms' && req.method === 'POST') {
    const body = await req.json().catch(() => ({}));
    const mode = Number(body.mode) === 2 ? 2 : 4;
    let code = roomCode();
    for (let i = 0; i < 5; i++) {
      const exist = await DB.getRoom(env, code);
      if (!exist) break;
      code = roomCode();
    }
    const settings = {
      targetPoints: clamp(Number(body.targetPoints) || (mode === 2 ? DEFAULTS.targetPoints2 : DEFAULTS.targetPoints4), 1, 21),
      turnSeconds: clamp(Number(body.turnSeconds) || DEFAULTS.turnSeconds, 10, 180),
      botLevel: ['easy', 'normal', 'hard', 'ai'].includes(body.botLevel) ? body.botLevel : 'normal',
      useLLM: !!body.useLLM && collectKeys(env).length > 0,
      kotRule: body.kotRule !== false,
      revealRejected: body.revealRejected !== false,
      hakemMethod: body.hakemMethod === 'random' ? 'random' : 'ace',
      autoFillBots: body.autoFillBots !== false,
      isPrivate: !!body.isPrivate,
    };
    const stub = roomStub(env, code);
    await stub.fetch('https://do/do/init', {
      method: 'POST',
      body: JSON.stringify({ code, mode, settings, host: { uid: sess.uid, name: sess.name } }),
    });
    await DB.touchRoom(env, {
      code, mode, host_uid: sess.uid, status: 'lobby', settings,
      players: [], is_private: settings.isPrivate ? 1 : 0,
    });
    return json({ ok: true, code, mode, settings });
  }

  /* GET /api/rooms/:code */
  const mRoom = path.match(/^\/rooms\/([A-Za-z0-9]{4,8})$/);
  if (mRoom && req.method === 'GET') {
    const code = mRoom[1].toUpperCase();
    const stub = roomStub(env, code);
    const r = await stub.fetch('https://do/do/info');
    const d = await r.json();
    if (!d.exists) return json({ ok: false, error: 'not_found' }, { status: 404 });
    return json({ ok: true, room: d.info });
  }

  /* GET /api/rooms — public lobby list */
  if (path === '/rooms' && req.method === 'GET') {
    return json({ ok: true, rooms: await DB.publicRooms(env) });
  }

  /* POST /api/quick — instant single-player game vs bots */
  if (path === '/quick' && req.method === 'POST') {
    const body = await req.json().catch(() => ({}));
    const mode = Number(body.mode) === 2 ? 2 : 4;
    const code = roomCode();
    const settings = {
      targetPoints: mode === 2 ? DEFAULTS.targetPoints2 : DEFAULTS.targetPoints4,
      turnSeconds: clamp(Number(body.turnSeconds) || 45, 10, 180),
      botLevel: ['easy', 'normal', 'hard', 'ai'].includes(body.botLevel) ? body.botLevel : 'normal',
      useLLM: !!body.useLLM && collectKeys(env).length > 0,
      kotRule: true, revealRejected: true, hakemMethod: 'ace',
      autoFillBots: true, isPrivate: true,
    };
    const stub = roomStub(env, code);
    await stub.fetch('https://do/do/init', {
      method: 'POST',
      body: JSON.stringify({ code, mode, settings, host: { uid: sess.uid, name: sess.name } }),
    });
    return json({ ok: true, code, mode, quick: true });
  }

  /* GET /api/me */
  if (path === '/me' && req.method === 'GET') {
    const [st, hist] = await Promise.all([DB.myStats(env, sess.uid), DB.myHistory(env, sess.uid, 15)]);
    return json({ ok: true, user: { uid: sess.uid, name: sess.name, photo: sess.photo }, stats: st, history: hist });
  }

  /* GET /api/leaderboard */
  if (path === '/leaderboard' && req.method === 'GET') {
    return json({ ok: true, top: await DB.leaderboard(env, 30) });
  }

  /* GET /api/ai/status — key pool diagnostics (no secrets leaked) */
  if (path === '/ai/status' && req.method === 'GET') {
    const keys = collectKeys(env);
    const health = await DB.keyHealth(env);
    const hashes = await Promise.all(keys.map(async k => (await sha256Hex(k)).slice(0, 16)));
    return json({
      ok: true,
      enabled: keys.length > 0 && String(env.AI_ENABLED ?? 'true') !== 'false',
      count: keys.length,
      model: env.AI_MODEL || 'gpt-4o-mini',
      baseUrl: env.AI_BASE_URL || 'https://api.openai.com/v1',
      keys: hashes.map((h, i) => ({
        n: i + 1, id: h.slice(0, 6),
        ok: health[h]?.ok || 0, fail: health[h]?.fail || 0,
        cooling: (health[h]?.cooldown_until || 0) > now(),
        lastError: health[h]?.last_error || null,
      })),
    });
  }

  /* POST /api/ai/test — verify the pool actually works */
  if (path === '/ai/test' && req.method === 'POST') {
    const out = await llmComplete(env, [{ role: 'user', content: 'Reply with the single word: OK' }], { maxTokens: 5 });
    return json({ ok: !!out, reply: out || null });
  }

  /* POST /api/telegram/setup — one-shot bot wiring (webhook + menu button) */
  if (path === '/telegram/setup' && req.method === 'POST') {
    if (!env.ADMIN_SECRET) return bad('ADMIN_SECRET تنظیم نشده است', 400);
    const body = await req.json().catch(() => ({}));
    if (body.adminSecret !== env.ADMIN_SECRET) return bad('forbidden', 403);
    const origin = env.PUBLIC_URL || url.origin;
    const res1 = await tgApi(env, 'setWebhook', {
      url: origin + '/telegram/webhook',
      secret_token: env.TELEGRAM_WEBHOOK_SECRET || undefined,
      allowed_updates: ['message', 'callback_query', 'inline_query'],
    });
    const res2 = await tgApi(env, 'setChatMenuButton', {
      menu_button: { type: 'web_app', text: 'بازی حکم', web_app: { url: origin } },
    });
    const res3 = await tgApi(env, 'setMyCommands', {
      commands: [
        { command: 'start', description: 'شروع و باز کردن بازی' },
        { command: 'new', description: 'ساخت بازی جدید' },
        { command: 'join', description: 'پیوستن با کد اتاق' },
        { command: 'stats', description: 'آمار من' },
      ],
    });
    return json({ ok: true, webhook: res1, menu: res2, commands: res3, origin });
  }

  return json({ ok: false, error: 'not_found' }, { status: 404 });
}

/* ---------- Telegram bot handlers --------------------------------------------- */

async function handleTelegramUpdate(env, update, url) {
  const origin = env.PUBLIC_URL || url.origin;
  const msg = update.message || update.edited_message;

  if (update.inline_query) {
    await tgApi(env, 'answerInlineQuery', {
      inline_query_id: update.inline_query.id,
      cache_time: 5,
      results: [{
        type: 'article', id: '1', title: 'بازی حکم بساز',
        description: 'یک میز حکم ۴ نفره یا ۲ نفره بساز و دوستانت را دعوت کن',
        input_message_content: { message_text: `🎴 بیا حکم بازی کنیم!\n${origin}`, parse_mode: 'HTML' },
      }],
    });
    return;
  }

  if (!msg || !msg.text) return;
  const chatId = msg.chat.id;
  const text = msg.text.trim();
  const kb = (extra) => ({
    inline_keyboard: [[{ text: '🎴 باز کردن بازی', web_app: { url: origin + (extra || '') } }]],
  });

  if (/^\/start/.test(text)) {
    const param = text.split(/\s+/)[1] || '';
    const deep = param && /^[A-Za-z0-9]{4,8}$/.test(param) ? ('?tgWebAppStartParam=' + param) : '';
    await tgApi(env, 'sendMessage', {
      chat_id: chatId,
      parse_mode: 'HTML',
      text: `<b>🎴 ${APP_NAME}</b>\n\nحکم ایرانی، ۴ نفره (تیمی) و ۲ نفره (قوانین ویژه).\n` +
        `• اتاق بساز و کد ۵ حرفی را برای دوستانت بفرست\n` +
        `• کمبود بازیکن؟ ربات هوشمند جایگزین می‌شود\n` +
        `• قطع شدی؟ همان صندلی برایت نگه داشته می‌شود\n\n` +
        (param ? `کد اتاق: <code>${param}</code>\n\n` : '') +
        `برای شروع دکمه زیر را بزن 👇`,
      reply_markup: kb(deep),
    });
    return;
  }
  if (/^\/new/.test(text)) {
    await tgApi(env, 'sendMessage', { chat_id: chatId, text: 'میز جدید بساز 👇', reply_markup: kb('?new=1') });
    return;
  }
  if (/^\/join/.test(text)) {
    const code = (text.split(/\s+/)[1] || '').toUpperCase();
    if (!/^[A-Z0-9]{4,8}$/.test(code)) {
      await tgApi(env, 'sendMessage', { chat_id: chatId, text: 'فرمت درست: /join ABCDE' });
      return;
    }
    await tgApi(env, 'sendMessage', {
      chat_id: chatId, text: `پیوستن به اتاق ${code} 👇`,
      reply_markup: { inline_keyboard: [[{ text: '🎴 ورود به اتاق ' + code, web_app: { url: origin + '?tgWebAppStartParam=' + code } }]] },
    });
    return;
  }
  if (/^\/stats/.test(text)) {
    const uid = 'tg:' + msg.from.id;
    const st = await DB.myStats(env, uid);
    await tgApi(env, 'sendMessage', {
      chat_id: chatId, parse_mode: 'HTML',
      text: st
        ? `<b>📊 آمار تو</b>\nبازی‌ها: ${st.games}\nبرد: ${st.wins}\nباخت: ${st.losses}\nکت: ${st.kots}\nامتیاز رتبه: ${st.rating}`
        : 'هنوز بازی‌ای انجام نداده‌ای! 🎴',
      reply_markup: kb(),
    });
    return;
  }
  await tgApi(env, 'sendMessage', { chat_id: chatId, text: 'برای شروع /start را بزن 🎴', reply_markup: kb() });
}

function manifest() {
  return new Response(JSON.stringify({
    name: APP_NAME, short_name: 'حکم', lang: 'fa', dir: 'rtl',
    start_url: '/', display: 'standalone',
    background_color: '#0b3d2e', theme_color: '#0b3d2e',
    icons: [{ src: '/icon.svg', sizes: 'any', type: 'image/svg+xml' }],
  }), { headers: { 'content-type': 'application/manifest+json; charset=utf-8' } });
}

function svgIcon() {
  const svg = `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 192 192">
  <defs><linearGradient id="g" x1="0" y1="0" x2="1" y2="1">
    <stop offset="0" stop-color="#0f5132"/><stop offset="1" stop-color="#052e1c"/></linearGradient></defs>
  <rect width="192" height="192" rx="42" fill="url(#g)"/>
  <g transform="translate(96 100)">
    <rect x="-52" y="-46" width="66" height="92" rx="10" fill="#fff" transform="rotate(-14)"/>
    <rect x="-14" y="-46" width="66" height="92" rx="10" fill="#f8fafc" transform="rotate(12)"/>
    <text x="14" y="20" font-size="56" text-anchor="middle" fill="#dc2626" transform="rotate(12)">♥</text>
    <text x="-24" y="14" font-size="48" text-anchor="middle" fill="#111827" transform="rotate(-14)">♠</text>
  </g></svg>`;
  return new Response(svg, { headers: { 'content-type': 'image/svg+xml; charset=utf-8', 'cache-control': 'public, max-age=86400' } });
}

/* =====================================================================================
 * SECTION 8 — MINI APP FRONTEND (single inlined document: RTL Persian, mobile-first)
 *   Rendering strategy: full snapshot -> declarative re-render of a small DOM tree.
 *   No framework, no CDN dependency (works inside Telegram with poor connectivity).
 * ===================================================================================*/

function APP_HTML(env) {
  const cfg = JSON.stringify({
    botUsername: env.TELEGRAM_BOT_USERNAME || '',
    miniAppName: env.TELEGRAM_MINIAPP_NAME || '',
    aiAvailable: collectKeys(env).length > 0,
    publicUrl: env.PUBLIC_URL || '',
    appName: APP_NAME,
  });

  return `<!DOCTYPE html>
<html lang="fa" dir="rtl">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover,maximum-scale=1,user-scalable=no">
<meta name="theme-color" content="#08301f">
<title>${APP_NAME}</title>
<link rel="manifest" href="/manifest.webmanifest">
<link rel="icon" href="/icon.svg">
<script src="https://telegram.org/js/telegram-web-app.js"></script>
<style>
:root{
  --felt1:#0f6b45; --felt2:#07452c; --felt3:#032015;
  --gold:#e9c46a; --gold2:#b8860b;
  --ink:#f4f7f5; --muted:#a9c3b6;
  --card-w:clamp(46px,13.2vw,64px);
  --radius:18px;
  --t1:#43a5ff; --t2:#ff7a59;
  --safe-t:env(safe-area-inset-top,0px); --safe-b:env(safe-area-inset-bottom,0px);
  --tg-bg:#08301f;
}
*{box-sizing:border-box;-webkit-tap-highlight-color:transparent}
html,body{margin:0;padding:0;height:100%;overflow:hidden}
body{
  font-family:'Vazirmatn','IRANSans',system-ui,-apple-system,'Segoe UI',Tahoma,sans-serif;
  color:var(--ink); background:var(--tg-bg);
  -webkit-user-select:none;user-select:none;
  touch-action:manipulation;
}
/* ---------- animated felt background ---------- */
#bg{position:fixed;inset:0;z-index:0;overflow:hidden;background:
  radial-gradient(115% 80% at 50% 8%, var(--felt1) 0%, var(--felt2) 46%, var(--felt3) 100%)}
#bg:before{content:'';position:absolute;inset:-20%;
  background-image:
    radial-gradient(circle at 20% 30%, rgba(255,255,255,.055) 0 2px, transparent 3px),
    radial-gradient(circle at 70% 60%, rgba(255,255,255,.045) 0 2px, transparent 3px);
  background-size:26px 26px, 34px 34px; opacity:.5;
  animation:drift 40s linear infinite}
#bg:after{content:'';position:absolute;inset:0;
  background:radial-gradient(70% 50% at 50% 42%, rgba(255,255,255,.10), transparent 70%),
             linear-gradient(180deg, rgba(0,0,0,.28), transparent 30%, rgba(0,0,0,.45));
  pointer-events:none}
@keyframes drift{to{transform:translate3d(26px,34px,0)}}
.orb{position:absolute;border-radius:50%;filter:blur(42px);opacity:.30;mix-blend-mode:screen;
  animation:float 18s ease-in-out infinite}
.orb.a{width:52vw;height:52vw;background:#25d07a;top:-14vw;right:-12vw}
.orb.b{width:44vw;height:44vw;background:#0d7fd1;bottom:-12vw;left:-10vw;animation-delay:-6s}
.orb.c{width:34vw;height:34vw;background:#e9c46a;top:38%;left:56%;opacity:.16;animation-delay:-11s}
@keyframes float{0%,100%{transform:translate(0,0) scale(1)}50%{transform:translate(-4vw,5vh) scale(1.1)}}
.suitdeco{position:absolute;font-size:26vw;opacity:.035;color:#fff;pointer-events:none}
.suitdeco.s1{top:4%;right:6%;transform:rotate(-14deg)}
.suitdeco.s2{bottom:2%;left:4%;transform:rotate(12deg)}

/* ---------- shell ---------- */
#app{position:relative;z-index:1;height:100%;display:flex;flex-direction:column;
  padding-top:var(--safe-t);padding-bottom:var(--safe-b)}
.scr{flex:1;min-height:0;display:none;flex-direction:column}
.scr.on{display:flex}
.pad{padding:14px 16px}
.scroll{overflow-y:auto;-webkit-overflow-scrolling:touch;flex:1;min-height:0}

/* ---------- generic components ---------- */
.glass{background:linear-gradient(180deg,rgba(255,255,255,.11),rgba(255,255,255,.05));
  border:1px solid rgba(255,255,255,.14);border-radius:var(--radius);
  backdrop-filter:blur(14px);-webkit-backdrop-filter:blur(14px);
  box-shadow:0 10px 34px rgba(0,0,0,.30)}
.btn{display:flex;align-items:center;justify-content:center;gap:8px;
  border:0;border-radius:16px;padding:14px 16px;font:inherit;font-weight:700;font-size:15px;
  color:#08301f;background:linear-gradient(180deg,#f6d98b,var(--gold));
  box-shadow:0 6px 18px rgba(233,196,106,.28), inset 0 1px 0 rgba(255,255,255,.55);
  cursor:pointer;transition:transform .12s, filter .12s, opacity .12s;width:100%}
.btn:active{transform:scale(.97);filter:brightness(.95)}
.btn.sec{background:linear-gradient(180deg,rgba(255,255,255,.16),rgba(255,255,255,.08));
  color:var(--ink);border:1px solid rgba(255,255,255,.18);box-shadow:none}
.btn.dark{background:linear-gradient(180deg,#0d5b3c,#08402a);color:#eafaf1;border:1px solid rgba(255,255,255,.12)}
.btn.danger{background:linear-gradient(180deg,#ff7a6b,#e04a3a);color:#fff}
.btn.sm{padding:9px 12px;font-size:13px;border-radius:12px;width:auto}
.btn.xs{padding:6px 9px;font-size:12px;border-radius:10px;width:auto}
.btn[disabled]{opacity:.45;pointer-events:none}
.row{display:flex;gap:10px;align-items:center}
.col{display:flex;flex-direction:column;gap:10px}
.grow{flex:1;min-width:0}
.h1{font-size:22px;font-weight:800;letter-spacing:-.3px}
.h2{font-size:16px;font-weight:800}
.mut{color:var(--muted);font-size:12.5px;line-height:1.75}
.center{text-align:center}
input,select{font:inherit;width:100%;padding:13px 14px;border-radius:14px;
  border:1px solid rgba(255,255,255,.18);background:rgba(0,0,0,.24);color:var(--ink);outline:none}
input::placeholder{color:#7f998d}
.chip{padding:7px 11px;border-radius:999px;font-size:12.5px;font-weight:700;
  background:rgba(0,0,0,.3);border:1px solid rgba(255,255,255,.14)}
.seg{display:flex;background:rgba(0,0,0,.3);border-radius:14px;padding:4px;gap:4px;
  border:1px solid rgba(255,255,255,.12)}
.seg button{flex:1;border:0;background:transparent;color:var(--muted);font:inherit;font-weight:700;
  padding:10px 6px;border-radius:11px;font-size:13.5px;cursor:pointer;transition:.15s}
.seg button.on{background:linear-gradient(180deg,#f6d98b,var(--gold));color:#08301f}
.sw{display:flex;align-items:center;justify-content:space-between;gap:10px;padding:11px 2px}
.toggle{width:48px;height:28px;border-radius:999px;background:rgba(0,0,0,.4);position:relative;
  border:1px solid rgba(255,255,255,.16);flex:0 0 auto;cursor:pointer;transition:.18s}
.toggle b{position:absolute;top:2px;right:2px;width:22px;height:22px;border-radius:50%;
  background:#cfe6da;transition:.18s}
.toggle.on{background:linear-gradient(90deg,var(--gold2),var(--gold))}
.toggle.on b{right:24px;background:#fff}

/* ---------- home ---------- */
.logo{display:flex;flex-direction:column;align-items:center;gap:6px;padding:22px 0 10px}
.logocards{position:relative;height:86px;width:120px}
.logocards i{position:absolute;width:56px;height:80px;border-radius:10px;background:#fff;
  box-shadow:0 8px 22px rgba(0,0,0,.4);display:grid;place-items:center;font-size:30px;font-style:normal}
.logocards i:nth-child(1){transform:rotate(-16deg) translateX(14px);color:#111}
.logocards i:nth-child(2){transform:rotate(4deg) translateX(38px);color:#dc2626;z-index:2}
.title{font-size:27px;font-weight:900;
  background:linear-gradient(180deg,#fff,var(--gold));-webkit-background-clip:text;background-clip:text;
  -webkit-text-fill-color:transparent}
.tile{display:flex;align-items:center;gap:12px;padding:14px;border-radius:16px;cursor:pointer;
  background:linear-gradient(180deg,rgba(255,255,255,.10),rgba(255,255,255,.04));
  border:1px solid rgba(255,255,255,.13);transition:transform .12s}
.tile:active{transform:scale(.985)}
.tile .ic{width:44px;height:44px;border-radius:13px;display:grid;place-items:center;font-size:21px;
  background:linear-gradient(180deg,rgba(233,196,106,.28),rgba(233,196,106,.10));flex:0 0 auto}
.tile b{display:block;font-size:15px}
.tile span{font-size:12px;color:var(--muted)}

/* ---------- table ---------- */
#table{position:relative;flex:1 1 auto;min-height:0;overflow:hidden}
.topbar{display:flex;align-items:center;gap:8px;padding:8px 12px}
.pill{display:flex;align-items:center;gap:6px;padding:6px 10px;border-radius:999px;font-size:12px;
  font-weight:800;background:rgba(0,0,0,.34);border:1px solid rgba(255,255,255,.14)}
.pill.t0{border-color:rgba(67,165,255,.6)} .pill.t1{border-color:rgba(255,122,89,.6)}
.trumpb{display:flex;align-items:center;gap:5px;padding:6px 11px;border-radius:999px;font-weight:900;
  background:linear-gradient(180deg,#f6d98b,var(--gold));color:#08301f;font-size:13px}
.felt{position:absolute;inset:52px 10px 0 10px}
.seat{position:absolute;display:flex;flex-direction:column;align-items:center;gap:4px;width:96px;
  transform:translate(-50%,-50%);transition:.25s}
.seat .av{width:46px;height:46px;border-radius:50%;display:grid;place-items:center;font-size:19px;font-weight:800;
  background:linear-gradient(180deg,#12694a,#0a3f2b);border:2px solid rgba(255,255,255,.22);
  box-shadow:0 6px 16px rgba(0,0,0,.35);position:relative;overflow:visible}
.seat .av img{width:100%;height:100%;border-radius:50%;object-fit:cover}
.seat.turn .av{border-color:var(--gold);box-shadow:0 0 0 4px rgba(233,196,106,.25),0 0 22px rgba(233,196,106,.5);
  animation:pulse 1.6s ease-in-out infinite}
@keyframes pulse{50%{box-shadow:0 0 0 8px rgba(233,196,106,.12),0 0 26px rgba(233,196,106,.65)}}
.seat.off .av{filter:grayscale(.7) brightness(.8)}
.seat .nm{font-size:11.5px;font-weight:700;max-width:96px;overflow:hidden;text-overflow:ellipsis;
  white-space:nowrap;text-shadow:0 1px 3px rgba(0,0,0,.6)}
.seat .meta{display:flex;gap:4px;align-items:center;font-size:10px;color:var(--muted)}
.seat .team{position:absolute;top:-4px;left:-4px;width:14px;height:14px;border-radius:50%;
  border:2px solid rgba(0,0,0,.4)}
.seat .team.t0{background:var(--t1)} .seat .team.t1{background:var(--t2)}
.seat .crown{position:absolute;top:-13px;right:-6px;font-size:14px}
.seat .cardsn{position:absolute;bottom:-3px;left:-6px;background:rgba(0,0,0,.7);border-radius:9px;
  font-size:9.5px;padding:1px 5px;font-weight:800}
.seat .ring{position:absolute;inset:-5px;border-radius:50%;pointer-events:none}
.seat .ring svg{width:100%;height:100%;transform:rotate(-90deg)}
.hakemtag{background:linear-gradient(180deg,#f6d98b,var(--gold));color:#08301f;
  border-radius:8px;font-size:9.5px;font-weight:900;padding:1px 6px}
.emo{position:absolute;top:-16px;left:50%;transform:translateX(-50%);font-size:22px;
  animation:pop .9s ease-out forwards;pointer-events:none}
@keyframes pop{0%{transform:translateX(-50%) scale(.4);opacity:0}30%{transform:translateX(-50%) scale(1.25);opacity:1}100%{transform:translateX(-50%) translateY(-24px) scale(1);opacity:0}}

/* center trick area */
.tarea{position:absolute;left:50%;top:50%;transform:translate(-50%,-50%);
  width:min(70vw,260px);height:min(70vw,260px);border-radius:50%;
  background:radial-gradient(circle at 50% 40%, rgba(255,255,255,.10), rgba(0,0,0,.20) 70%);
  border:1px solid rgba(255,255,255,.10);box-shadow:inset 0 0 40px rgba(0,0,0,.35)}
.tcard{position:absolute;left:50%;top:50%;animation:toss .28s cubic-bezier(.2,.9,.3,1.2)}
@keyframes toss{from{opacity:0;transform:translate(-50%,-50%) scale(.7)}}
.card{width:var(--card-w);height:calc(var(--card-w)*1.45);border-radius:9px;background:#fff;color:#111;
  position:relative;box-shadow:0 5px 14px rgba(0,0,0,.4);flex:0 0 auto;
  display:flex;flex-direction:column;justify-content:space-between;padding:4px 5px;
  font-weight:900;line-height:1}
.card.red{color:#d81f2a}
.card .r{font-size:calc(var(--card-w)*.30)}
.card .s{font-size:calc(var(--card-w)*.28);align-self:flex-end}
.card .big{position:absolute;inset:0;display:grid;place-items:center;
  font-size:calc(var(--card-w)*.60);opacity:.16}
.card.back{background:
  repeating-linear-gradient(45deg,#0e5c3e 0 6px,#0a4530 6px 12px);border:2px solid #e9c46a55}
.card.back:after{content:'♠';position:absolute;inset:0;display:grid;place-items:center;
  font-size:calc(var(--card-w)*.5);color:rgba(233,196,106,.5)}
.card.sel{transform:translateY(-16px);box-shadow:0 12px 22px rgba(0,0,0,.5),0 0 0 2px var(--gold)}
.card.dim{filter:brightness(.55) saturate(.6)}
.card.pl{cursor:pointer}
.card.hl{box-shadow:0 6px 16px rgba(0,0,0,.4),0 0 0 2px rgba(233,196,106,.8)}

/* hand */
.hand{display:flex;justify-content:center;align-items:flex-end;
  padding:10px 10px calc(8px + var(--safe-b));min-height:calc(var(--card-w)*1.62);
  flex:0 0 auto;overflow:visible}
/* --overlap is set per render from the card count so a 13-card fan always fits */
.hand .card{margin-inline-start:calc(var(--card-w) * var(--overlap, -0.36));
  transition:transform .16s, box-shadow .16s}
.hand .card:first-child{margin-inline-start:0}
.hand .card:active{transform:translateY(-10px)}
.hand .card.pl:hover{transform:translateY(-8px)}
.actbar{display:flex;gap:8px;padding:0 12px 4px;align-items:center;justify-content:center;
  flex-wrap:wrap;flex:0 0 auto}
.banner{position:absolute;left:50%;top:38%;transform:translate(-50%,-50%);z-index:20;
  padding:16px 22px;border-radius:20px;text-align:center;min-width:70%;
  background:linear-gradient(180deg,rgba(8,48,31,.96),rgba(3,26,17,.96));
  border:1px solid rgba(233,196,106,.4);box-shadow:0 20px 60px rgba(0,0,0,.6);
  animation:bin .3s ease-out}
@keyframes bin{from{opacity:0;transform:translate(-50%,-50%) scale(.9)}}
.suitpick{display:grid;grid-template-columns:repeat(4,1fr);gap:8px;margin-top:12px}
.suitpick button{border:0;border-radius:14px;padding:12px 4px;font-size:26px;background:#fff;cursor:pointer;
  box-shadow:0 6px 16px rgba(0,0,0,.35);transition:transform .12s}
.suitpick button:active{transform:scale(.94)}
.suitpick button.red{color:#d81f2a}
.toast{position:fixed;left:50%;bottom:calc(16px + var(--safe-b));transform:translateX(-50%);z-index:60;
  padding:10px 16px;border-radius:14px;background:rgba(0,0,0,.85);font-size:13px;font-weight:700;
  border:1px solid rgba(255,255,255,.16);animation:tin .25s;max-width:88vw;text-align:center}
@keyframes tin{from{opacity:0;transform:translate(-50%,12px)}}
.sheet{position:fixed;inset:0;z-index:70;background:rgba(0,0,0,.55);display:none;
  align-items:flex-end;backdrop-filter:blur(3px)}
.sheet.on{display:flex}
.sheetbox{width:100%;max-height:86vh;overflow-y:auto;border-radius:22px 22px 0 0;
  background:linear-gradient(180deg,#0c4b33,#062d1e);border-top:1px solid rgba(233,196,106,.3);
  padding:14px 16px calc(18px + var(--safe-b));animation:up .26s cubic-bezier(.2,.9,.3,1)}
@keyframes up{from{transform:translateY(100%)}}
.hbar{width:44px;height:4px;border-radius:9px;background:rgba(255,255,255,.3);margin:0 auto 12px}
.list{display:flex;flex-direction:column;gap:8px}
.li{display:flex;align-items:center;gap:10px;padding:10px 12px;border-radius:14px;
  background:rgba(0,0,0,.25);border:1px solid rgba(255,255,255,.10)}
.chatlog{max-height:180px;overflow-y:auto;display:flex;flex-direction:column;gap:6px;font-size:13px}
.msg{padding:7px 10px;border-radius:12px;background:rgba(0,0,0,.3);align-self:flex-start;max-width:85%}
.msg.me{align-self:flex-end;background:rgba(233,196,106,.22)}
.msg b{font-size:11px;color:var(--gold);display:block}
.scoreboard{display:flex;gap:8px}
.sb{flex:1;padding:10px;border-radius:14px;text-align:center;background:rgba(0,0,0,.28);
  border:1px solid rgba(255,255,255,.12)}
.sb b{font-size:24px;display:block}
.sb.t0{border-color:rgba(67,165,255,.55)} .sb.t1{border-color:rgba(255,122,89,.55)}
.lb{display:flex;align-items:center;gap:10px;padding:9px 11px;border-radius:13px;background:rgba(0,0,0,.24)}
.lb .n{width:26px;height:26px;border-radius:50%;display:grid;place-items:center;font-weight:900;font-size:12px;
  background:rgba(233,196,106,.22)}
.rej{display:flex;gap:5px;flex-wrap:wrap;margin-top:8px}
.rej .card{--card-w:34px}
.fade{animation:fi .25s}@keyframes fi{from{opacity:0}}
.spin{width:26px;height:26px;border-radius:50%;border:3px solid rgba(255,255,255,.2);
  border-top-color:var(--gold);animation:sp .8s linear infinite;margin:0 auto}
@keyframes sp{to{transform:rotate(360deg)}}
.conn{position:fixed;top:calc(4px + var(--safe-t));left:50%;transform:translateX(-50%);z-index:80;
  font-size:11.5px;font-weight:800;padding:5px 12px;border-radius:999px;background:#7a1d1d;display:none}
.conn.on{display:block}
</style>
</head>
<body>
<div id="bg">
  <div class="orb a"></div><div class="orb b"></div><div class="orb c"></div>
  <div class="suitdeco s1">♠</div><div class="suitdeco s2">♥</div>
</div>
<div class="conn" id="conn">در حال اتصال…</div>
<div id="app">

  <!-- ================= HOME ================= -->
  <section class="scr on" id="scrHome">
    <div class="scroll pad">
      <div class="logo">
        <div class="logocards"><i>♠</i><i>♥</i></div>
        <div class="title">حکم آنلاین</div>
        <div class="mut center">حکم ایرانی ۴ نفره و ۲ نفره — با دوستان یا ربات هوشمند</div>
      </div>

      <div class="col" style="margin-top:6px">
        <div class="tile" onclick="UI.go('new')">
          <div class="ic">🎴</div>
          <div class="grow"><b>ساخت میز جدید</b><span>۴ نفره تیمی یا ۲ نفره ویژه</span></div>
          <div style="opacity:.5">‹</div>
        </div>
        <div class="tile" onclick="UI.go('join')">
          <div class="ic">🔑</div>
          <div class="grow"><b>پیوستن با کد</b><span>کد ۵ حرفی اتاق را وارد کن</span></div>
          <div style="opacity:.5">‹</div>
        </div>
        <div class="tile" onclick="Net.quick(4)">
          <div class="ic">⚡</div>
          <div class="grow"><b>بازی سریع با ربات</b><span>بدون انتظار، همین حالا شروع کن</span></div>
          <div style="opacity:.5">‹</div>
        </div>
        <div class="row">
          <div class="tile grow" onclick="UI.openRooms()">
            <div class="ic">🌐</div><div class="grow"><b>میزهای عمومی</b><span>پیوستن سریع</span></div>
          </div>
        </div>
        <div class="row">
          <div class="tile grow" onclick="UI.openMe()"><div class="ic">📊</div><div class="grow"><b>پروفایل</b><span>آمار من</span></div></div>
          <div class="tile grow" onclick="UI.openTop()"><div class="ic">🏆</div><div class="grow"><b>رتبه‌بندی</b><span>بهترین‌ها</span></div></div>
        </div>
        <div class="tile" onclick="UI.openRules()">
          <div class="ic">📖</div><div class="grow"><b>قوانین بازی</b><span>حکم ۴ نفره و ۲ نفره</span></div>
        </div>
      </div>
      <div class="mut center" style="margin-top:16px" id="whoami"></div>
    </div>
  </section>

  <!-- ================= NEW ROOM ================= -->
  <section class="scr" id="scrNew">
    <div class="scroll pad">
      <div class="h1" style="margin-bottom:12px">میز جدید</div>
      <div class="glass pad col">
        <div>
          <div class="h2" style="margin-bottom:8px">حالت بازی</div>
          <div class="seg" id="modeSeg">
            <button class="on" data-m="4" onclick="UI.setMode(4)">۴ نفره (تیمی)</button>
            <button data-m="2" onclick="UI.setMode(2)">۲ نفره (ویژه)</button>
          </div>
          <div class="mut" id="modeHint" style="margin-top:8px"></div>
        </div>
        <div class="row">
          <div class="grow"><div class="mut">امتیاز برد</div><input id="tp" type="number" min="1" max="21" value="7"></div>
          <div class="grow"><div class="mut">زمان نوبت (ثانیه)</div><input id="ts" type="number" min="10" max="180" value="30"></div>
        </div>
        <div>
          <div class="mut" style="margin-bottom:6px">سطح ربات‌ها</div>
          <div class="seg" id="lvlSeg">
            <button data-l="easy" onclick="UI.setLvl('easy')">ساده</button>
            <button class="on" data-l="normal" onclick="UI.setLvl('normal')">معمولی</button>
            <button data-l="hard" onclick="UI.setLvl('hard')">حرفه‌ای</button>
            <button data-l="ai" onclick="UI.setLvl('ai')">هوش مصنوعی</button>
          </div>
          <div class="mut" id="aiHint" style="margin-top:6px"></div>
        </div>
        <div class="sw"><div><b style="font-size:14px">قانون کت</b><div class="mut">۷-۰ ⇒ ۲ امتیاز، کت حاکم ⇒ ۳</div></div>
          <div class="toggle on" id="tgKot" onclick="UI.tg(this)"></div></div>
        <div class="sw"><div><b style="font-size:14px">پر کردن خودکار با ربات</b><div class="mut">صندلی‌های خالی ربات می‌گیرند</div></div>
          <div class="toggle on" id="tgFill" onclick="UI.tg(this)"></div></div>
        <div class="sw"><div><b style="font-size:14px">میز خصوصی</b><div class="mut">در لیست عمومی نشان داده نشود</div></div>
          <div class="toggle" id="tgPriv" onclick="UI.tg(this)"></div></div>
        <div class="sw" id="rowReveal"><div><b style="font-size:14px">نمایش کارت ردشده</b><div class="mut">۲ نفره: کارتی که دور انداخته می‌شود دیده شود</div></div>
          <div class="toggle on" id="tgRev" onclick="UI.tg(this)"></div></div>
        <button class="btn" onclick="Net.createRoom()">ساخت میز و دعوت</button>
        <button class="btn sec" onclick="UI.go('home')">بازگشت</button>
      </div>
    </div>
  </section>

  <!-- ================= JOIN ================= -->
  <section class="scr" id="scrJoin">
    <div class="scroll pad">
      <div class="h1" style="margin-bottom:12px">پیوستن به میز</div>
      <div class="glass pad col">
        <div class="mut">کد اتاق را وارد کن (۵ حرف)</div>
        <input id="joinCode" placeholder="مثلاً: K7QMP" maxlength="8"
          style="text-align:center;font-size:26px;font-weight:900;letter-spacing:6px;direction:ltr"
          oninput="this.value=this.value.toUpperCase().replace(/[^A-Z0-9]/g,'')">
        <button class="btn" onclick="Net.join()">ورود به میز</button>
        <button class="btn sec" onclick="UI.go('home')">بازگشت</button>
      </div>
    </div>
  </section>

  <!-- ================= LOBBY ================= -->
  <section class="scr" id="scrLobby">
    <div class="scroll pad">
      <div class="row" style="margin-bottom:10px">
        <div class="grow"><div class="h1">اتاق انتظار</div><div class="mut" id="lobbyMode"></div></div>
        <div class="chip" onclick="UI.copyCode()" style="direction:ltr;font-size:17px;font-weight:900;letter-spacing:3px"
             id="lobbyCode">-----</div>
      </div>
      <div class="glass pad col" style="margin-bottom:10px">
        <button class="btn" onclick="UI.invite()">📤 دعوت دوستان</button>
        <div class="row"><button class="btn sec sm grow" onclick="UI.copyCode()">کپی کد</button>
          <button class="btn sec sm grow" onclick="UI.copyLink()">کپی لینک</button></div>
      </div>
      <div class="glass pad">
        <div class="h2" style="margin-bottom:10px">بازیکنان</div>
        <div class="list" id="lobbySeats"></div>
        <div class="mut" id="lobbyHint" style="margin-top:10px"></div>
      </div>
      <div class="glass pad col" id="hostBox" style="margin-top:10px;display:none">
        <div class="h2">کنترل میزبان</div>
        <div class="row" style="flex-wrap:wrap;gap:8px" id="hostBtns"></div>
        <button class="btn" id="btnStart" onclick="Net.send({t:'start'})">شروع بازی</button>
      </div>
      <div class="row" style="margin-top:10px">
        <button class="btn sec sm grow" onclick="UI.openChat()">💬 گفتگو</button>
        <button class="btn sec sm grow" onclick="UI.leave()">خروج</button>
      </div>
    </div>
  </section>

  <!-- ================= GAME ================= -->
  <section class="scr" id="scrGame">
    <div class="topbar">
      <div class="pill" onclick="UI.leave()">✕</div>
      <div class="pill t0" id="pillT0">۰</div>
      <div class="pill t1" id="pillT1">۰</div>
      <div class="grow"></div>
      <div class="trumpb" id="trumpBadge" style="display:none"></div>
      <div class="pill" id="pillTricks">۰-۰</div>
      <div class="pill" onclick="UI.openMenu()">☰</div>
    </div>
    <div id="table">
      <div class="felt" id="felt">
        <div class="tarea" id="tarea"></div>
      </div>
      <div id="banner"></div>
    </div>
    <div class="actbar" id="actbar"></div>
    <div class="hand" id="hand"></div>
  </section>
</div>

<div class="sheet" id="sheet" onclick="if(event.target===this)UI.closeSheet()">
  <div class="sheetbox"><div class="hbar"></div><div id="sheetBody"></div></div>
</div>
<script>window.__CFG__=${cfg};</script>
<script>
/* ===================================================================================
 *  CLIENT  — plain ES2019, no build step, no external deps.
 *  NOTE: this block lives inside a JS template literal on the server, therefore it
 *  intentionally avoids backticks and dollar-brace sequences.
 * =================================================================================*/
(function () {
'use strict';
var CFG = window.__CFG__ || {};
var TG = window.Telegram && window.Telegram.WebApp ? window.Telegram.WebApp : null;

var SUIT_CH = { S: '♠', H: '♥', D: '♦', C: '♣' };
var SUIT_NAME = { S: 'پیک', H: 'دل', D: 'خشت', C: 'خاج' };   // ♠ پیک | ♥ دل | ♦ خشت | ♣ خاج
var RANK_FA = { T: '10', J: 'J', Q: 'Q', K: 'K', A: 'A' };
var FA_DIGITS = ['۰','۱','۲','۳','۴','۵','۶','۷','۸','۹'];

function fa(n) { return String(n).replace(/[0-9]/g, function (d) { return FA_DIGITS[+d]; }); }
function el(id) { return document.getElementById(id); }
function esc(s) {
  return String(s == null ? '' : s).replace(/[&<>"']/g, function (c) {
    return ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' })[c];
  });
}
function haptic(kind) {
  try {
    if (!TG || !TG.HapticFeedback) return;
    if (kind === 'sel') TG.HapticFeedback.selectionChanged();
    else if (kind === 'ok') TG.HapticFeedback.notificationOccurred('success');
    else if (kind === 'err') TG.HapticFeedback.notificationOccurred('error');
    else if (kind === 'warn') TG.HapticFeedback.notificationOccurred('warning');
    else TG.HapticFeedback.impactOccurred(kind || 'light');
  } catch (e) {}
}

/* ---------------- state ---------------- */
var S = {
  token: null, me: null, code: null, snap: null,
  mode: 4, lvl: 'normal',
  ws: null, wsTries: 0, lastSeq: 0, seenEvent: 0,
  sel: [], screen: 'home', timer: null, pingTimer: null,
  aiAvailable: !!CFG.aiAvailable, startParam: '',
};
window.S = S;

/* ---------------- toast ---------------- */
var toastT = null;
function toast(msg, err) {
  var d = document.createElement('div');
  d.className = 'toast';
  d.textContent = msg;
  if (err) d.style.background = 'rgba(150,25,25,.92)';
  document.body.appendChild(d);
  clearTimeout(toastT);
  setTimeout(function () { d.remove(); }, 2600);
  haptic(err ? 'err' : 'sel');
}

/* ---------------- API ---------------- */
function apiFetch(path, opts) {
  opts = opts || {};
  var h = { 'content-type': 'application/json' };
  if (S.token) h['authorization'] = 'Bearer ' + S.token;
  return fetch('/api' + path, {
    method: opts.method || 'GET',
    headers: h,
    body: opts.body ? JSON.stringify(opts.body) : undefined,
  }).then(function (r) { return r.json().catch(function () { return { ok: false }; }); });
}

/* ---------------- boot ---------------- */
function guestId() {
  var k = 'hokm_guest';
  var v = null;
  try { v = localStorage.getItem(k); } catch (e) {}
  if (!v) { v = 'gu' + Math.random().toString(36).slice(2, 12); try { localStorage.setItem(k, v); } catch (e) {} }
  return v;
}

function boot() {
  if (TG) {
    try {
      TG.ready(); TG.expand();
      if (TG.enableClosingConfirmation) TG.enableClosingConfirmation();
      if (TG.setHeaderColor) TG.setHeaderColor('#08301f');
      if (TG.setBackgroundColor) TG.setBackgroundColor('#08301f');
      if (TG.disableVerticalSwipes) TG.disableVerticalSwipes();
      if (TG.BackButton) TG.BackButton.onClick(function () { onBack(); });
    } catch (e) {}
  }
  var initData = TG && TG.initData ? TG.initData : '';
  var qs = new URLSearchParams(location.search);
  var sp = (TG && TG.initDataUnsafe && TG.initDataUnsafe.start_param) || qs.get('tgWebAppStartParam') || qs.get('code') || '';

  apiFetch('/auth', { method: 'POST', body: { initData: initData, guestId: guestId(), name: (TG && TG.initDataUnsafe && TG.initDataUnsafe.user && TG.initDataUnsafe.user.first_name) || 'مهمان' } })
    .then(function (d) {
      if (!d.ok) { toast('ورود ناموفق بود', true); return; }
      S.token = d.token; S.me = d.user; S.aiAvailable = !!d.aiAvailable;
      CFG.botUsername = d.botUsername || CFG.botUsername;
      CFG.miniAppName = d.miniAppName || CFG.miniAppName;
      S.startParam = d.startParam || sp || '';
      el('whoami').textContent = (d.user.name || '') + (d.user.guest ? ' (مهمان)' : '') ;
      el('aiHint').textContent = S.aiAvailable
        ? 'کلید هوش مصنوعی فعال است ✅'
        : 'کلید AI تنظیم نشده — سطح «هوش مصنوعی» از موتور داخلی حرفه‌ای استفاده می‌کند';
      UI.setMode(4);
      var code = (S.startParam || '').toUpperCase().replace(/[^A-Z0-9]/g, '');
      if (/^[A-Z0-9]{4,8}$/.test(code)) { S.code = code; connect(code); }
      else if (qs.get('new')) UI.go('new');
    })
    .catch(function () { toast('خطای شبکه', true); });
}

/* ---------------- websocket ---------------- */
function wsUrl(code) {
  var proto = location.protocol === 'https:' ? 'wss:' : 'ws:';
  return proto + '//' + location.host + '/ws?code=' + encodeURIComponent(code) + '&token=' + encodeURIComponent(S.token);
}

function connect(code) {
  S.code = code;
  el('conn').classList.add('on');
  el('conn').textContent = 'در حال اتصال…';
  try { if (S.ws) { S.ws.onclose = null; S.ws.close(); } } catch (e) {}
  var ws = new WebSocket(wsUrl(code));
  S.ws = ws;
  ws.onopen = function () {
    S.wsTries = 0;
    el('conn').classList.remove('on');
    clearInterval(S.pingTimer);
    S.pingTimer = setInterval(function () {
      try { if (ws.readyState === 1) ws.send(JSON.stringify({ t: 'ping' })); } catch (e) {}
    }, 25000);
    haptic('ok');
  };
  ws.onmessage = function (ev) {
    var m;
    try { m = JSON.parse(ev.data); } catch (e) { return; }
    if (m.t === 'state') onState(m);
    else if (m.t === 'error') toast(m.m || 'خطا', true);
  };
  ws.onclose = function () {
    clearInterval(S.pingTimer);
    if (S.screen === 'home' || S.screen === 'new' || S.screen === 'join') return;
    S.wsTries++;
    el('conn').classList.add('on');
    el('conn').textContent = 'اتصال قطع شد — تلاش مجدد…';
    var wait = Math.min(8000, 700 * Math.pow(1.6, Math.min(S.wsTries, 6)));
    setTimeout(function () { if (S.code) connect(S.code); }, wait);
  };
  ws.onerror = function () {};
}

function send(msg) {
  try {
    if (S.ws && S.ws.readyState === 1) S.ws.send(JSON.stringify(msg));
    else toast('اتصال برقرار نیست', true);
  } catch (e) { toast('ارسال ناموفق', true); }
}

/* ---------------- state handling ---------------- */
function onState(m) {
  var prev = S.snap;
  S.snap = m;
  if (m.seq) S.lastSeq = m.seq;
  processEvents(prev, m);
  if (m.phase === 'lobby') { UI.go('lobby'); renderLobby(); }
  else { UI.go('game'); renderGame(); }
  syncMainButton();
}

function processEvents(prev, m) {
  var evs = m.events || [];
  for (var i = 0; i < evs.length; i++) {
    var e = evs[i];
    if (!e.ts || e.ts <= S.seenEvent) continue;
    S.seenEvent = e.ts;
    if (e.t === 'play') haptic('light');
    else if (e.t === 'trick') haptic(e.team === teamOfMe(m) ? 'ok' : 'light');
    else if (e.t === 'trump') toast('حکم: ' + SUIT_NAME[e.suit] + ' ' + SUIT_CH[e.suit]);
    else if (e.t === 'round_end') haptic(e.winnerTeam === teamOfMe(m) ? 'ok' : 'warn');
    else if (e.t === 'game_end') haptic(e.winnerTeam === teamOfMe(m) ? 'ok' : 'err');
    else if (e.t === 'offline') toast(e.name + ' قطع شد');
    else if (e.t === 'reconnect' && m.mySeat !== e.seat) toast(e.name + ' برگشت ✅');
    else if (e.t === 'autoplay') toast('بازی خودکار برای ' + e.name);
    else if (e.t === 'afk') toast(e.name + ' غایب شد — ربات موقتاً بازی می‌کند 💤');
    else if (e.t === 'back') toast(e.name + ' برگشت به بازی 👋');
    else if (e.t === 'timeout') toast('زمان ' + e.name + ' تمام شد');
    else if (e.t === 'emoji') showEmoji(e.seat, e.e);
    else if (e.t === 'kick') toast(e.name + ' حذف شد');
    else if (e.t === 'rejected' && e.card) toast('کارت ردشده: ' + cardText(e.card));
  }
}
function teamOfMe(m) {
  if (m.mySeat == null) return -1;
  return m.mode === 2 ? m.mySeat : m.mySeat % 2;
}
function cardText(c) { return RANK_FA[c.slice(1)] || c.slice(1); }

/* ---------------- Telegram MainButton ---------------- */
function syncMainButton() {
  if (!TG || !TG.MainButton) return;
  var m = S.snap;
  var mb = TG.MainButton;
  try {
    if (S.screen === 'lobby' && m && m.isHost) {
      mb.setParams({ text: 'شروع بازی', color: '#e9c46a', text_color: '#08301f', is_visible: true });
      mb.offClick(mbHandler); mbHandler = function () { send({ t: 'start' }); };
      mb.onClick(mbHandler);
      return;
    }
    if (m && m.phase === 'discard' && m.mySeat != null && m.turnSeat === m.mySeat) {
      var need = (m.draft && m.draft.discardCount) || 2;
      var ok = S.sel.length === need;
      mb.setParams({ text: ok ? 'انداختن ' + fa(need) + ' کارت' : 'کارت انتخاب کن (' + fa(S.sel.length) + '/' + fa(need) + ')',
        color: ok ? '#e9c46a' : '#4b6b5c', text_color: '#08301f', is_visible: true });
      mb.offClick(mbHandler); mbHandler = function () { doDiscard(); };
      mb.onClick(mbHandler);
      return;
    }
    if (m && m.phase === 'game_end' && m.isHost) {
      mb.setParams({ text: 'بازی جدید', color: '#e9c46a', text_color: '#08301f', is_visible: true });
      mb.offClick(mbHandler); mbHandler = function () { send({ t: 'restart' }); };
      mb.onClick(mbHandler);
      return;
    }
    mb.hide();
  } catch (e) {}
  try {
    if (TG.BackButton) { if (S.screen === 'home') TG.BackButton.hide(); else TG.BackButton.show(); }
  } catch (e) {}
}
var mbHandler = function () {};

function onBack() {
  if (S.screen === 'game' || S.screen === 'lobby') UI.leave();
  else UI.go('home');
}

/* ---------------- rendering: lobby ---------------- */
function renderLobby() {
  var m = S.snap;
  el('lobbyCode').textContent = m.code;
  el('lobbyMode').textContent = (m.mode === 2 ? 'حالت ۲ نفره (ویژه)' : 'حالت ۴ نفره تیمی') +
    ' • تا ' + fa(m.settings.targetPoints) + ' امتیاز';
  var box = el('lobbySeats');
  box.innerHTML = '';
  for (var i = 0; i < m.seats.length; i++) {
    var p = m.seats[i];
    var div = document.createElement('div');
    div.className = 'li';
    var teamLabel = m.mode === 4 ? ('<span class="chip" style="font-size:10px">تیم ' + fa((i % 2) + 1) + '</span>') : '';
    if (p) {
      div.innerHTML =
        '<div style="width:34px;height:34px;border-radius:50%;background:rgba(255,255,255,.14);display:grid;place-items:center;font-weight:800">' +
          (p.isBot ? '🤖' : esc((p.name || '?').slice(0, 1))) + '</div>' +
        '<div class="grow"><b style="font-size:14px">' + esc(p.name) + (p.uid === m.hostUid ? ' 👑' : '') + '</b>' +
        '<div class="mut" style="font-size:11px">' + (p.isBot ? 'ربات (' + lvlName(p.botLevel) + ')' : (p.online ? (p.afk ? 'غایب 💤' : 'آنلاین') : 'آفلاین')) + '</div></div>' +
        teamLabel;
      if (m.isHost && p.uid !== m.hostUid) {
        var b1 = document.createElement('button');
        b1.className = 'btn xs danger'; b1.textContent = 'حذف';
        b1.setAttribute('data-seat', i);
        b1.onclick = (function (seat) { return function () { send({ t: 'kick', seat: seat }); }; })(i);
        div.appendChild(b1);
      }
      if (m.isHost && !p.isBot && p.uid !== m.hostUid) {
        var b2 = document.createElement('button');
        b2.className = 'btn xs sec'; b2.textContent = '👑';
        b2.onclick = (function (seat) { return function () { send({ t: 'transfer_host', seat: seat }); }; })(i);
        div.appendChild(b2);
      }
    } else {
      div.innerHTML = '<div style="width:34px;height:34px;border-radius:50%;border:2px dashed rgba(255,255,255,.3)"></div>' +
        '<div class="grow"><b style="font-size:14px;opacity:.6">صندلی خالی</b>' +
        '<div class="mut" style="font-size:11px">صندلی ' + fa(i + 1) + '</div></div>' + teamLabel;
      var b3 = document.createElement('button');
      b3.className = 'btn xs sec'; b3.textContent = 'نشستن';
      b3.onclick = (function (seat) { return function () { send({ t: 'sit', seat: seat }); }; })(i);
      div.appendChild(b3);
      if (m.isHost) {
        var b4 = document.createElement('button');
        b4.className = 'btn xs'; b4.textContent = '🤖';
        b4.onclick = (function (seat) { return function () { send({ t: 'add_bot', seat: seat }); }; })(i);
        div.appendChild(b4);
      }
    }
    box.appendChild(div);
  }
  var humans = m.seats.filter(function (p) { return p && !p.isBot; }).length;
  var empty = m.seats.filter(function (p) { return !p; }).length;
  el('lobbyHint').textContent = 'بازیکن انسانی: ' + fa(humans) + ' • صندلی خالی: ' + fa(empty) +
    (empty && m.settings.autoFillBots ? ' (با شروع بازی، ربات پر می‌شود)' : '');

  el('hostBox').style.display = m.isHost ? 'flex' : 'none';
  if (m.isHost) {
    var hb = el('hostBtns');
    hb.innerHTML = '';
    addHostBtn(hb, '🤖 افزودن ربات', function () { send({ t: 'add_bot' }); });
    addHostBtn(hb, '🔁 جابجایی صندلی', function () { UI.openSwap(); });
    addHostBtn(hb, '⚙️ تنظیمات', function () { UI.openSettings(); });
  }
  var sp = (m.spectators || []).length;
  if (sp) el('lobbyHint').textContent += ' • تماشاچی: ' + fa(sp);
}
function addHostBtn(parent, label, fn) {
  var b = document.createElement('button');
  b.className = 'btn sec sm'; b.textContent = label; b.onclick = fn;
  parent.appendChild(b);
}
function lvlName(l) {
  return ({ easy: 'ساده', normal: 'معمولی', hard: 'حرفه‌ای', ai: 'هوش مصنوعی' })[l] || 'معمولی';
}

/* ---------------- rendering: game table ---------------- */
function cardHTML(code, cls) {
  if (code === 'XX') return '<div class="card back ' + (cls || '') + '"></div>';
  var s = code[0], r = code.slice(1);
  var red = (s === 'H' || s === 'D');
  var rr = RANK_FA[r] || r;
  return '<div class="card ' + (red ? 'red ' : '') + (cls || '') + '" data-card="' + code + '">' +
    '<div class="big">' + SUIT_CH[s] + '</div>' +
    '<div class="r">' + rr + '<div style="font-size:.8em">' + SUIT_CH[s] + '</div></div>' +
    '<div class="s">' + SUIT_CH[s] + '</div></div>';
}

/* Seat layout: my seat is always at the bottom; others rotate around. */
function seatPositions(mode, mySeat) {
  if (mode === 2) return [{ x: 50, y: 88 }, { x: 50, y: 12 }];
  return [{ x: 50, y: 90 }, { x: 12, y: 50 }, { x: 50, y: 10 }, { x: 88, y: 50 }];
}
function relIndex(m, seat) {
  var n = m.seats.length;
  var base = m.mySeat != null ? m.mySeat : 0;
  return ((seat - base) + n) % n;
}

function renderGame() {
  var m = S.snap;
  el('pillT0').textContent = (m.mode === 2 ? '🔵 ' : '🔵 تیم ۱: ') + fa(m.scores[0]);
  el('pillT1').textContent = (m.mode === 2 ? '🔴 ' : '🔴 تیم ۲: ') + fa(m.scores[1]);
  el('pillTricks').textContent = 'دست‌ها ' + fa(m.tricksWon[0]) + '-' + fa(m.tricksWon[1]);
  var tb = el('trumpBadge');
  if (m.trump) {
    tb.style.display = 'flex';
    tb.innerHTML = 'حکم ' + SUIT_CH[m.trump] + ' ' + SUIT_NAME[m.trump];
    tb.style.color = (m.trump === 'H' || m.trump === 'D') ? '#b91c1c' : '#08301f';
  } else tb.style.display = 'none';

  /* seats */
  var felt = el('felt');
  Array.prototype.slice.call(felt.querySelectorAll('.seat')).forEach(function (n) { n.remove(); });
  var pos = seatPositions(m.mode, m.mySeat);
  for (var i = 0; i < m.seats.length; i++) {
    var p = m.seats[i];
    var r = relIndex(m, i);
    var pt = pos[r] || pos[0];
    var d = document.createElement('div');
    d.className = 'seat' + (m.turnSeat === i ? ' turn' : '') + (p && !p.online && !p.isBot ? ' off' : '');
    d.style.left = pt.x + '%';
    d.style.top = pt.y + '%';
    d.setAttribute('data-seat', i);
    var av = p
      ? (p.photo ? '<img src="' + esc(p.photo) + '" alt="">' : (p.isBot ? '🤖' : esc((p.name || '?').slice(0, 1))))
      : '+';
    var team = m.mode === 4 ? '<div class="team t' + (i % 2) + '"></div>' : '<div class="team t' + i + '"></div>';
    d.innerHTML =
      '<div class="av">' + av + team +
        (p && p.uid === m.hostUid ? '<div class="crown">👑</div>' : '') +
        '<div class="cardsn">' + fa(p ? p.cards : 0) + '</div>' +
      '</div>' +
      '<div class="nm">' + esc(p ? p.name : 'خالی') + '</div>' +
      '<div class="meta">' + (m.hakemSeat === i ? '<span class="hakemtag">حاکم</span>' : '') +
        (p && !p.online && !p.isBot ? '<span>📴</span>' : '') +
        (p && p.online && p.afk && !p.isBot ? '<span title="غایب">💤</span>' : '') + '</div>';
    if (m.mySeat == null && !p) {
      d.style.cursor = 'pointer';
      d.onclick = (function (seat) { return function () { send({ t: 'sit', seat: seat }); }; })(i);
    }
    felt.appendChild(d);
  }

  /* trick cards */
  var ta = el('tarea');
  ta.innerHTML = '';
  var radius = 0.30;
  for (var j = 0; j < (m.trick || []).length; j++) {
    var tc = m.trick[j];
    var rr = relIndex(m, tc.seat);
    var ang = (m.mode === 2)
      ? (rr === 0 ? 90 : 270)
      : [90, 180, 270, 0][rr];
    var rad = ang * Math.PI / 180;
    var wrap = document.createElement('div');
    wrap.className = 'tcard';
    var dx = Math.cos(rad) * 44, dy = Math.sin(rad) * 44;
    wrap.style.transform = 'translate(calc(-50% + ' + (-dx) + 'px), calc(-50% + ' + dy + 'px)) rotate(' + ((rr * 7) - 10) + 'deg)';
    wrap.innerHTML = cardHTML(tc.card, m.lastTrick && 0 ? 'hl' : '');
    ta.appendChild(wrap);
  }
  if (!(m.trick || []).length && m.lastTrick && m.phase === 'playing') {
    var lab = document.createElement('div');
    lab.style.cssText = 'position:absolute;left:50%;top:50%;transform:translate(-50%,-50%);text-align:center;font-size:12px;opacity:.65;font-weight:700';
    var wn = m.seats[m.lastTrick.winner];
    lab.innerHTML = 'دست قبل: ' + esc(wn ? wn.name : '') + ' 🏅';
    ta.appendChild(lab);
  }

  renderBanner();
  renderHand();
  renderActbar();
  startTimer();
}

function renderBanner() {
  var m = S.snap;
  var b = el('banner');
  b.innerHTML = '';
  var mine = m.mySeat != null;

  if (m.phase === 'paused') {
    b.innerHTML = '<div class="banner"><div class="h2">⏸️ بازی متوقف شد</div>' +
      '<div class="mut">' + esc(m.pausedBy || '') + ' بازی را متوقف کرد</div>' +
      (m.isHost ? '<button class="btn" style="margin-top:10px" onclick="Net.send({t:&#39;resume&#39;})">ادامه بازی</button>' : '') + '</div>';
    return;
  }
  if (m.phase === 'deal_hakem' && m.reveal) {
    var cs = m.reveal.cards || [];
    var html = '<div class="banner"><div class="h2">تعیین حاکم 🎴</div><div class="mut">تا آمدن آس ورق می‌چینیم…</div>' +
      '<div style="display:flex;gap:4px;flex-wrap:wrap;justify-content:center;margin-top:10px">';
    for (var i = 0; i < cs.length; i++) {
      html += '<div style="--card-w:32px">' + cardHTML(cs[i].card, '') + '</div>';
    }
    html += '</div>';
    if (m.reveal.hakem != null && m.seats[m.reveal.hakem]) {
      html += '<div style="margin-top:10px;font-weight:800">حاکم: ' + esc(m.seats[m.reveal.hakem].name) + ' 👑</div>';
    }
    b.innerHTML = html + '</div>';
    return;
  }
  if (m.phase === 'trump') {
    if (mine && m.mySeat === m.hakemSeat) {
      var sp = '';
      ['S', 'H', 'D', 'C'].forEach(function (s) {
        sp += '<button class="' + ((s === 'H' || s === 'D') ? 'red' : '') + '" onclick="Net.trump(&#39;' + s + '&#39;)">' +
          SUIT_CH[s] + '<div style="font-size:11px;font-weight:800;margin-top:3px">' + SUIT_NAME[s] + '</div></button>';
      });
      b.innerHTML = '<div class="banner"><div class="h2">👑 تو حاکمی — حکم را انتخاب کن</div>' +
        '<div class="mut">۵ کارت اولت را ببین و خال حکم را تعیین کن</div>' +
        '<div class="suitpick">' + sp + '</div></div>';
    } else {
      var hk = m.seats[m.hakemSeat];
      b.innerHTML = '<div class="banner"><div class="spin"></div><div class="h2" style="margin-top:10px">در انتظار حکم</div>' +
        '<div class="mut">' + esc(hk ? hk.name : '') + ' دارد حکم را انتخاب می‌کند…</div></div>';
    }
    return;
  }
  if (m.phase === 'draw' && m.draft) {
    var d = m.draft;
    var isMe = m.mySeat === d.drawSeat;
    if (isMe) {
      if (!d.pending) {
        b.innerHTML = '<div class="banner"><div class="h2">🃏 نوبت برداشتن کارت</div>' +
          '<div class="mut">' + fa(d.drawsLeft[m.mySeat] || 0) + ' برداشت باقی مانده — کارت رو بردار</div>' +
          '<button class="btn" style="margin-top:12px" onclick="Net.send({t:&#39;draw_take&#39;})">برداشتن کارت</button></div>';
      } else {
        b.innerHTML = '<div class="banner"><div class="h2">' + (d.forced ? 'این کارت اجباری است' : 'کارت را نگه می‌داری؟') + '</div>' +
          '<div style="display:flex;justify-content:center;margin:10px 0">' + cardHTML(d.pending, '') + '</div>' +
          (d.forced
            ? '<div class="mut">کارت قبلی را رد کردی، پس این کارت هرچه باشد باید برداری</div>' +
              '<button class="btn" style="margin-top:10px" onclick="Net.send({t:&#39;draw_decide&#39;,keep:true})">قبول</button>'
            : '<div class="row" style="margin-top:6px"><button class="btn grow" onclick="Net.send({t:&#39;draw_decide&#39;,keep:true})">نگه می‌دارم</button>' +
              '<button class="btn sec grow" onclick="Net.send({t:&#39;draw_decide&#39;,keep:false})">دور می‌اندازم</button></div>' +
              '<div class="mut" style="margin-top:6px">اگر رد کنی، کارت بعدی هرچه بود اجباری است</div>') +
          '</div>';
      }
    } else {
      var dp = m.seats[d.drawSeat];
      b.innerHTML = '<div class="banner"><div class="spin"></div><div class="h2" style="margin-top:10px">در انتظار حریف</div>' +
        '<div class="mut">' + esc(dp ? dp.name : '') + ' دارد کارت برمی‌دارد…</div>' +
        (d.rejectedPublic && d.rejectedPublic.length
          ? '<div class="mut" style="margin-top:8px">کارت‌های ردشده:</div><div class="rej" style="justify-content:center">' +
            d.rejectedPublic.map(function (x) { return cardHTML(x.card, ''); }).join('') + '</div>'
          : '') + '</div>';
    }
    return;
  }
  if (m.phase === 'round_end' && m.roundSummary) {
    var rs = m.roundSummary;
    var win = rs.winnerTeam === teamOfMe(m);
    b.innerHTML = '<div class="banner"><div style="font-size:34px">' + (win ? '🎉' : '😕') + '</div>' +
      '<div class="h2">' + (rs.kot ? (rs.kotHakem ? 'کت حاکم!' : 'کت!') : 'پایان دست ' + fa(rs.roundNo)) + '</div>' +
      '<div class="mut">' + (m.mode === 2 ? 'برنده: بازیکن ' + fa(rs.winnerTeam + 1) : 'برنده: تیم ' + fa(rs.winnerTeam + 1)) +
      ' • ' + fa(rs.points) + ' امتیاز</div>' +
      '<div class="scoreboard" style="margin-top:10px"><div class="sb t0"><b>' + fa(rs.scores[0]) + '</b>' +
      (m.mode === 2 ? 'تو/حریف ۱' : 'تیم ۱') + '</div><div class="sb t1"><b>' + fa(rs.scores[1]) + '</b>' +
      (m.mode === 2 ? 'بازیکن ۲' : 'تیم ۲') + '</div></div>' +
      '<div class="mut" style="margin-top:8px">دست بعدی به‌زودی…</div>' +
      (m.isHost ? '<button class="btn" style="margin-top:8px" onclick="Net.send({t:&#39;next_round&#39;})">دست بعدی</button>' : '') +
      '</div>';
    return;
  }
  if (m.phase === 'game_end' && m.gameSummary) {
    var gs = m.gameSummary;
    var iWon = gs.winnerTeam === teamOfMe(m);
    b.innerHTML = '<div class="banner"><div style="font-size:44px">' + (iWon ? '🏆' : '🥀') + '</div>' +
      '<div class="h1">' + (iWon ? 'بردی!' : 'باختی') + '</div>' +
      '<div class="mut">نتیجه: ' + fa(gs.scores[0]) + ' - ' + fa(gs.scores[1]) + ' در ' + fa(gs.rounds) + ' دست</div>' +
      (m.isHost
        ? '<button class="btn" style="margin-top:12px" onclick="Net.send({t:&#39;restart&#39;})">بازی جدید</button>' +
          '<button class="btn sec" style="margin-top:8px" onclick="Net.send({t:&#39;back_to_lobby&#39;})">بازگشت به اتاق</button>'
        : '<div class="mut" style="margin-top:8px">منتظر تصمیم میزبان…</div>') +
      '<button class="btn sec" style="margin-top:8px" onclick="UI.leave()">خروج</button></div>';
    return;
  }
}

function renderHand() {
  var m = S.snap;
  var h = el('hand');
  h.innerHTML = '';
  if (m.mySeat == null) {
    h.innerHTML = '<div class="mut">تماشاچی هستی — با لمس صندلی خالی وارد بازی شو</div>';
    return;
  }
  var cards = m.hand || [];
  // Fit the fan inside the viewport: solve for the overlap that keeps
  // total width <= available width.  w + (n-1)*w*(1+ov) <= avail
  var cw = parseFloat(getComputedStyle(document.documentElement).getPropertyValue('--card-w')) ||
           Math.max(46, Math.min(64, window.innerWidth * 0.132));
  var avail = Math.max(200, window.innerWidth - 24);
  var n = cards.length;
  var ov = -0.36;
  if (n > 1) {
    var needed = (avail - cw) / ((n - 1) * cw) - 1;   // negative => overlap
    ov = Math.max(-0.82, Math.min(-0.20, needed));
  }
  h.style.setProperty('--overlap', ov);
  var canPlay = m.phase === 'playing' && m.turnSeat === m.mySeat;
  var picking = m.phase === 'discard' && m.turnSeat === m.mySeat;
  var legal = m.legal || [];
  for (var i = 0; i < cards.length; i++) {
    var c = cards[i];
    var cls = '';
    if (canPlay) cls += legal.indexOf(c) >= 0 ? ' pl' : ' dim';
    if (picking) cls += S.sel.indexOf(c) >= 0 ? ' sel pl' : ' pl';
    var wrap = document.createElement('div');
    wrap.innerHTML = cardHTML(c, cls);
    var node = wrap.firstChild;
    node.onclick = (function (card) {
      return function () {
        if (picking) {
          var need = (m.draft && m.draft.discardCount) || 2;
          var ix = S.sel.indexOf(card);
          if (ix >= 0) S.sel.splice(ix, 1);
          else { if (S.sel.length >= need) S.sel.shift(); S.sel.push(card); }
          haptic('sel');
          renderHand(); renderActbar(); syncMainButton();
          return;
        }
        if (!canPlay) { toast('نوبت تو نیست'); return; }
        if (legal.indexOf(card) < 0) { toast('باید از خال زمین بازی کنی', true); haptic('err'); return; }
        haptic('medium');
        send({ t: 'play', card: card });
      };
    })(c);
    h.appendChild(node);
  }
}

function renderActbar() {
  var m = S.snap;
  var a = el('actbar');
  a.innerHTML = '';
  if (m.phase === 'discard' && m.turnSeat === m.mySeat) {
    var need = (m.draft && m.draft.discardCount) || 2;
    var btn = document.createElement('button');
    btn.className = 'btn sm';
    btn.textContent = 'انداختن ' + fa(need) + ' کارت (' + fa(S.sel.length) + '/' + fa(need) + ')';
    btn.disabled = S.sel.length !== need;
    btn.onclick = doDiscard;
    a.appendChild(btn);
    var hint = document.createElement('div');
    hint.className = 'mut';
    hint.textContent = 'کارت‌هایی که می‌خواهی دور بیندازی را انتخاب کن';
    a.appendChild(hint);
    return;
  }
  if (m.phase === 'discard' && m.turnSeat !== m.mySeat) {
    var w = document.createElement('div');
    w.className = 'mut';
    var op = m.seats[m.turnSeat];
    w.textContent = 'در انتظار انداختن کارت توسط ' + (op ? op.name : '');
    a.appendChild(w);
    return;
  }
  if (m.phase === 'playing') {
    var info = document.createElement('div');
    info.className = 'chip';
    info.id = 'turnChip';
    var tp = m.seats[m.turnSeat];
    info.textContent = (m.turnSeat === m.mySeat) ? 'نوبت تو ⏳' : ('نوبت ' + (tp ? tp.name : ''));
    a.appendChild(info);
    ['👍','😂','🔥','😱','🤝'].forEach(function (e) {
      var b = document.createElement('button');
      b.className = 'btn xs sec'; b.textContent = e;
      b.onclick = function () { send({ t: 'emoji', e: e }); };
      a.appendChild(b);
    });
  }
}

function doDiscard() {
  var m = S.snap;
  var need = (m.draft && m.draft.discardCount) || 2;
  if (S.sel.length !== need) { toast('باید ' + fa(need) + ' کارت انتخاب کنی', true); return; }
  send({ t: 'discard', cards: S.sel.slice() });
  S.sel = [];
}

function showEmoji(seat, e) {
  var node = document.querySelector('.seat[data-seat="' + seat + '"]');
  if (!node) return;
  var d = document.createElement('div');
  d.className = 'emo'; d.textContent = e;
  node.appendChild(d);
  setTimeout(function () { d.remove(); }, 950);
}

/* turn countdown ring on the active seat */
function startTimer() {
  clearInterval(S.timer);
  S.timer = setInterval(function () {
    var m = S.snap;
    if (!m || m.turnSeat == null || !m.turnDeadline) return;
    var left = Math.max(0, m.turnDeadline - Date.now());
    var total = (m.turnSeconds || 30) * 1000;
    var frac = Math.max(0, Math.min(1, left / total));
    var chip = el('turnChip');
    if (chip && m.phase === 'playing') {
      var secs = Math.ceil(left / 1000);
      var tp = m.seats[m.turnSeat];
      chip.textContent = (m.turnSeat === m.mySeat ? 'نوبت تو' : 'نوبت ' + (tp ? tp.name : '')) + ' • ' + fa(secs) + 'ث';
      chip.style.borderColor = frac < 0.3 ? 'rgba(255,90,90,.8)' : 'rgba(255,255,255,.14)';
    }
  }, 500);
}

/* ---------------- UI namespace ---------------- */
var UI = {
  go: function (name) {
    if (S.screen === name) return;
    S.screen = name;
    ['Home', 'New', 'Join', 'Lobby', 'Game'].forEach(function (n) {
      var node = el('scr' + n);
      if (node) node.classList.toggle('on', n.toLowerCase() === name);
    });
    syncMainButton();
  },
  setMode: function (m) {
    S.mode = m;
    Array.prototype.slice.call(document.querySelectorAll('#modeSeg button')).forEach(function (b) {
      b.classList.toggle('on', +b.getAttribute('data-m') === m);
    });
    el('tp').value = m === 2 ? 5 : 7;
    el('rowReveal').style.display = m === 2 ? 'flex' : 'none';
    el('modeHint').innerHTML = m === 2
      ? 'قوانین ویژه: ۵ کارت، حاکم شانسی، اعلام حکم، هرکس ۲ کارت دور می‌اندازد، سپس نوبتی کارت برمی‌دارید (رد کردی؟ کارت بعدی اجباری است). برنده هر دست ۳ دست از ۵.'
      : 'حکم کلاسیک: تیمی ۲×۲، حاکم با آس مشخص می‌شود، ۱۳ کارت، هر تیم ۷ دست ببرد برنده دست است. کت = ۲ امتیاز، کت حاکم = ۳ امتیاز.';
  },
  setLvl: function (l) {
    S.lvl = l;
    Array.prototype.slice.call(document.querySelectorAll('#lvlSeg button')).forEach(function (b) {
      b.classList.toggle('on', b.getAttribute('data-l') === l);
    });
  },
  tg: function (node) { node.classList.toggle('on'); haptic('sel'); },
  on: function (id) { var n = el(id); return !!(n && n.classList.contains('on')); },

  copyCode: function () {
    var m = S.snap;
    var code = (m && m.code) || S.code || '';
    copy(code);
    toast('کد کپی شد: ' + code);
  },
  copyLink: function () { copy(inviteLink()); toast('لینک دعوت کپی شد'); },
  invite: function () {
    var link = inviteLink();
    var text = '🎴 بیا حکم بازی کنیم! کد اتاق: ' + ((S.snap && S.snap.code) || S.code);
    if (TG && TG.openTelegramLink) {
      TG.openTelegramLink('https://t.me/share/url?url=' + encodeURIComponent(link) + '&text=' + encodeURIComponent(text));
    } else if (navigator.share) {
      navigator.share({ title: 'حکم آنلاین', text: text, url: link }).catch(function () {});
    } else { copy(link); toast('لینک کپی شد'); }
    haptic('ok');
  },
  leave: function () {
    var done = function () {
      try { if (S.ws) { S.ws.onclose = null; S.ws.close(); } } catch (e) {}
      S.ws = null; S.code = null; S.snap = null; S.sel = [];
      clearInterval(S.timer); clearInterval(S.pingTimer);
      el('conn').classList.remove('on');
      UI.go('home');
    };
    if (S.snap && S.snap.phase !== 'lobby' && S.snap.phase !== 'game_end') {
      if (TG && TG.showConfirm) TG.showConfirm('از میز خارج می‌شوی؟ جایت را ربات می‌گیرد.', function (ok) { if (ok) done(); });
      else if (confirm('از میز خارج می‌شوی؟')) done();
    } else done();
  },

  closeSheet: function () { el('sheet').classList.remove('on'); },
  sheet: function (html) { el('sheetBody').innerHTML = html; el('sheet').classList.add('on'); },

  openMenu: function () {
    var m = S.snap || {};
    var h = '<div class="h2" style="margin-bottom:10px">منوی بازی</div><div class="col">';
    h += '<div class="scoreboard"><div class="sb t0"><b>' + fa(m.scores ? m.scores[0] : 0) + '</b>' +
      (m.mode === 2 ? 'بازیکن ۱' : 'تیم ۱') + '</div><div class="sb t1"><b>' + fa(m.scores ? m.scores[1] : 0) + '</b>' +
      (m.mode === 2 ? 'بازیکن ۲' : 'تیم ۲') + '</div></div>';
    h += '<div class="li"><div class="grow">کد اتاق</div><b style="direction:ltr;letter-spacing:2px">' + esc(m.code || '') + '</b></div>';
    h += '<button class="btn sec" onclick="UI.invite()">📤 دعوت دوستان</button>';
    h += '<button class="btn sec" onclick="UI.openChat()">💬 گفتگو</button>';
    h += '<button class="btn sec" onclick="UI.openLastTrick()">🃏 دست قبلی</button>';
    if (m.isHost) {
      h += '<div class="h2" style="margin-top:8px">کنترل میزبان</div>';
      h += '<button class="btn sec" onclick="UI.openSwap()">🔁 جابجایی صندلی بازیکنان</button>';
      h += '<button class="btn sec" onclick="UI.openSeatMgr()">👥 مدیریت بازیکنان / ربات</button>';
      h += '<button class="btn sec" onclick="UI.openSettings()">⚙️ تنظیمات میز</button>';
      if (m.phase === 'paused') h += '<button class="btn" onclick="Net.send({t:&#39;resume&#39;});UI.closeSheet()">▶️ ادامه بازی</button>';
      else h += '<button class="btn sec" onclick="Net.send({t:&#39;pause&#39;});UI.closeSheet()">⏸️ توقف بازی</button>';
      h += '<button class="btn sec" onclick="Net.send({t:&#39;restart&#39;});UI.closeSheet()">🔄 شروع مجدد بازی</button>';
      h += '<button class="btn sec" onclick="Net.send({t:&#39;back_to_lobby&#39;});UI.closeSheet()">🏠 بازگشت همه به اتاق انتظار</button>';
    }
    h += '<button class="btn sec" onclick="UI.openRules()">📖 قوانین</button>';
    h += '<button class="btn danger" onclick="UI.closeSheet();UI.leave()">خروج از میز</button>';
    h += '</div>';
    UI.sheet(h);
  },

  openSwap: function () {
    var m = S.snap;
    if (!m) return;
    var h = '<div class="h2">جابجایی صندلی</div><div class="mut" style="margin:6px 0 10px">' +
      'دو صندلی را انتخاب کن تا بازیکنانشان (همراه کارت‌هایشان) جابجا شوند.</div><div class="list">';
    for (var i = 0; i < m.seats.length; i++) {
      var p = m.seats[i];
      h += '<div class="li"><div class="grow"><b>صندلی ' + fa(i + 1) + '</b>' +
        (m.mode === 4 ? ' <span class="chip" style="font-size:10px">تیم ' + fa((i % 2) + 1) + '</span>' : '') +
        '<div class="mut" style="font-size:11px">' + esc(p ? p.name : 'خالی') + '</div></div>' +
        '<button class="btn xs sec" id="swp' + i + '" onclick="UI.pickSwap(' + i + ')">انتخاب</button></div>';
    }
    h += '</div><div class="mut" id="swapInfo" style="margin-top:8px"></div>' +
      '<button class="btn" style="margin-top:10px" onclick="UI.doSwap()">اعمال جابجایی</button>' +
      '<button class="btn sec" style="margin-top:8px" onclick="UI.closeSheet()">بستن</button>';
    UI.sheet(h);
    UI._swap = [];
  },
  pickSwap: function (i) {
    UI._swap = UI._swap || [];
    var ix = UI._swap.indexOf(i);
    if (ix >= 0) UI._swap.splice(ix, 1);
    else { if (UI._swap.length >= 2) UI._swap.shift(); UI._swap.push(i); }
    for (var k = 0; k < 4; k++) {
      var b = el('swp' + k);
      if (b) { b.className = 'btn xs ' + (UI._swap.indexOf(k) >= 0 ? '' : 'sec'); b.textContent = UI._swap.indexOf(k) >= 0 ? '✓' : 'انتخاب'; }
    }
    var inf = el('swapInfo');
    if (inf) inf.textContent = UI._swap.length === 2
      ? ('جابجایی صندلی ' + fa(UI._swap[0] + 1) + ' با ' + fa(UI._swap[1] + 1))
      : 'یک صندلی دیگر انتخاب کن';
    haptic('sel');
  },
  doSwap: function () {
    if (!UI._swap || UI._swap.length !== 2) { toast('دو صندلی انتخاب کن', true); return; }
    send({ t: 'swap', a: UI._swap[0], b: UI._swap[1], withCards: true });
    UI.closeSheet();
    toast('صندلی‌ها جابجا شد');
  },

  openSeatMgr: function () {
    var m = S.snap;
    var h = '<div class="h2">مدیریت بازیکنان</div><div class="mut" style="margin:6px 0 10px">' +
      'می‌توانی بازیکن را با ربات جایگزین کنی یا صندلی خالی را با ربات پر کنی. بازی هیچ‌وقت متوقف نمی‌شود.</div><div class="list">';
    for (var i = 0; i < m.seats.length; i++) {
      var p = m.seats[i];
      h += '<div class="li"><div class="grow"><b>' + esc(p ? p.name : 'صندلی خالی') + '</b>' +
        '<div class="mut" style="font-size:11px">صندلی ' + fa(i + 1) +
        (p ? (p.isBot ? ' • ربات ' + lvlName(p.botLevel) : (p.online ? ' • آنلاین' : ' • آفلاین')) : '') + '</div></div>';
      if (!p) h += '<button class="btn xs" onclick="Net.send({t:&#39;add_bot&#39;,seat:' + i + '});UI.closeSheet()">🤖 ربات</button>';
      else if (!p.isBot) h += '<button class="btn xs sec" onclick="Net.send({t:&#39;to_bot&#39;,seat:' + i + '});UI.closeSheet()">جایگزینی با ربات</button>';
      else h += '<button class="btn xs sec" onclick="Net.send({t:&#39;sit&#39;,seat:' + i + '});UI.closeSheet()">من می‌نشینم</button>';
      h += '</div>';
    }
    h += '</div><button class="btn sec" style="margin-top:10px" onclick="UI.closeSheet()">بستن</button>';
    UI.sheet(h);
  },

  openSettings: function () {
    var m = S.snap;
    var st = m.settings || {};
    var h = '<div class="h2">تنظیمات میز</div><div class="col" style="margin-top:10px">' +
      '<div class="row"><div class="grow"><div class="mut">امتیاز برد</div>' +
      '<input id="stTp" type="number" min="1" max="21" value="' + (st.targetPoints || 7) + '"></div>' +
      '<div class="grow"><div class="mut">زمان نوبت</div>' +
      '<input id="stTs" type="number" min="10" max="180" value="' + (st.turnSeconds || 30) + '"></div></div>' +
      '<div class="mut">سطح ربات</div><div class="seg" id="stLvl">' +
      ['easy', 'normal', 'hard', 'ai'].map(function (l) {
        return '<button class="' + (st.botLevel === l ? 'on' : '') + '" data-l="' + l + '" onclick="UI.pickLvl(this)">' + lvlName(l) + '</button>';
      }).join('') + '</div>' +
      '<div class="sw"><div><b style="font-size:14px">قانون کت</b></div>' +
      '<div class="toggle ' + (st.kotRule ? 'on' : '') + '" id="stKot" onclick="UI.tg(this)"></div></div>' +
      '<div class="sw"><div><b style="font-size:14px">استفاده از AI خارجی</b><div class="mut">' +
      (S.aiAvailable ? 'کلید فعال است' : 'کلیدی تنظیم نشده') + '</div></div>' +
      '<div class="toggle ' + (st.useLLM ? 'on' : '') + '" id="stLLM" onclick="UI.tg(this)"></div></div>' +
      '<div class="sw"><div><b style="font-size:14px">پر کردن خودکار با ربات</b></div>' +
      '<div class="toggle ' + (st.autoFillBots ? 'on' : '') + '" id="stFill" onclick="UI.tg(this)"></div></div>' +
      '<div class="sw"><div><b style="font-size:14px">میز خصوصی</b></div>' +
      '<div class="toggle ' + (st.isPrivate ? 'on' : '') + '" id="stPriv" onclick="UI.tg(this)"></div></div>' +
      (m.mode === 2 ? '<div class="sw"><div><b style="font-size:14px">نمایش کارت ردشده</b></div>' +
        '<div class="toggle ' + (st.revealRejected ? 'on' : '') + '" id="stRev" onclick="UI.tg(this)"></div></div>' : '') +
      '<button class="btn" onclick="UI.saveSettings()">ذخیره</button>' +
      '<button class="btn sec" onclick="UI.closeSheet()">بستن</button></div>';
    UI.sheet(h);
    UI._lvl = st.botLevel || 'normal';
  },
  pickLvl: function (node) {
    UI._lvl = node.getAttribute('data-l');
    Array.prototype.slice.call(document.querySelectorAll('#stLvl button')).forEach(function (b) {
      b.classList.toggle('on', b === node);
    });
    haptic('sel');
  },
  saveSettings: function () {
    var v = {
      targetPoints: +el('stTp').value,
      turnSeconds: +el('stTs').value,
      botLevel: UI._lvl || 'normal',
      kotRule: UI.on('stKot'),
      useLLM: UI.on('stLLM'),
      autoFillBots: UI.on('stFill'),
      isPrivate: UI.on('stPriv'),
    };
    if (el('stRev')) v.revealRejected = UI.on('stRev');
    send({ t: 'settings', v: v });
    UI.closeSheet();
    toast('تنظیمات ذخیره شد');
  },

  openChat: function () {
    var m = S.snap || {};
    var msgs = (m.chat || []).map(function (c) {
      return '<div class="msg' + (c.uid === (S.me && S.me.uid) ? ' me' : '') + '"><b>' + esc(c.name) + '</b>' + esc(c.text) + '</div>';
    }).join('');
    UI.sheet('<div class="h2">گفتگو</div><div class="chatlog" id="chatlog" style="margin:10px 0">' +
      (msgs || '<div class="mut">هنوز پیامی نیست</div>') + '</div>' +
      '<div class="row"><input id="chatIn" placeholder="پیامت را بنویس…" maxlength="200" ' +
      'onkeydown="if(event.key===&#39;Enter&#39;)UI.sendChat()"><button class="btn sm" onclick="UI.sendChat()">ارسال</button></div>' +
      '<div class="row" style="margin-top:8px;flex-wrap:wrap">' +
      ['سلام!','حکم چی شد؟','عجله نکن 😄','دستت درد نکنه','یکی بیاد جای من'].map(function (t) {
        return '<button class="btn xs sec" onclick="UI.quickChat(&#39;' + t + '&#39;)">' + t + '</button>';
      }).join('') + '</div>' +
      '<button class="btn sec" style="margin-top:10px" onclick="UI.closeSheet()">بستن</button>');
    var cl = el('chatlog'); if (cl) cl.scrollTop = cl.scrollHeight;
  },
  sendChat: function () {
    var i = el('chatIn');
    if (!i || !i.value.trim()) return;
    send({ t: 'chat', text: i.value.trim() });
    i.value = '';
    setTimeout(UI.openChat, 350);
  },
  quickChat: function (t) { send({ t: 'chat', text: t }); setTimeout(UI.openChat, 350); },

  openLastTrick: function () {
    var m = S.snap || {};
    if (!m.lastTrick) { toast('هنوز دستی بازی نشده'); return; }
    var w = m.seats[m.lastTrick.winner];
    UI.sheet('<div class="h2">دست قبلی</div>' +
      '<div style="display:flex;gap:6px;justify-content:center;margin:12px 0">' +
      m.lastTrick.cards.map(function (c) { return cardHTML(c.card, c.seat === m.lastTrick.winner ? 'hl' : ''); }).join('') +
      '</div><div class="center">برنده: <b>' + esc(w ? w.name : '') + '</b> 🏅</div>' +
      '<button class="btn sec" style="margin-top:12px" onclick="UI.closeSheet()">بستن</button>');
  },

  openRooms: function () {
    UI.sheet('<div class="h2">میزهای عمومی</div><div class="spin" style="margin:20px auto"></div>');
    apiFetch('/rooms').then(function (d) {
      var rooms = (d.rooms || []).filter(function (r) { return r.status === 'lobby'; });
      var h = '<div class="h2">میزهای عمومی</div><div class="list" style="margin-top:10px">';
      if (!rooms.length) h += '<div class="mut">میز عمومی فعالی نیست — خودت یکی بساز!</div>';
      rooms.forEach(function (r) {
        var n = (r.players || []).filter(function (p) { return p && !p.isBot; }).length;
        h += '<div class="li"><div class="grow"><b style="direction:ltr">' + esc(r.code) + '</b>' +
          '<div class="mut" style="font-size:11px">' + (r.mode === 2 ? '۲ نفره' : '۴ نفره') + ' • ' + fa(n) + ' بازیکن</div></div>' +
          '<button class="btn xs" onclick="UI.closeSheet();Net.enter(&#39;' + esc(r.code) + '&#39;)">ورود</button></div>';
      });
      h += '</div><button class="btn sec" style="margin-top:10px" onclick="UI.closeSheet()">بستن</button>';
      UI.sheet(h);
    });
  },

  openMe: function () {
    UI.sheet('<div class="h2">پروفایل</div><div class="spin" style="margin:20px auto"></div>');
    apiFetch('/me').then(function (d) {
      var st = d.stats || {};
      var h = '<div class="h2">' + esc((d.user && d.user.name) || 'من') + '</div>' +
        '<div class="row" style="margin:12px 0;gap:8px">' +
        statBox('بازی', st.games || 0) + statBox('برد', st.wins || 0) +
        statBox('کت', st.kots || 0) + statBox('رتبه', st.rating || 1000) + '</div>';
      h += '<div class="h2" style="margin-top:6px">آخرین بازی‌ها</div><div class="list" style="margin-top:8px">';
      var hist = d.history || [];
      if (!hist.length) h += '<div class="mut">تاریخچه‌ای نیست</div>';
      hist.forEach(function (g) {
        var won = String(g.winner) === String(g.team);
        h += '<div class="li"><div class="grow"><b>' + (g.mode === 2 ? '۲ نفره' : '۴ نفره') + '</b>' +
          '<div class="mut" style="font-size:11px">' + esc(g.code) + ' • ' + fa((g.scores || [0, 0]).join('-')) + '</div></div>' +
          '<span class="chip">' + (g.ended_at ? (won ? '🏆 برد' : 'باخت') : 'ناتمام') + '</span></div>';
      });
      h += '</div><button class="btn sec" style="margin-top:10px" onclick="UI.closeSheet()">بستن</button>';
      UI.sheet(h);
    });
  },

  openTop: function () {
    UI.sheet('<div class="h2">رتبه‌بندی</div><div class="spin" style="margin:20px auto"></div>');
    apiFetch('/leaderboard').then(function (d) {
      var h = '<div class="h2">🏆 بهترین بازیکنان</div><div class="list" style="margin-top:10px">';
      var top = d.top || [];
      if (!top.length) h += '<div class="mut">هنوز رتبه‌ای ثبت نشده</div>';
      top.forEach(function (u, i) {
        h += '<div class="lb"><div class="n">' + fa(i + 1) + '</div><div class="grow"><b>' + esc(u.name) + '</b>' +
          '<div class="mut" style="font-size:11px">' + fa(u.wins) + ' برد از ' + fa(u.games) + ' بازی</div></div>' +
          '<b>' + fa(u.rating) + '</b></div>';
      });
      h += '</div><button class="btn sec" style="margin-top:10px" onclick="UI.closeSheet()">بستن</button>';
      UI.sheet(h);
    });
  },

  openRules: function () {
    UI.sheet('<div class="h2">📖 قوانین</div>' +
      '<div class="mut" style="margin-top:10px;line-height:2">' +
      '<b style="color:#e9c46a">حکم ۴ نفره (کلاسیک)</b><br>' +
      '۱) چهار بازیکن، دو تیم روبه‌رو (۱ و ۳ / ۲ و ۴).<br>' +
      '۲) برای تعیین حاکم، ورق‌ها یکی‌یکی رو می‌شوند؛ اولین کسی که آس بگیرد حاکم است.<br>' +
      '۳) حاکم ۵ کارت اول را می‌بیند و خال حکم را اعلام می‌کند.<br>' +
      '۴) بقیه کارت‌ها ۴+۴ پخش می‌شود (هر نفر ۱۳ کارت).<br>' +
      '۵) حاکم اولین کارت را زمین می‌گذارد؛ هر کس باید از خال زمین بازی کند؛ نداشتی هر کارتی مجاز است.<br>' +
      '۶) بالاترین کارت خال حکم برنده است؛ اگر حکم نبود، بالاترین کارت خال زمین.<br>' +
      '۷) تیمی که اول ۷ دست ببرد برنده آن دست است (۱ امتیاز).<br>' +
      '۸) کت (۷–۰): ۲ امتیاز. کت حاکم (تیم حاکم هیچ دستی نبرد): ۳ امتیاز.<br>' +
      '۹) اگر تیم حاکم ببرد، حاکم ثابت می‌ماند؛ وگرنه حاکمی به تیم برنده منتقل می‌شود.<br><br>' +
      '<b style="color:#e9c46a">حکم ۲ نفره (قوانین ویژه)</b><br>' +
      '۱) حاکم به‌صورت شانسی انتخاب می‌شود.<br>' +
      '۲) به هر بازیکن ۵ کارت داده می‌شود.<br>' +
      '۳) حاکم حکم را اعلام می‌کند.<br>' +
      '۴) حاکم ۲ کارت دور می‌اندازد.<br>' +
      '۵) بازیکن مقابل هم ۲ کارت دور می‌اندازد.<br>' +
      '۶) حاکم یک کارت برمی‌دارد و می‌بیند: راضی بود نگه می‌دارد، راضی نبود دورش می‌اندازد ولی <b>کارت بعدی را حتماً باید بردارد</b>.<br>' +
      '۷) سپس همین روند برای بازیکن دوم اجرا می‌شود.<br>' +
      '۸) بعد از پخش کارت، بازی عادی با حکم اعلام‌شده ادامه پیدا می‌کند؛ هر کس اول ۳ دست ببرد برنده است.<br><br>' +
      '<b style="color:#e9c46a">نکات فنی</b><br>' +
      '• قطع اتصال؟ صندلی‌ات نگه داشته می‌شود و بعد از مهلت کوتاه، ربات موقتاً برایت بازی می‌کند. با برگشت، کنترل به خودت برمی‌گردد.<br>' +
      '• میزبان می‌تواند بازی را با تعداد کمتر از ۴ نفر (با ربات) شروع کند، صندلی‌ها را جابجا کند و بازیکن جایگزین بگذارد.' +
      '</div><button class="btn sec" style="margin-top:12px" onclick="UI.closeSheet()">بستن</button>');
  },
};
function statBox(label, val) {
  return '<div class="sb grow"><b>' + fa(val) + '</b><span class="mut">' + label + '</span></div>';
}
function copy(text) {
  try {
    if (navigator.clipboard) navigator.clipboard.writeText(text);
    else {
      var ta = document.createElement('textarea');
      ta.value = text; document.body.appendChild(ta); ta.select();
      document.execCommand('copy'); ta.remove();
    }
  } catch (e) {}
  haptic('sel');
}
function inviteLink() {
  var code = (S.snap && S.snap.code) || S.code || '';
  if (CFG.botUsername) {
    return CFG.miniAppName
      ? 'https://t.me/' + CFG.botUsername + '/' + CFG.miniAppName + '?startapp=' + code
      : 'https://t.me/' + CFG.botUsername + '?start=' + code;
  }
  return location.origin + '/?code=' + code;
}

/* ---------------- Net namespace ---------------- */
var Net = {
  send: send,
  trump: function (s) { haptic('medium'); send({ t: 'trump', suit: s }); },
  createRoom: function () {
    var body = {
      mode: S.mode,
      targetPoints: +el('tp').value,
      turnSeconds: +el('ts').value,
      botLevel: S.lvl,
      useLLM: S.lvl === 'ai',
      kotRule: UI.on('tgKot'),
      autoFillBots: UI.on('tgFill'),
      isPrivate: UI.on('tgPriv'),
      revealRejected: UI.on('tgRev'),
    };
    apiFetch('/rooms', { method: 'POST', body: body }).then(function (d) {
      if (!d.ok) { toast(d.error || 'ساخت میز ناموفق بود', true); return; }
      haptic('ok');
      connect(d.code);
    });
  },
  quick: function (mode) {
    apiFetch('/quick', { method: 'POST', body: { mode: mode, botLevel: S.lvl } }).then(function (d) {
      if (!d.ok) { toast('خطا در شروع بازی سریع', true); return; }
      connect(d.code);
      setTimeout(function () { send({ t: 'start' }); }, 900);
    });
  },
  join: function () {
    var code = (el('joinCode').value || '').toUpperCase();
    if (!/^[A-Z0-9]{4,8}$/.test(code)) { toast('کد نامعتبر است', true); return; }
    Net.enter(code);
  },
  enter: function (code) {
    apiFetch('/rooms/' + code).then(function (d) {
      if (!d.ok) { toast('اتاقی با این کد پیدا نشد', true); haptic('err'); return; }
      connect(code);
    });
  },
};

window.UI = UI;
window.Net = Net;

/* refresh on returning to foreground: force a resync */
document.addEventListener('visibilitychange', function () {
  if (!document.hidden && S.code) {
    if (!S.ws || S.ws.readyState !== 1) connect(S.code);
    else send({ t: 'sync' });
  }
});
window.addEventListener('online', function () { if (S.code && (!S.ws || S.ws.readyState !== 1)) connect(S.code); });

boot();
})();
</script>
</body>
</html>`;
}
