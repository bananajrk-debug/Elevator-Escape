'use strict';
const express = require('express');
const http = require('http');
const path = require('path');
const crypto = require('crypto');
const fs = require('fs');
const { Server } = require('socket.io');

const app = express();
const server = http.createServer(app);
const io = new Server(server);
app.use(express.static(path.join(__dirname, 'public')));

// ================= 定数 =================
const TEST = process.env.EG_TEST === '1';                 // 自動テスト用：時間を短縮（本番では未設定）
const N = 19, T = 80, MAP = N * T, MID = (N - 1) / 2;
const ELEVS = [                                           // 0=上 1=右 2=下 3=左
  { tx: MID, ty: 0, dx: 0, dy: 1 },
  { tx: N - 1, ty: MID, dx: -1, dy: 0 },
  { tx: MID, ty: N - 1, dx: 0, dy: -1 },
  { tx: 0, ty: MID, dx: 1, dy: 0 }
];
const CFG = { zoom: 1.9, lightR: { runner: 230, oni: 270 }, ghostR: { runner: 320, oni: 370 } };
const RUNNER_R = 18, ONI_R = 22;
const SPEED = { runner: 236, carrier: 214, oni: 230, cpu: 204, cpuAngry: 224 };
const RUSH_MUL = 1.5;                                     // エレベーター突入時の鬼の加速
const ELEV_OPEN_SEC = 20, CLOSE_PHASE = 8, DOOR_PASS = 0.15;
const BOARD_TIME = 4, BOARD_CATCH = 110;
const MAX_HP = 100, HIT_DMG = 50, HEAL = 50;
const INVULN = 3, START_STUN = 2, ONI_RESPAWN = 5;
const PLACE_MIN = 300, HINT_AFTER = 45;
const WARP_CD = 5, WARP_ACT_R = 38;
const BOOST_SEC = 10, BOOST_MUL = 1.4;
const GRENADE_STUN = 8, GRENADE_R = 240;
const CHEST_RESPAWN = 45, POTION_RESPAWN = 40, POTION_COUNT = 3;
const ONI_TP_CD = 30;
const KB_BLOCKS = 17, KB_SPEED = 1700;
const CROUCH_SEC = 2, CROUCH_CD = 10, CROUCH_MUL = 0.5;   // しゃがみ：2秒透明・CT10秒
const SKIN_COUNT = 8, MAX_PLAYERS = 8;
const COUNT_SEC = TEST ? 0.4 : 3.8;                       // 3, 2, 1, START!
const ROUND_GAP = TEST ? 1500 : 7000, MATCH_END_WAIT = 25000;
// マルチステージ／サドンデス（偶数階）
const SD_TIME_MUL = 0.5, SD_ONI_MUL = 1.2, SD_RESP = 3;
// ポイント・EG
const SKIN_PRICE = 50, FREE_SKINS = [0, 1, 2];
const PTS_LEAD = 100, EG_LEAD = 2, PTS_HIT = 30, PTS_ESCAPE = 100, PTS_ESCAPE_TEAM = 40, PTS_NODMG = 50, PTS_WIPE = 100, PTS_TIMEUP = 60;
const EG_FLOOR_WIN = 5, EG_MATCH_WIN = 10, EG_PARTICIPATE = 3, EG_CPU_WIN = 15;
const LEAD_MAX = 5, LEAD_START = 3, LEAD_INTERVAL = 10;   // シャー芯
const ITEMS = ['stun', 'boots'];                          // 宝箱：スタン／ブーツのみ
const ITEM_NAME = { stun: 'スタングレネード', boots: 'スピードブーツ' };
const CHATS = ['👍', '😂', '😱', '🙏', '🔥', '❤️', '👀', '💤', 'こっちに逃げて！', '鬼が来る！', '消しゴム発見！', '助けて！', 'ありがとう！', 'ナイス！', '待って！', '急げ！'];
const DEFAULT_RULES = { matchTime: 300, placeTime: 30, runnerSpeed: 100, oniSpeed: 100, floors: 3, items: true, potions: true, warps: true, crouch: true, leads: true };
function cleanRules(r) {
  r = r || {};
  const n = (v, lo, hi, st, d) => { v = Number(v); if (!isFinite(v)) return d; v = Math.round(v / st) * st; return Math.max(lo, Math.min(hi, v)); };
  return {
    matchTime: n(r.matchTime, TEST ? 5 : 120, 600, TEST ? 1 : 30, 300), placeTime: n(r.placeTime, 10, 60, 5, 30),
    runnerSpeed: n(r.runnerSpeed, 70, 150, 5, 100), oniSpeed: n(r.oniSpeed, 70, 150, 5, 100), floors: n(r.floors, 1, 9, 1, 3),
    items: r.items !== false, potions: r.potions !== false, warps: r.warps !== false, crouch: r.crouch !== false, leads: r.leads !== false
  };
}
// 実績（称号は実績達成で解放）
const ACH = {
  first_escape: { n: '初脱出', d: 'エレベーターで脱出する', eg: 5, t: '脱走者' },
  nodmg: { n: 'ノーダメージ脱出', d: 'ダメージを受けずに脱出する', eg: 15, t: '無傷の脱出王' },
  leads10: { n: 'シャー芯10本獲得', d: 'シャー芯を累計10本集める', eg: 15, t: 'シャー芯コレクター', need: 10, stat: 'leads' },
  cpuwin: { n: 'CPU戦で勝利', d: 'CPU戦を最上階までクリアする', eg: 10, t: 'CPUキラー' },
  wipe: { n: '鬼で全滅させる', d: '鬼として逃げ側を全員倒す', eg: 15, t: '鬼の王' },
  shopper: { n: '初めてのお買い物', d: 'ショップでスキンを購入する', eg: 5, t: 'おしゃれ番長' },
  multi: { n: 'フレンド戦を完走', d: '2人以上のマルチ戦を最後まで遊ぶ', eg: 10, t: '冒険者' }
};

const hidden = (e) => e.crouch > 0;                        // しゃがみ中：鬼から完全に見えない
const elevIndexAt = (tx, ty) => { for (let i = 0; i < 4; i++) if (ELEVS[i].tx === tx && ELEVS[i].ty === ty) return i; return -1; };
const elevCenter = (i) => ({ x: ELEVS[i].tx * T + T / 2, y: ELEVS[i].ty * T + T / 2 });
const elevFront = (i) => ({ x: (ELEVS[i].tx + ELEVS[i].dx) * T + T / 2, y: (ELEVS[i].ty + ELEVS[i].dy) * T + T / 2 });
function shuffle(a) { for (let i = a.length - 1; i > 0; i--) { const j = Math.floor(Math.random() * (i + 1)); [a[i], a[j]] = [a[j], a[i]]; } return a; }
const cleanSkin = (v) => { v = parseInt(v, 10); return v >= 0 && v < SKIN_COUNT ? v : 0; };

// ================= 迷路生成（行き止まりを減らし、必ず連結）=================
function generateMaze() {
  const g = [];
  for (let y = 0; y < N; y++) g.push(new Array(N).fill(1));
  const stack = [[1, 1]];
  g[1][1] = 0;
  const dirs = [[2, 0], [-2, 0], [0, 2], [0, -2]];
  while (stack.length) {
    const [cx, cy] = stack[stack.length - 1];
    const opts = dirs.filter(([dx, dy]) => {
      const nx = cx + dx, ny = cy + dy;
      return nx > 0 && ny > 0 && nx < N - 1 && ny < N - 1 && g[ny][nx] === 1;
    });
    if (!opts.length) { stack.pop(); continue; }
    const [dx, dy] = opts[Math.floor(Math.random() * opts.length)];
    g[cy + dy / 2][cx + dx / 2] = 0;
    g[cy + dy][cx + dx] = 0;
    stack.push([cx + dx, cy + dy]);
  }
  const cd4 = [[1, 0], [-1, 0], [0, 1], [0, -1]];
  const openCount = (cx, cy) => cd4.filter(([dx, dy]) => g[cy + dy][cx + dx] === 0).length;
  for (let cy = 1; cy < N; cy += 2) for (let cx = 1; cx < N; cx += 2) {
    if (openCount(cx, cy) !== 1 || Math.random() < 0.1) continue;
    const walls = cd4.filter(([dx, dy]) => {
      const nx = cx + dx * 2, ny = cy + dy * 2;
      return g[cy + dy][cx + dx] === 1 && nx > 0 && ny > 0 && nx < N - 1 && ny < N - 1;
    });
    if (!walls.length) continue;
    const good = walls.filter(([dx, dy]) => openCount(cx + dx * 2, cy + dy * 2) >= 2);
    const pool = good.length ? good : walls;
    const [dx, dy] = pool[Math.floor(Math.random() * pool.length)];
    g[cy + dy][cx + dx] = 0;
  }
  for (let k = 0; k < 10; k++) {
    const x = 1 + Math.floor(Math.random() * (N - 2));
    const y = 1 + Math.floor(Math.random() * (N - 2));
    if ((x + y) % 2 === 1) g[y][x] = 0;
  }
  for (const E of ELEVS) g[E.ty][E.tx] = 0;
  return g;
}

// ================= 衝突・経路 =================
function isSolid(g, tx, ty, ent) {
  if (tx < 0 || ty < 0 || tx >= N || ty >= N) return true;
  if (g.grid[ty][tx] === 1) return true;
  const i = elevIndexAt(tx, ty);
  if (i >= 0) return !(ent && ent.role === 'runner' && ent.side === i && (ent.board || (ent.hasEraser && g.elev.door > DOOR_PASS)));
  return false;
}
function collides(g, x, y, r, ent) {
  const x0 = Math.floor((x - r) / T), x1 = Math.floor((x + r) / T);
  const y0 = Math.floor((y - r) / T), y1 = Math.floor((y + r) / T);
  for (let ty = y0; ty <= y1; ty++) for (let tx = x0; tx <= x1; tx++) {
    if (!isSolid(g, tx, ty, ent)) continue;
    const cx = Math.max(tx * T, Math.min(x, tx * T + T));
    const cy = Math.max(ty * T, Math.min(y, ty * T + T));
    const dx = x - cx, dy = y - cy;
    if (dx * dx + dy * dy < r * r) return true;
  }
  return false;
}
function moveEnt(g, e, dx, dy) {
  const r = e.role === 'oni' ? ONI_R : RUNNER_R;
  if (dx !== 0 && !collides(g, e.x + dx, e.y, r, e)) e.x += dx;
  if (dy !== 0 && !collides(g, e.x, e.y + dy, r, e)) e.y += dy;
}
const bfsParent = new Int16Array(N * N), bfsQueue = new Int16Array(N * N);
function pathTiles(g, fx, fy, tx, ty, ent) {             // 開始〜目標までのタイル中心の並び（開始を含む）
  bfsParent.fill(-2);
  const start = fy * N + fx, goal = ty * N + tx;
  let head = 0, tail = 0;
  bfsQueue[tail++] = start; bfsParent[start] = -1;
  while (head < tail) {
    const cur = bfsQueue[head++];
    if (cur === goal) break;
    const cx = cur % N, cy = (cur / N) | 0;
    for (const [dx, dy] of [[1, 0], [-1, 0], [0, 1], [0, -1]]) {
      const nx = cx + dx, ny = cy + dy;
      if (isSolid(g, nx, ny, ent)) continue;
      const ni = ny * N + nx;
      if (bfsParent[ni] !== -2) continue;
      bfsParent[ni] = cur; bfsQueue[tail++] = ni;
    }
  }
  if (bfsParent[goal] === -2) return null;
  const out = [];
  for (let c = goal; c !== -1; c = bfsParent[c]) out.push({ x: (c % N) * T + T / 2, y: Math.floor(c / N) * T + T / 2 });
  return out.reverse();
}
function lineClear(g, x0, y0, x1, y1, r, ent) {
  const n = Math.ceil(Math.hypot(x1 - x0, y1 - y0) / 10);
  for (let i = 1; i <= n; i++) { const t = i / n; if (collides(g, x0 + (x1 - x0) * t, y0 + (y1 - y0) * t, r, ent)) return false; }
  return true;
}

// ================= アカウント・EG・実績・フレンド（申請/承認制）=================
// 保存先は DATA_DIR（既定 ./data）。Renderの無料プランは再起動でファイルが消えるため、永続ディスクを DATA_DIR に指定すること。
const DATA_DIR = process.env.DATA_DIR || path.join(__dirname, 'data');
const ACC_FILE = path.join(DATA_DIR, 'accounts.json');
const accounts = new Map(), byName = new Map(), byToken = new Map(), byDevice = new Map(), online = new Map(), sockAcc = new Map();
let saveTimer = null;
const sha = (v) => crypto.createHash('sha256').update(String(v)).digest('hex');
function normAcc(a) {
  a.friends = a.friends || []; a.reqIn = a.reqIn || []; a.reqOut = a.reqOut || []; a.devices = a.devices || [];
  a.eg = a.eg || 0; a.owned = a.owned || FREE_SKINS.slice(); a.ach = a.ach || []; a.title = a.title || null;
  a.stats = Object.assign({ leads: 0, escapes: 0, wipes: 0, cpuWins: 0, matches: 0, purchases: 0 }, a.stats);
  delete a.passHash; delete a.salt;                       // 旧フレンドパスワードは廃止
  return a;
}
function loadAccounts() {
  try {
    const j = JSON.parse(fs.readFileSync(ACC_FILE, 'utf8'));
    for (const a0 of j.accounts || []) {
      const a = normAcc(a0);
      accounts.set(a.id, a); byName.set(a.nameKey, a.id); byToken.set(a.tokenHash, a.id);
      for (const d of a.devices) byDevice.set(d, a.id);
    }
    console.log('accounts loaded:', accounts.size);
  } catch (e) { /* 初回は無し */ }
}
function saveAccounts() {
  if (saveTimer) return;
  saveTimer = setTimeout(() => {
    saveTimer = null;
    try {
      fs.mkdirSync(DATA_DIR, { recursive: true });
      fs.writeFileSync(ACC_FILE + '.tmp', JSON.stringify({ accounts: [...accounts.values()] }));
      fs.renameSync(ACC_FILE + '.tmp', ACC_FILE);
    } catch (e) { console.error('accounts save failed:', e.message); }
  }, TEST ? 50 : 400);
}
loadAccounts();
function cleanAccName(n) {
  n = String(n || '').trim();
  if (n.length < 2 || n.length > 12) return null;
  if (!/^[A-Za-z0-9_\-ぁ-んァ-ヶー一-龠]+$/.test(n)) return null;
  return n;
}
const cleanDevice = (d) => { d = String(d || ''); return /^[A-Za-z0-9\-]{8,64}$/.test(d) ? d : null; };
const accOf = (socketId) => sockAcc.get(socketId) || null;
const accName = (socketId) => { const a = accOf(socketId); return a ? a.name : null; };
const titleOf = (socketId) => { const a = accOf(socketId); return a && a.title && ACH[a.title] ? ACH[a.title].t : null; };
const walletOf = (a) => ({ eg: a.eg, owned: a.owned, ach: a.ach, title: a.title, stats: a.stats });
function socksOf(acc) { return online.get(acc.id) || new Set(); }
function emitWallet(acc) { for (const sid of socksOf(acc)) io.to(sid).emit('wallet', walletOf(acc)); }
function canUseSkin(socketId, skin) { const a = accOf(socketId); return a ? a.owned.includes(skin) : FREE_SKINS.includes(skin); }
function safeSkin(socketId, v) { const s = cleanSkin(v); return canUseSkin(socketId, s) ? s : 0; }
// EG付与（アカウントがあるときだけ保存される）
function payEG(socketId, n) { const a = accOf(socketId); if (!a || !n) return false; a.eg += n; saveAccounts(); emitWallet(a); return true; }
function grantAch(socketId, id) {
  const a = accOf(socketId);
  if (!a || !ACH[id] || a.ach.includes(id)) return false;
  a.ach.push(id); a.eg += ACH[id].eg; saveAccounts(); emitWallet(a);
  for (const sid of socksOf(a)) io.to(sid).emit('achieved', { id, n: ACH[id].n, eg: ACH[id].eg, t: ACH[id].t });
  return true;
}
function bumpStat(socketId, key, n) {
  const a = accOf(socketId);
  if (!a) return;
  a.stats[key] = (a.stats[key] || 0) + n; saveAccounts();
  for (const id in ACH) if (ACH[id].stat === key && a.stats[key] >= ACH[id].need) grantAch(socketId, id);
}
function friendEntries(acc) {
  const mk = (fid) => accounts.get(fid);
  const list = acc.friends.map(mk).filter(Boolean).map((f) => {
    const socks = online.get(f.id), isOn = !!(socks && socks.size);
    let room = null, state = null;
    if (isOn) for (const sid of socks) { const r = sockRoom.get(sid); if (r && !r.solo) { room = r.code; state = r.state; break; } }
    return { name: f.name, online: isOn, room, state, title: f.title && ACH[f.title] ? ACH[f.title].t : null };
  }).sort((a, b) => (b.online - a.online) || a.name.localeCompare(b.name));
  return { list, reqIn: acc.reqIn.map(mk).filter(Boolean).map((f) => f.name), reqOut: acc.reqOut.map(mk).filter(Boolean).map((f) => f.name) };
}
function pushFriends(acc) { const p = friendEntries(acc); for (const sid of socksOf(acc)) io.to(sid).emit('friends', p); }
function notifyPresence(acc) {
  if (!acc) return;
  pushFriends(acc);
  for (const fid of acc.friends) { const f = accounts.get(fid); if (f) pushFriends(f); }
}
function touchPresence(socketId) { const a = accOf(socketId); if (a) notifyPresence(a); }
function detach(socket, silent) {
  const a = sockAcc.get(socket.id);
  if (!a) return;
  sockAcc.delete(socket.id);
  const set = online.get(a.id);
  if (set) { set.delete(socket.id); if (!set.size) online.delete(a.id); }
  if (!silent) notifyPresence(a);
}
function attach(socket, acc) {
  detach(socket, true);
  sockAcc.set(socket.id, acc);
  if (!online.has(acc.id)) online.set(acc.id, new Set());
  online.get(acc.id).add(socket.id);
}
function sendProfile(socket) {
  const a = accOf(socket.id);
  socket.emit('profile', a ? { name: a.name, wallet: walletOf(a) } : { name: null, wallet: null });
  if (a) socket.emit('friends', friendEntries(a));
}
function bindDevice(acc, dev) {
  if (!dev || acc.devices.includes(dev)) return;
  acc.devices.push(dev); byDevice.set(dev, acc.id); saveAccounts();
}

// ================= ルーム管理 =================
const rooms = new Map();
const sockRoom = new Map();
function newCode() {
  for (let i = 0; i < 1000; i++) {
    const c = String(Math.floor(Math.random() * 100000)).padStart(5, '0');
    if (!rooms.has(c)) return c;
  }
  return null;
}
function cleanName(n) { return String(n || '').trim().slice(0, 12) || 'プレイヤー'; }
function sendLobby(room) {
  const players = [...room.players.values()].map((p) => ({ id: p.id, name: p.name, role: p.role, skin: p.skin, ready: p.id === room.host || !!p.ready, title: titleOf(p.id) }));
  for (const id of room.players.keys()) io.to(id).emit('lobby', { code: room.code, state: room.state, host: room.host, players, you: id, rules: room.rules });
}
function toLobby(room) {
  room.state = 'lobby'; room.game = null; room.match = null;
  for (const p of room.players.values()) p.ready = false;
  sendLobby(room);
  for (const id of room.players.keys()) touchPresence(id);
}
function makeRoom(socket, solo) {
  const code = newCode();
  if (!code) { socket.emit('errmsg', 'ルームを作れませんでした'); return null; }
  const room = { code, players: new Map(), host: socket.id, state: 'lobby', game: null, match: null, solo: !!solo, rules: { ...DEFAULT_RULES } };
  rooms.set(code, room);
  return room;
}
function addPlayer(room, socket, name, role, skin) {
  room.players.set(socket.id, { id: socket.id, name: cleanName(name), role, skin: safeSkin(socket.id, skin), ready: false });
  sockRoom.set(socket.id, room);
  touchPresence(socket.id);
}
function leaveRoom(id) { try { leaveRoomInner(id); } finally { touchPresence(id); } }
function leaveRoomInner(id) {
  const room = sockRoom.get(id);
  if (!room) return;
  sockRoom.delete(id);
  room.players.delete(id);
  if (room.match && room.match.scores[id]) room.match.scores[id].left = true;
  const g = room.game;
  if (g) {
    const ent = g.ents.find((e) => e.id === id);
    if (ent) {
      if (g.board && g.board.id === id) g.board = null;
      if (ent.hasEraser) dropEraser(g, ent);
      g.ents = g.ents.filter((e) => e !== ent);
      if (!g.ents.some((e) => e.role === 'oni')) addEnt(g, 'cpu' + Date.now(), 'CPU鬼', 'oni', true, Math.floor(Math.random() * 4), 0);
    }
  }
  if (room.players.size === 0) { rooms.delete(room.code); return; }
  if (room.host === id) room.host = room.players.keys().next().value;
  sendLobby(room);
}

// ================= マッチ（階層）=================
function addEnt(g, id, name, role, cpu, side, skin, title) {
  const E = ELEVS[side];
  const k = g.ents.filter((e) => e.side === side).length;
  const off = [0, 16, -16][k % 3];
  const px = E.dy !== 0 ? 1 : 0, py = E.dx !== 0 ? 1 : 0;
  const x = (E.tx + E.dx) * T + T / 2 + px * off, y = (E.ty + E.dy) * T + T / 2 + py * off;
  g.ents.push({
    id, name, role, cpu, side, skin: skin || 0, title: title || null, x, y, spawn: { x, y },
    input: { u: 0, d: 0, l: 0, r: 0 }, alive: true, hp: MAX_HP, hasEraser: false, board: false,
    invuln: 0, stun: 0, resp: false, tpCd: ONI_TP_CD, item: null, boost: 0, wcd: 0, msgCd: 0, crouch: 0, crouchCd: 0, kb: null,
    wp: null, wpT: 0, idle: 0, vx: 0, vy: 0, path: null, repath: 0, pts: 0, dmg: 0, leads: 0
  });
}
function assignRound1(list) {
  const target = list.length >= 2 ? Math.max(1, Math.floor(list.length / 3)) : 0;
  let oniCount = list.filter((p) => p.role === 'oni').length;
  for (const p of list) p.assigned = p.role;
  for (const p of shuffle(list.filter((p) => p.role === 'auto'))) {
    if (oniCount < target) { p.assigned = 'oni'; oniCount++; } else p.assigned = 'runner';
  }
  if (!list.some((p) => p.assigned === 'runner')) shuffle(list.filter((p) => p.assigned === 'oni'))[0].assigned = 'runner';
}
function rolesFor(room, floor) {                           // 階ごとにロールチェンジ（順番に鬼を交代）
  const m = room.match, ids = m.order.filter((id) => room.players.has(id)), n = ids.length, roles = new Map();
  if (floor === 1) { for (const id of ids) roles.set(id, room.players.get(id).assigned); return roles; }
  if (n <= 1) { for (const id of ids) roles.set(id, 'runner'); return roles; }
  const k = Math.max(1, Math.min(m.k, n - 1)), oniSet = new Set();
  for (let i = 0; i < k; i++) oniSet.add(ids[((floor - 1) * k + i) % n]);
  for (const id of ids) roles.set(id, oniSet.has(id) ? 'oni' : 'runner');
  return roles;
}
function startMatch(room) {
  const list = [...room.players.values()];
  assignRound1(list);
  const rules = cleanRules(room.rules);
  const onis = list.filter((p) => p.assigned === 'oni'), runners = list.filter((p) => p.assigned === 'runner'), n = list.length;
  room.match = {
    floor: 0, total: room.solo ? (room.soloFloors || 3) : rules.floors, order: onis.concat(runners).map((p) => p.id),
    k: n >= 2 ? Math.max(1, Math.min(onis.length || 1, n - 1)) : 0, scores: {}, done: false, solo: room.solo, humans: n
  };
  for (const p of list) room.match.scores[p.id] = { name: p.name, pts: 0, eg: 0, left: false };
  startRound(room, 1);
}
function startRound(room, floor) {
  const m = room.match, rules = cleanRules(room.rules);
  const sudden = floor % 2 === 0;                          // 偶数階はサドンデス
  const ang = Math.random() * Math.PI * 2, mag = 40 + Math.random() * 80;
  const g = {
    room, rules, floor, total: m.total, sudden, grid: generateMaze(), status: 'playing',
    phase: (floor === 1 && !room.solo) ? 'place' : 'count', countLeft: (floor === 1 && !room.solo) ? 0 : COUNT_SEC,
    placeLeft: rules.placeTime, time: sudden ? Math.max(TEST ? 3 : 60, Math.round(rules.matchTime * SD_TIME_MUL)) : rules.matchTime,
    oniMul: rules.oniSpeed / 100 * (sudden ? SD_ONI_MUL : 1), respSec: sudden ? SD_RESP : ONI_RESPAWN,
    playT: 0, endAt: 0, finished: false, pingClock: 0, ents: [], board: null, slide: 0, escaper: null, leads: [], leadT: LEAD_INTERVAL,
    hintOff: { x: Math.cos(ang) * mag, y: Math.sin(ang) * mag },
    eraser: { x: 0, y: 0, home: { x: 0, y: 0 }, placed: false, carried: false, cool: 0 },
    elev: { open: false, left: 0, door: 0 }
  };
  setupSpots(g);
  if (rules.leads) for (let i = 0; i < LEAD_START; i++) spawnLead(g);
  const roles = rolesFor(room, floor), sides = shuffle([0, 1, 2, 3]);
  let si = 0;
  const ids = [...roles.keys()];
  for (const id of ids) if (roles.get(id) === 'runner') { const p = room.players.get(id); addEnt(g, id, p.name, 'runner', false, sides[si++ % 4], p.skin, titleOf(id)); }
  for (const id of ids) if (roles.get(id) === 'oni') { const p = room.players.get(id); addEnt(g, id, p.name, 'oni', false, sides[si++ % 4], p.skin, titleOf(id)); }
  if (!g.ents.some((e) => e.role === 'oni')) addEnt(g, 'cpu1', 'CPU鬼', 'oni', true, sides[si++ % 4], 0, null);
  m.floor = floor;
  room.game = g; room.state = 'playing';
  for (const e of g.ents) if (!e.cpu) {
    io.to(e.id).emit('init', {
      grid: g.grid.map((r) => r.join('')), T, N, map: MAP, elevs: ELEVS, cfg: CFG, role: e.role, side: e.side, name: e.name,
      skin: e.skin, title: e.title, matchTime: g.time, placeTime: rules.placeTime, rules, warpCd: WARP_CD, tpCd: ONI_TP_CD, boardTime: BOARD_TIME,
      solo: room.solo, floor, total: m.total, sudden, count: g.countLeft,
      pads: g.pads, chests: g.chests.map((c) => ({ x: c.x, y: c.y })), potions: g.potions.map((p) => ({ x: p.x, y: p.y }))
    });
  }
  sendLobby(room);
  for (const id of room.players.keys()) touchPresence(id);
}
function beginCountdown(room) {                            // フレンド戦：ロビー中央で 3,2,1,START!
  room.state = 'starting';
  sendLobby(room);
  const seq = [3, 2, 1, 0]; let i = 0;
  const tick = () => {
    if (!rooms.has(room.code) || room.state !== 'starting') return;
    for (const id of room.players.keys()) io.to(id).emit('lobbyCount', { n: seq[i] });
    i++;
    if (i < seq.length) setTimeout(tick, TEST ? 80 : 1000);
    else setTimeout(() => { if (rooms.has(room.code) && room.state === 'starting') startMatch(room); }, TEST ? 80 : 800);
  };
  tick();
}

// ================= 配置（ワープ・宝箱・回復薬・シャー芯）=================
function pickSpots(n, minBetween, taken) {
  const cells = [];
  for (let ty = 1; ty < N; ty += 2) for (let tx = 1; tx < N; tx += 2) {
    const x = tx * T + T / 2, y = ty * T + T / 2;
    let ok = true;
    for (let i = 0; i < 4; i++) { const c = elevCenter(i); if (Math.hypot(x - c.x, y - c.y) < 300) ok = false; }
    if (ok) cells.push({ x, y });
  }
  shuffle(cells);
  const out = [];
  for (const c of cells) {
    if (out.length >= n) break;
    if (taken.concat(out).every((p) => Math.hypot(p.x - c.x, p.y - c.y) >= minBetween)) out.push(c);
  }
  return out;
}
function setupSpots(g) {
  const R = g.rules;
  let sp = [];
  for (const mb of [450, 350, 250, 0]) { sp = pickSpots(4, mb, []); if (sp.length === 4) break; }
  const d = (a, b) => Math.hypot(sp[a].x - sp[b].x, sp[a].y - sp[b].y);
  const opts = [[0, 1, 2, 3], [0, 2, 1, 3], [0, 3, 1, 2]];
  opts.sort((p, q) => Math.min(d(q[0], q[1]), d(q[2], q[3])) - Math.min(d(p[0], p[1]), d(p[2], p[3])));
  g.pads = R.warps ? opts[0].map((i, k) => ({ x: sp[i].x, y: sp[i].y, pair: k >> 1 })) : [];
  g.chests = R.items ? pickSpots(2, 400, g.pads).map((c) => ({ x: c.x, y: c.y, open: false, respawn: 0 })) : [];
  g.potions = (R.potions && !g.sudden) ? pickSpots(POTION_COUNT, 300, g.pads.concat(g.chests)).map((c) => ({ x: c.x, y: c.y, taken: false, respawn: 0 })) : [];
}
function spawnLead(g) {                                    // シャー芯：通路のランダムな位置に出現
  if (g.leads.length >= LEAD_MAX) return;
  const taken = g.pads.concat(g.chests, g.potions, g.leads);
  const c = pickSpots(1, 160, taken)[0];
  if (c) g.leads.push({ x: c.x, y: c.y });
}

// ================= ゲームロジック =================
function ev(g, msg) { for (const e of g.ents) if (!e.cpu) io.to(e.id).emit('ev', msg); }
function evTo(id, msg) { io.to(id).emit('ev', msg); }
function fxNear(g, type, x, y) {
  for (const e of g.ents) if (!e.cpu && Math.hypot(e.x - x, e.y - y) < 420) io.to(e.id).emit('fx', { t: type, x, y });
}
function validSpot(g, x, y) {
  const tx = Math.floor(x / T), ty = Math.floor(y / T);
  if (tx < 0 || ty < 0 || tx >= N || ty >= N || g.grid[ty][tx] === 1 || elevIndexAt(tx, ty) >= 0) return false;
  for (let i = 0; i < 4; i++) { const c = elevCenter(i); if (Math.hypot(x - c.x, y - c.y) < PLACE_MIN) return false; }
  for (const p of g.pads.concat(g.chests, g.potions, g.leads)) if (Math.hypot(x - p.x, y - p.y) < 70) return false;
  return !collides(g, x, y, 10, { role: 'oni', side: -1 });
}
function randomSpot(g) {
  const cands = [];
  for (let ty = 0; ty < N; ty++) for (let tx = 0; tx < N; tx++) {
    const x = tx * T + T / 2, y = ty * T + T / 2;
    if (g.grid[ty][tx] === 0 && validSpot(g, x, y)) cands.push({ x, y });
  }
  return cands[Math.floor(Math.random() * cands.length)] || { x: MAP / 2, y: MAP / 2 };
}
function placeEraser(g, x, y) {
  const er = g.eraser;
  er.x = x; er.y = y; er.home = { x, y }; er.placed = true; er.carried = false; er.cool = 0;
  g.placeLeft = 1.5;
  ev(g, '📍 消しゴムが迷路のどこかに設置された…');
}
function dropEraser(g, holder) {
  holder.hasEraser = false;
  g.eraser.carried = false; g.eraser.x = holder.x; g.eraser.y = holder.y; g.eraser.cool = 2.5;
}
function resetEraser(g, msg) {
  const er = g.eraser;
  for (const e of g.ents) e.hasEraser = false;
  er.x = er.home.x; er.y = er.home.y; er.carried = false; er.cool = 3;
  g.elev.open = false; g.elev.left = 0;
  ev(g, msg);
}
function updateElevator(g, dt) {
  const el = g.elev;
  if (g.board) return;
  if (el.open) {
    el.left -= dt;
    if (el.left <= 0) { el.left = 0; resetEraser(g, '⏰ エレベーターが閉まった！消しゴムは設置場所に戻った'); }
  }
  const target = el.open ? Math.min(1, el.left / CLOSE_PHASE) : 0;
  if (target > el.door) el.door = Math.min(target, el.door + dt * 1.2);
  else el.door = Math.max(target, el.door - dt * (el.open ? 2 : 3));
}
function startKnockback(g, o, from) {                      // 鬼が命中すると自身が17ブロック先まで弾き飛ばされる
  const sx = Math.floor(o.x / T), sy = Math.floor(o.y / T);
  const dist = new Int16Array(N * N).fill(-1), par = new Int16Array(N * N).fill(-1), q = [sy * N + sx];
  dist[q[0]] = 0; let maxD = 0;
  for (let h = 0; h < q.length; h++) {
    const c = q[h], cx = c % N, cy = (c / N) | 0;
    if (dist[c] >= KB_BLOCKS) continue;
    for (const [dx, dy] of [[1, 0], [-1, 0], [0, 1], [0, -1]]) {
      const nx = cx + dx, ny = cy + dy;
      if (isSolid(g, nx, ny, o)) continue;
      const ni = ny * N + nx;
      if (dist[ni] !== -1) continue;
      dist[ni] = dist[c] + 1; par[ni] = c; maxD = Math.max(maxD, dist[ni]); q.push(ni);
    }
  }
  const D = Math.min(KB_BLOCKS, maxD);
  if (D <= 0) return;
  let best = -1, bd = -1;
  for (const c of q) {
    if (dist[c] !== D) continue;
    const d = Math.hypot((c % N) * T + T / 2 - from.x, Math.floor(c / N) * T + T / 2 - from.y);
    if (d > bd) { bd = d; best = c; }
  }
  const pts = [];
  for (let c = best; c !== -1; c = par[c]) pts.push({ x: (c % N) * T + T / 2, y: Math.floor(c / N) * T + T / 2 });
  pts.reverse();
  o.kb = { pts, i: 1 }; o.next = null; o.path = null;
}
function advanceKnockback(e, dt) {
  let rem = KB_SPEED * dt;
  while (rem > 0 && e.kb) {
    const t = e.kb.pts[e.kb.i], dx = t.x - e.x, dy = t.y - e.y, d = Math.hypot(dx, dy);
    if (d <= rem) { e.x = t.x; e.y = t.y; rem -= d; e.kb.i++; if (e.kb.i >= e.kb.pts.length) e.kb = null; }
    else { e.x += dx / d * rem; e.y += dy / d * rem; rem = 0; }
  }
}
function hurtRunner(g, r, oni) {
  r.hp = Math.max(0, r.hp - HIT_DMG);
  r.invuln = INVULN; r.dmg++;
  if (r.hasEraser) dropEraser(g, r);
  fxNear(g, 'hit', r.x, r.y);
  if (oni) { oni.pts += PTS_HIT; startKnockback(g, oni, r); oni.stun = g.respSec; oni.resp = true; }
  if (r.hp <= 0) { r.alive = false; ev(g, '☠ ' + r.name + ' が力尽きた'); }
  else ev(g, '💥 ' + r.name + ' がやられた！HP ' + r.hp + '%');
}
function moveByInput(g, e, dt) {
  if (e.board) return;
  const ix = e.input.r - e.input.l, iy = e.input.d - e.input.u;
  if (!ix && !iy) return;
  const len = Math.hypot(ix, iy);
  const sp = e.role === 'oni' ? SPEED.oni * (g.board ? RUSH_MUL : 1) * g.oniMul
    : (e.hasEraser ? SPEED.carrier : SPEED.runner) * (e.boost > 0 ? BOOST_MUL : 1) * (e.crouch > 0 ? CROUCH_MUL : 1) * g.rules.runnerSpeed / 100;
  moveEnt(g, e, (ix / len) * sp * dt, (iy / len) * sp * dt);
}
// CPU鬼：経路を先読みして滑らかに曲がり、加減速しながら自然に追いかける（カクつき対策）
function cpuChase(g, e, dt, target, baseSpeed) {
  e.repath -= dt;
  const etx = Math.floor(e.x / T), ety = Math.floor(e.y / T), ttx = Math.floor(target.x / T), tty = Math.floor(target.y / T);
  if (e.repath <= 0 || !e.path) { e.path = (etx === ttx && ety === tty) ? null : pathTiles(g, etx, ety, ttx, tty, e); e.repath = 0.15; }
  let aim = target;
  if (e.path && e.path.length > 1) {
    aim = e.path[1];
    for (let i = Math.min(e.path.length - 1, 6); i >= 1; i--) {
      if (lineClear(g, e.x, e.y, e.path[i].x, e.path[i].y, ONI_R - 3, e)) { aim = e.path[i]; break; }
    }
  }
  const dx = aim.x - e.x, dy = aim.y - e.y, d = Math.hypot(dx, dy);
  const sp = baseSpeed * (g.board ? RUSH_MUL : 1) * g.oniMul;
  const dvx = d > 3 ? dx / d * sp : 0, dvy = d > 3 ? dy / d * sp : 0;
  const a = 1 - Math.exp(-dt * 10);                       // 速度をなめらかに変化させる
  e.vx += (dvx - e.vx) * a; e.vy += (dvy - e.vy) * a;
  moveEnt(g, e, e.vx * dt, e.vy * dt);
}
function cpuWander(g, e, dt) {
  if (e.idle > 0) { e.idle -= dt; e.vx *= 0.8; e.vy *= 0.8; return; }
  e.wpT = (e.wpT || 0) - dt;
  if (!e.wp || e.wpT <= 0 || Math.hypot(e.x - e.wp.x, e.y - e.wp.y) < 16) {
    if (e.wp && e.wpT > 0) { e.wp = null; e.idle = 0.4 + Math.random() * 0.8; return; }
    const cells = [];
    for (let ty = 1; ty < N; ty += 2) for (let tx = 1; tx < N; tx += 2) {
      const x = tx * T + T / 2, y = ty * T + T / 2;
      if (Math.hypot(x - e.x, y - e.y) > 3 * T) cells.push({ x, y });
    }
    e.wp = cells[Math.floor(Math.random() * cells.length)] || { x: MAP / 2, y: MAP / 2 };
    e.wpT = 14; e.path = null;
  }
  cpuChase(g, e, dt, e.wp, SPEED.cpu * 0.8);
}

function stepPlace(g, dt) {
  g.placeLeft -= dt;
  for (const e of g.ents) if (e.role === 'oni' && !e.cpu) moveByInput(g, e, dt);
  const er = g.eraser;
  if (!er.placed) {
    const human = g.ents.find((e) => e.role === 'oni' && !e.cpu);
    if (!human && g.placeLeft <= g.rules.placeTime - 3) { const p = randomSpot(g); placeEraser(g, p.x, p.y); }
    else if (g.placeLeft <= 0) {
      if (human && validSpot(g, human.x, human.y)) placeEraser(g, human.x, human.y);
      else { const p = randomSpot(g); placeEraser(g, p.x, p.y); }
    }
  }
  if (er.placed && g.placeLeft <= 0) {
    g.phase = 'play';
    for (const e of g.ents) if (e.role === 'oni') e.stun = START_STUN;
    ev(g, '🚨 スタート！自分のエレベーターから脱出せよ');
  }
}

function step(g, dt) {
  if (g.status !== 'playing') return;
  if (g.phase === 'count') {                               // 3,2,1,START!（この間は誰も動けない）
    g.countLeft -= dt;
    if (g.countLeft <= 0) { g.countLeft = 0; g.phase = 'place'; }
    return;
  }
  for (const e of g.ents) {
    if (e.invuln > 0) e.invuln -= dt;
    if (e.stun > 0) e.stun -= dt; else e.resp = false;
    if (e.boost > 0) e.boost -= dt;
    if (e.wcd > 0) e.wcd -= dt;
    if (e.crouch > 0) e.crouch -= dt;
    if (e.crouchCd > 0) e.crouchCd -= dt;
    if (e.tpCd > 0) e.tpCd -= dt;
    if (e.msgCd > 0) e.msgCd -= dt;
  }
  if (!g.ents.some((e) => e.role === 'runner' && e.alive)) { g.status = 'oniwin'; return; }
  if (g.phase === 'place') { stepPlace(g, dt); return; }

  g.time -= dt; g.playT += dt; g.pingClock += dt;
  if (g.time <= 0) { g.status = 'timeup'; return; }
  const er = g.eraser, el = g.elev;
  if (er.cool > 0) er.cool -= dt;
  updateElevator(g, dt);

  const runnersAlive = g.ents.filter((e) => e.role === 'runner' && e.alive);
  const carrier = g.ents.find((e) => e.hasEraser);

  for (const e of g.ents) {
    if (!e.alive) continue;
    if (e.kb) { advanceKnockback(e, dt); continue; }
    if (!e.cpu) {
      if (e.role === 'oni' && e.stun > 0) continue;
      moveByInput(g, e, dt);
    } else if (e.stun <= 0) {
      if (g.board) cpuChase(g, e, dt, elevFront(g.board.side), SPEED.cpuAngry);          // 突入したエレベーターへ急行して阻止
      else {
        let tgt = null, best = 1e9;                                                      // 見えている最寄りの逃げ側を自然に追跡
        for (const r of runnersAlive) {
          if (hidden(r) || r.board) continue;
          const d = Math.hypot(r.x - e.x, r.y - e.y);
          if (d < best) { best = d; tgt = r; }
        }
        if (tgt) cpuChase(g, e, dt, tgt, carrier ? SPEED.cpuAngry : SPEED.cpu);
        else cpuWander(g, e, dt);                                                        // 誰も見えなければ巡回
      }
    }
  }
  if (carrier) { er.x = carrier.x; er.y = carrier.y; }

  // 自動スタングレネード
  for (const r of runnersAlive) {
    if (r.item !== 'stun' || r.board) continue;
    const near = g.ents.filter((o) => o.role === 'oni' && o.stun <= 0 && Math.hypot(o.x - r.x, o.y - r.y) < GRENADE_R);
    if (!near.length) continue;
    r.item = null;
    for (const o of g.ents) if (o.role === 'oni' && Math.hypot(o.x - r.x, o.y - r.y) < GRENADE_R) { o.stun = Math.max(o.stun, GRENADE_STUN); o.resp = false; }
    fxNear(g, 'stun', r.x, r.y);
    ev(g, '💫 スタングレネード自動発動！鬼が8秒間停止');
  }

  for (const c of g.chests) if (c.open) { c.respawn -= dt; if (c.respawn <= 0) c.open = false; }
  for (const p of g.potions) {
    if (p.taken) { p.respawn -= dt; if (p.respawn <= 0) p.taken = false; continue; }
    for (const r of runnersAlive) {
      if (r.hp >= MAX_HP || r.board || Math.hypot(r.x - p.x, r.y - p.y) >= RUNNER_R + 22) continue;
      r.hp = Math.min(MAX_HP, r.hp + HEAL);
      p.taken = true; p.respawn = POTION_RESPAWN;
      evTo(r.id, '🧪 HPが回復した！ HP ' + r.hp + '%');
      break;
    }
  }
  // シャー芯：拾うと高ポイント＋EG。一定間隔で新しく出現
  if (g.rules.leads) {
    g.leadT -= dt;
    if (g.leadT <= 0) { g.leadT = LEAD_INTERVAL; spawnLead(g); }
    for (let i = g.leads.length - 1; i >= 0; i--) {
      const l = g.leads[i];
      for (const r of runnersAlive) {
        if (r.board || Math.hypot(r.x - l.x, r.y - l.y) >= RUNNER_R + 18) continue;
        g.leads.splice(i, 1);
        r.leads++; r.pts += PTS_LEAD;
        const saved = payEG(r.id, EG_LEAD);
        if (room_scores(g, r.id)) room_scores(g, r.id).eg += EG_LEAD;
        bumpStat(r.id, 'leads', 1);
        fxNear(g, 'lead', l.x, l.y);
        evTo(r.id, '✏️ シャー芯 +' + PTS_LEAD + 'pt' + (saved ? ' +' + EG_LEAD + ' EG' : '（ユーザー名登録で EG を獲得）'));
        break;
      }
    }
  }

  if (!er.carried && er.cool <= 0) {
    for (const r of runnersAlive) {
      if (r.board) continue;
      if (Math.hypot(r.x - er.x, r.y - er.y) < RUNNER_R + 22) {
        er.carried = true; r.hasEraser = true;
        el.open = true; el.left = ELEV_OPEN_SEC;
        ev(g, '📦 ' + r.name + ' が消しゴムを奪った！エレベーターが開く');
        break;
      }
    }
  }
  if (!er.carried && er.cool <= 0 && Math.hypot(er.x - er.home.x, er.y - er.home.y) > 10) {
    for (const o of g.ents) {
      if (o.role === 'oni' && o.stun <= 0 && Math.hypot(o.x - er.x, o.y - er.y) < ONI_R + 22) { resetEraser(g, '👹 鬼が消しゴムを奪還した！'); break; }
    }
  }

  // エレベーター突入：位置公開＋鬼1.5倍速＋扉が閉まるまで数秒
  if (!g.board) {
    for (const r of runnersAlive) {
      if (!r.hasEraser || !el.open || el.door <= DOOR_PASS) continue;
      const c = elevCenter(r.side);
      if (Math.abs(r.x - c.x) < T / 2 && Math.abs(r.y - c.y) < T / 2) {
        r.board = true; r.x = c.x; r.y = c.y;
        g.board = { id: r.id, side: r.side, left: BOARD_TIME, total: BOARD_TIME, d0: el.door };
        ev(g, '🚪 ' + r.name + ' がエレベーターに突入！ 鬼が急行する');
        break;
      }
    }
  }
  if (g.board) {
    const b = g.board, r = g.ents.find((e) => e.id === b.id);
    if (!r || !r.alive) g.board = null;
    else {
      b.left -= dt;
      el.door = b.d0 * Math.max(0, b.left / b.total);
      const c = elevCenter(b.side);
      const arrived = g.ents.find((o) => o.role === 'oni' && o.stun <= 0 && Math.hypot(o.x - c.x, o.y - c.y) < BOARD_CATCH);
      if (arrived) {
        const f = elevFront(b.side);
        r.board = false; r.x = f.x; r.y = f.y; g.board = null;
        hurtRunner(g, r, arrived);
        ev(g, '⚠ ドアが閉まる前に鬼が追いついた！');
      } else if (b.left <= 0) {
        let nd = 9999;
        for (const o of g.ents) if (o.role === 'oni') nd = Math.min(nd, Math.hypot(o.x - c.x, o.y - c.y));
        g.status = 'runwin'; g.slide = nd; g.escaper = r.id; return;
      }
    }
  }

  for (const o of g.ents) {
    if (o.role !== 'oni' || o.stun > 0) continue;
    for (const r of runnersAlive) {
      if (!r.alive || r.invuln > 0 || r.board || hidden(r)) continue;
      if (Math.hypot(r.x - o.x, r.y - o.y) < RUNNER_R + ONI_R - 4) { hurtRunner(g, r, o); break; }
    }
  }
  if (!g.ents.some((e) => e.role === 'runner' && e.alive)) g.status = 'oniwin';
}
function room_scores(g, id) { const m = g.room.match; return m && m.scores[id]; }

// ================= ラウンド終了：ポイント・EG・実績 =================
function standingsOf(m, delta) {
  return Object.keys(m.scores).map((id) => ({ id, name: m.scores[id].name, pts: m.scores[id].pts, delta: (delta && delta[id]) || 0, left: m.scores[id].left }))
    .sort((a, b) => b.pts - a.pts);
}
function finishRound(room, g) {
  const m = room.match, st = g.status, runnersWon = st === 'runwin';
  const humans = g.ents.filter((e) => !e.cpu), delta = {}, egRound = {};
  for (const e of humans) { delta[e.id] = e.pts || 0; egRound[e.id] = 0; }
  for (const e of humans) {
    if (runnersWon && e.role === 'runner') {
      if (e.id === g.escaper) { delta[e.id] += PTS_ESCAPE + (e.dmg ? 0 : PTS_NODMG); }
      else if (e.alive) delta[e.id] += PTS_ESCAPE_TEAM;
    }
    if (!runnersWon && e.role === 'oni') delta[e.id] += st === 'oniwin' ? PTS_WIPE : PTS_TIMEUP;
    const win = runnersWon ? (e.role === 'runner' && e.alive) : e.role === 'oni';
    if (win) egRound[e.id] += EG_FLOOR_WIN;
    if (runnersWon && e.id === g.escaper) {
      grantAch(e.id, 'first_escape'); bumpStat(e.id, 'escapes', 1);
      if (!e.dmg) grantAch(e.id, 'nodmg');
    }
    if (st === 'oniwin' && e.role === 'oni') { grantAch(e.id, 'wipe'); bumpStat(e.id, 'wipes', 1); }
  }
  for (const e of humans) {
    const sc = m.scores[e.id];
    if (sc) { sc.pts += delta[e.id]; sc.eg += egRound[e.id]; }
    payEG(e.id, egRound[e.id]);
  }
  m.done = m.solo ? (!runnersWon || g.floor >= m.total) : g.floor >= m.total;
  let final = null;
  if (m.done) {
    const stand = standingsOf(m, null), top = stand.length ? stand[0].pts : 0;
    const winners = stand.filter((s) => s.pts === top && !s.left).map((s) => s.id);
    const multi = !m.solo && m.humans >= 2;
    const cleared = m.solo && runnersWon && g.floor >= m.total;
    const egBonus = {};
    for (const id of Object.keys(m.scores)) {
      let b = 0;
      if (multi) { b += EG_PARTICIPATE; if (winners.includes(id)) b += EG_MATCH_WIN; }
      if (cleared) b += EG_CPU_WIN;
      egBonus[id] = b; m.scores[id].eg += b;
      payEG(id, b);
      if (!m.scores[id].left) {
        bumpStat(id, 'matches', 1);
        if (multi) grantAch(id, 'multi');
        if (cleared) { bumpStat(id, 'cpuWins', 1); grantAch(id, 'cpuwin'); }
      }
    }
    final = { winners: winners.map((id) => m.scores[id].name), cleared, solo: m.solo, egBonus };
  }
  for (const e of humans) {
    const saved = !!accOf(e.id);
    io.to(e.id).emit('roundEnd', {
      floor: g.floor, total: m.total, status: st, sudden: g.sudden, nextSudden: (g.floor + 1) % 2 === 0, done: m.done, saved,
      standings: standingsOf(m, delta).map((s) => ({ name: s.name, pts: s.pts, delta: s.delta, left: s.left, me: s.id === e.id })),
      egRound: egRound[e.id], egTotal: m.scores[e.id] ? m.scores[e.id].eg : 0,
      final: final ? { winners: final.winners, cleared: final.cleared, solo: final.solo, egBonus: final.egBonus[e.id] || 0 } : null
    });
  }
  g.endAt = Date.now() + (m.done ? MATCH_END_WAIT : ROUND_GAP);
}

// ================= 入力アクション =================
function padUnder(g, e) {
  for (let i = 0; i < g.pads.length; i++) if (Math.hypot(e.x - g.pads[i].x, e.y - g.pads[i].y) < WARP_ACT_R) return i;
  return -1;
}
function nearestChest(g, e) {
  for (const c of g.chests) if (!c.open && Math.hypot(e.x - c.x, e.y - c.y) < RUNNER_R + 36) return c;
  return null;
}
function doAction(g, e) {                                   // SPACE：ワープ(最優先)／設置／テレポート／宝箱
  if (g.status !== 'playing' || !e.alive || e.board || g.phase === 'count') return;
  const pi = padUnder(g, e);
  if (pi >= 0 && !(e.role === 'oni' && e.stun > 0)) {
    if (e.wcd > 0) { evTo(e.id, '⏳ ワープはあと ' + Math.ceil(e.wcd) + ' 秒'); return; }
    const dst = g.pads[pi ^ 1];
    fxNear(g, 'warp', e.x, e.y);
    e.x = dst.x; e.y = dst.y; e.wcd = WARP_CD; e.path = null;
    fxNear(g, 'warp', e.x, e.y);
    return;
  }
  if (g.phase === 'place') {
    if (e.role !== 'oni' || g.eraser.placed) return;
    if (validSpot(g, e.x, e.y)) placeEraser(g, e.x, e.y);
    else evTo(e.id, '❌ ここには置けない（エレベーター・ワープ・宝箱などに近すぎる）');
    return;
  }
  if (e.role === 'oni') {
    const respawning = e.stun > 0 && e.resp;
    if (e.stun > 0 && !e.resp) { evTo(e.id, '❌ 今はテレポートできない'); return; }
    if (!respawning && e.tpCd > 0) { evTo(e.id, '⏳ テレポートはあと ' + Math.ceil(e.tpCd) + ' 秒'); return; }
    fxNear(g, 'warp', e.x, e.y);
    e.x = e.spawn.x; e.y = e.spawn.y; e.path = null;
    if (respawning) e.resp = false; else e.tpCd = ONI_TP_CD;
    fxNear(g, 'warp', e.x, e.y);
    evTo(e.id, '🌀 スポーン位置へテレポート');
    return;
  }
  const c = nearestChest(g, e);
  if (!c) return;
  if (e.item) { evTo(e.id, '⚠ アイテムは1個までしか持てない'); return; }
  e.item = ITEMS[Math.floor(Math.random() * ITEMS.length)];
  c.open = true; c.respawn = CHEST_RESPAWN;
  evTo(e.id, '🎁 ' + ITEM_NAME[e.item] + ' を入手！' + (e.item === 'stun' ? '（鬼が近づくと自動発動）' : '（Qキー / ボタンで使用）'));
}
function useItem(g, e) {                                    // Q：スピードブーツ（スタンは自動）
  if (g.phase !== 'play' || g.status !== 'playing' || !e.alive || e.role !== 'runner' || !e.item || e.board) return;
  if (e.item === 'stun') { evTo(e.id, '💫 スタングレネードは鬼が近づくと自動で発動する'); return; }
  e.item = null; e.boost = BOOST_SEC; evTo(e.id, '👟 スピードアップ！');
}
function doCrouch(g, e) {                                   // しゃがみ：2秒間 完全に透明（CT10秒・移動速度低下）
  if (g.phase !== 'play' || g.status !== 'playing' || !e.alive || e.role !== 'runner' || e.board) return;
  if (!g.rules.crouch) { evTo(e.id, '❌ このルームではしゃがみが無効'); return; }
  if (e.crouch > 0) return;
  if (e.crouchCd > 0) { evTo(e.id, '⏳ しゃがみはあと ' + Math.ceil(e.crouchCd) + ' 秒'); return; }
  e.crouch = CROUCH_SEC; e.crouchCd = CROUCH_CD;
  evTo(e.id, '🫥 しゃがみ！2秒間 完全に透明（移動は遅くなる）');
}

// ================= 受信者ごとの状態 =================
function snapshot(g, r) {
  let ref = r;
  if (r.role === 'runner' && !r.alive) ref = g.ents.find((e) => e.role === 'runner' && e.alive) || r;
  const boarding = !!(g.board && g.board.id === r.id);
  const ghost = boarding ? 650 : (r.role === 'oni' ? CFG.ghostR.oni : CFG.ghostR.runner);
  const ents = [];
  for (const e of g.ents) {
    if (e === r) continue;
    const info = { id: e.id, n: e.name, ti: e.title, x: e.x, y: e.y, role: e.role, al: e.alive, e: e.hasEraser, st: e.stun > 0, inv: e.invuln > 0, sd: e.side, sk: e.skin, iv: hidden(e), cr: e.crouch > 0, hp: e.hp };
    if (e.role === r.role) ents.push(info);
    else if (e.alive && !hidden(e) && Math.hypot(e.x - ref.x, e.y - ref.y) < ghost) ents.push(info);   // しゃがみ中は鬼に完全に見えない
  }
  const E = g.eraser;
  let er = null, hint = null, eh = null;
  if (E.placed) {
    if (r.role === 'oni') er = E.carried ? { c: true } : { x: E.x, y: E.y, c: false };
    else if (E.carried) er = { c: true, x: E.x, y: E.y };
    else if (Math.hypot(E.x - ref.x, E.y - ref.y) < ghost) er = { x: E.x, y: E.y, c: false };
    if (r.role === 'runner' && !E.carried && g.playT > HINT_AFTER) hint = { x: E.x + g.hintOff.x, y: E.y + g.hintOff.y, r: 260 };
    if (r.role === 'runner' && r.alive && g.phase === 'play' && !r.hasEraser) eh = { x: E.x + g.hintOff.x, y: E.y + g.hintOff.y };
  }
  let ping = null;
  if (r.role === 'oni' && g.phase === 'play' && g.pingClock % 7 < 1.5) {
    const c = g.ents.find((e) => e.hasEraser);
    if (c && !hidden(c) && !c.board) ping = { x: c.x, y: c.y };
  }
  let rev = null;
  if (r.role === 'oni' && g.board) { const c = elevCenter(g.board.side); rev = { x: c.x, y: c.y, side: g.board.side, left: g.board.left }; }
  let oa = null, ld = null;
  if (r.role === 'runner') {
    oa = g.ents.filter((e) => e.role === 'oni').map((e) => ({ x: Math.round(e.x / 160) * 160, y: Math.round(e.y / 160) * 160 }));
    ld = g.leads.map((l) => ({ x: l.x, y: l.y }));
  }
  return {
    s: g.status, ph: g.phase, pl: Math.max(0, g.placeLeft), cd: Math.max(0, g.countLeft), placed: E.placed, t: g.time, slide: g.slide, role: r.role, side: ref.side,
    fl: g.floor, tf: g.total, sd: g.sudden,
    me: {
      x: r.x, y: r.y, al: r.alive, hp: r.hp, e: r.hasEraser, inv: r.invuln > 0, st: r.stun > 0, rs: r.stun > 0 && r.resp,
      item: r.item, boost: Math.max(0, r.boost), wcd: Math.max(0, r.wcd), tp: Math.max(0, r.tpCd), cr: Math.max(0, r.crouch), crCd: Math.max(0, r.crouchCd), np: padUnder(g, r),
      board: boarding, nc: r.role === 'runner' && r.alive && !r.board && !!nearestChest(g, r), pts: r.pts, leads: r.leads
    },
    cam: { x: ref.x, y: ref.y }, ents, ping, rev, er, hint, eh, oa, ld,
    bd: g.board ? { side: g.board.side, left: g.board.left, total: g.board.total } : null,
    ch: g.chests.map((c) => (c.open ? 1 : 0)), pt: g.potions.map((p) => (p.taken ? 1 : 0)),
    el: { open: g.elev.open, left: g.elev.left, door: g.elev.door },
    n: g.ents.filter((e) => e.role === 'runner' && e.alive).length
  };
}

// ================= 60fps ループ =================
let last = process.hrtime.bigint();
setInterval(() => {
  const now = process.hrtime.bigint();
  const dt = Math.min(Number(now - last) / 1e9, 0.05);
  last = now;
  for (const room of rooms.values()) {
    const g = room.game;
    if (!g) continue;
    const prev = g.status, prevPhase = g.phase;
    step(g, dt);
    const changed = prev !== g.status || prevPhase !== g.phase;
    for (const e of g.ents) {
      if (e.cpu) continue;
      const s = io.sockets.sockets.get(e.id);
      if (!s) continue;
      const snap = snapshot(g, e);
      if (changed) s.emit('state', snap); else s.volatile.emit('state', snap);
    }
    if (g.status !== 'playing') {
      if (!g.finished) { g.finished = true; finishRound(room, g); }
      else if (Date.now() > g.endAt) {
        if (room.match.done) { if (!room.solo) toLobby(room); }   // CPU戦は自動でロビーに戻さない（タイトルへ戻るのはプレイヤーの操作）
        else startRound(room, room.match.floor + 1);               // 次の階へ（ロールチェンジ）
      }
    }
  }
}, 1000 / 60);

// ================= Socket.io =================
io.on('connection', (socket) => {
  socket.emit('catalog', {
    ach: Object.keys(ACH).map((id) => ({ id, n: ACH[id].n, d: ACH[id].d, eg: ACH[id].eg, t: ACH[id].t, need: ACH[id].need || 0, stat: ACH[id].stat || null })),
    price: SKIN_PRICE, free: FREE_SKINS, egCpu: EG_CPU_WIN, egLead: EG_LEAD, ptsLead: PTS_LEAD
  });
  const reply = (evn, ok, msg) => socket.emit(evn, { ok, msg });
  const nameNow = (d) => accName(socket.id) || (d && d.name);
  socket.on('create', (d) => {
    leaveRoom(socket.id);
    const room = makeRoom(socket, false);
    if (!room) return;
    addPlayer(room, socket, nameNow(d), 'auto', d && d.skin);
    sendLobby(room);
  });
  socket.on('solo', (d) => {                                // CPUと戦う：即ゲーム画面へ。ゲーム内で 3,2,1,START!
    leaveRoom(socket.id);
    const room = makeRoom(socket, true);
    if (!room) return;
    room.soloFloors = Math.max(1, Math.min(9, parseInt(d && d.floors, 10) || 3));
    addPlayer(room, socket, nameNow(d), 'runner', d && d.skin);
    startMatch(room);
  });
  socket.on('join', (d) => {
    const code = String((d && d.code) || '').replace(/\D/g, '').slice(0, 5);
    if (code.length !== 5) { socket.emit('errmsg', '5桁のルームコードを入力してください'); return; }
    const room = rooms.get(code);
    if (!room || room.solo) { socket.emit('errmsg', 'そのルームは見つかりません'); return; }
    if (room.players.size >= MAX_PLAYERS && !room.players.has(socket.id)) { socket.emit('errmsg', 'ルームが満員です'); return; }
    leaveRoom(socket.id);
    addPlayer(room, socket, nameNow(d), 'auto', d && d.skin);
    sendLobby(room);
  });
  socket.on('setRole', (role) => {
    const room = sockRoom.get(socket.id);
    if (!room || room.state !== 'lobby' || !['auto', 'runner', 'oni'].includes(role)) return;
    room.players.get(socket.id).role = role;
    sendLobby(room);
  });
  socket.on('setSkin', (v) => {
    const room = sockRoom.get(socket.id);
    if (!room || room.state !== 'lobby') return;
    const s = cleanSkin(v);
    if (!canUseSkin(socket.id, s)) { socket.emit('errmsg', 'そのスキンはまだ持っていません（ショップで購入できます）'); return; }
    room.players.get(socket.id).skin = s;
    sendLobby(room);
  });
  socket.on('setReady', (v) => {
    const room = sockRoom.get(socket.id);
    if (!room || room.state !== 'lobby') return;
    room.players.get(socket.id).ready = !!v;
    sendLobby(room);
  });
  socket.on('start', () => {
    const room = sockRoom.get(socket.id);
    if (!room || room.host !== socket.id || room.state !== 'lobby' || room.solo) return;
    beginCountdown(room);                                   // ロビー中央で 3,2,1,START! → ゲーム画面へ
  });
  socket.on('input', (inp) => {
    const room = sockRoom.get(socket.id);
    if (!room || !room.game || !inp) return;
    const e = room.game.ents.find((x) => x.id === socket.id);
    if (e) e.input = { u: inp.u ? 1 : 0, d: inp.d ? 1 : 0, l: inp.l ? 1 : 0, r: inp.r ? 1 : 0 };
  });
  const withEnt = (fn) => () => {
    const room = sockRoom.get(socket.id), g = room && room.game, e = g && g.ents.find((x) => x.id === socket.id);
    if (e) fn(g, e);
  };
  socket.on('action', withEnt(doAction));
  socket.on('useItem', withEnt(useItem));
  socket.on('crouch', withEnt(doCrouch));
  socket.on('backToLobby', () => {
    const room = sockRoom.get(socket.id);
    if (room && !room.solo && room.match && room.match.done && room.game && room.game.status !== 'playing') toLobby(room);
  });

  // ---- アカウント（ユーザー名の重複不可・1端末1アカウント）----
  const renameInRoom = (name) => { const room = sockRoom.get(socket.id); const p = room && room.players.get(socket.id); if (p) { p.name = name; sendLobby(room); } };
  socket.on('auth', (d) => {
    const id = byToken.get(sha((d && d.token) || '')), acc = id && accounts.get(id);
    if (acc) { attach(socket, acc); bindDevice(acc, cleanDevice(d.device)); notifyPresence(acc); } else socket.emit('authFail');
    sendProfile(socket);
  });
  socket.on('register', (d) => {
    if (accOf(socket.id)) return reply('accMsg', false, 'すでにログイン中です');
    const dev = cleanDevice(d && d.device);
    if (!dev) return reply('accMsg', false, '端末を識別できませんでした。ページを再読み込みしてください');
    if (byDevice.has(dev)) { const ex = accounts.get(byDevice.get(dev)); return reply('accMsg', false, 'この端末ではすでにアカウント「' + (ex ? ex.name : '?') + '」を作成済みです（1端末1アカウント）。ログインキーでログインしてください'); }
    const name = cleanAccName(d && d.name);
    if (!name) return reply('accMsg', false, 'ユーザー名は2〜12文字（英数字・かな・漢字・_ -）');
    if (byName.has(name.toLowerCase())) return reply('accMsg', false, 'そのユーザー名はすでに使われています');
    const token = crypto.randomBytes(16).toString('hex');
    const acc = normAcc({ id: crypto.randomBytes(8).toString('hex'), name, nameKey: name.toLowerCase(), tokenHash: sha(token) });
    accounts.set(acc.id, acc); byName.set(acc.nameKey, acc.id); byToken.set(acc.tokenHash, acc.id);
    bindDevice(acc, dev); saveAccounts();
    attach(socket, acc);
    socket.emit('registered', { token, name });
    sendProfile(socket); renameInRoom(name);
    reply('accMsg', true, 'ユーザー名「' + name + '」を登録した！');
  });
  socket.on('rename', (d) => {
    const acc = accOf(socket.id);
    if (!acc) return reply('accMsg', false, '先にユーザー名を登録してください');
    const name = cleanAccName(d && d.name);
    if (!name) return reply('accMsg', false, 'ユーザー名は2〜12文字（英数字・かな・漢字・_ -）');
    const key = name.toLowerCase();
    if (byName.has(key) && byName.get(key) !== acc.id) return reply('accMsg', false, 'そのユーザー名はすでに使われています');
    byName.delete(acc.nameKey); acc.name = name; acc.nameKey = key; byName.set(key, acc.id); saveAccounts();
    sendProfile(socket); renameInRoom(name); notifyPresence(acc);
    reply('accMsg', true, 'ユーザー名を「' + name + '」に変更した');
  });
  socket.on('loginKey', (d) => {
    const id = byToken.get(sha((d && d.token) || '')), acc = id && accounts.get(id);
    if (!acc) return reply('accMsg', false, 'ログインキーが正しくありません');
    const dev = cleanDevice(d && d.device);
    if (dev && byDevice.has(dev) && byDevice.get(dev) !== acc.id) return reply('accMsg', false, 'この端末ではすでに別のアカウントを使っています（1端末1アカウント）');
    attach(socket, acc); bindDevice(acc, dev);
    socket.emit('registered', { token: String(d.token).trim(), name: acc.name });
    sendProfile(socket); notifyPresence(acc); renameInRoom(acc.name);
    reply('accMsg', true, '「' + acc.name + '」でログインした');
  });

  socket.on('logout', () => { detach(socket); sendProfile(socket); });

  // ---- ショップ・称号 ----
  socket.on('buySkin', (d) => {
    const acc = accOf(socket.id), id = parseInt(d && d.id, 10);
    if (!acc) return reply('shopMsg', false, 'ユーザー名を登録するとEGを貯めてスキンを購入できます');
    if (!(id >= 0 && id < SKIN_COUNT)) return reply('shopMsg', false, 'そのスキンはありません');
    if (acc.owned.includes(id)) return reply('shopMsg', false, 'すでに所有しています');
    if (acc.eg < SKIN_PRICE) return reply('shopMsg', false, 'EGが足りません（' + SKIN_PRICE + ' EG 必要）');
    acc.eg -= SKIN_PRICE; acc.owned.push(id); acc.stats.purchases++; saveAccounts();
    emitWallet(acc); grantAch(socket.id, 'shopper');
    socket.emit('bought', { id });
    reply('shopMsg', true, 'スキンを購入した！');
  });
  socket.on('setTitle', (d) => {
    const acc = accOf(socket.id), id = d && d.id;
    if (!acc) return;
    if (id && !acc.ach.includes(id)) return;
    acc.title = id || null; saveAccounts(); emitWallet(acc);
    const room = sockRoom.get(socket.id); if (room) sendLobby(room);
    notifyPresence(acc);
  });

  // ---- フレンド（ユーザー名だけの申請・承認制）----
  const byNameAcc = (n) => { const id = byName.get(String(n || '').trim().toLowerCase()); return id ? accounts.get(id) : null; };
  const link = (a, b) => { if (!a.friends.includes(b.id)) a.friends.push(b.id); if (!b.friends.includes(a.id)) b.friends.push(a.id); };
  const clearReq = (a, b) => { a.reqIn = a.reqIn.filter((x) => x !== b.id); a.reqOut = a.reqOut.filter((x) => x !== b.id); b.reqIn = b.reqIn.filter((x) => x !== a.id); b.reqOut = b.reqOut.filter((x) => x !== a.id); };
  const tellAcc = (acc, ev2, payload) => { for (const sid of socksOf(acc)) io.to(sid).emit(ev2, payload); };
  socket.on('friendRequest', (d) => {
    const me = accOf(socket.id);
    if (!me) return reply('friendMsg', false, '先にユーザー名を登録してください');
    const now = Date.now(), log = (socket.data.fr = (socket.data.fr || []).filter((t) => now - t < 60000));
    if (log.length >= 10) return reply('friendMsg', false, '申請が多すぎます。少し待ってください');
    log.push(now);
    const f = byNameAcc(d && d.name);
    if (!f) return reply('friendMsg', false, 'そのユーザー名は見つかりません');
    if (f.id === me.id) return reply('friendMsg', false, '自分自身には送れません');
    if (me.friends.includes(f.id)) return reply('friendMsg', true, 'すでにフレンドです');
    if (me.reqOut.includes(f.id)) return reply('friendMsg', false, 'すでに申請中です');
    if (me.reqIn.includes(f.id)) {                          // 相手からも申請が来ていれば即フレンド
      clearReq(me, f); link(me, f); saveAccounts(); notifyPresence(me); notifyPresence(f);
      tellAcc(f, 'friendMsg', { ok: true, msg: me.name + ' さんとフレンドになった！' });
      return reply('friendMsg', true, f.name + ' さんとフレンドになった！');
    }
    me.reqOut.push(f.id); f.reqIn.push(me.id); saveAccounts();
    pushFriends(me); pushFriends(f);
    tellAcc(f, 'friendReq', { from: me.name });
    reply('friendMsg', true, f.name + ' さんに申請を送った');
  });
  socket.on('friendRespond', (d) => {
    const me = accOf(socket.id), f = byNameAcc(d && d.name);
    if (!me || !f || !me.reqIn.includes(f.id)) return;
    clearReq(me, f);
    if (d.accept) { link(me, f); tellAcc(f, 'friendMsg', { ok: true, msg: me.name + ' さんが申請を承認した！' }); reply('friendMsg', true, f.name + ' さんとフレンドになった！'); }
    else reply('friendMsg', true, f.name + ' さんの申請を断った');
    saveAccounts(); notifyPresence(me); notifyPresence(f);
  });
  socket.on('cancelRequest', (d) => {
    const me = accOf(socket.id), f = byNameAcc(d && d.name);
    if (!me || !f) return;
    clearReq(me, f); saveAccounts(); pushFriends(me); pushFriends(f);
  });
  socket.on('removeFriend', (d) => {
    const me = accOf(socket.id), f = byNameAcc(d && d.name);
    if (!me || !f) return;
    me.friends = me.friends.filter((x) => x !== f.id); f.friends = f.friends.filter((x) => x !== me.id); saveAccounts();
    notifyPresence(me); notifyPresence(f);
    reply('friendMsg', true, f.name + ' さんをフレンドから外した');
  });
  socket.on('friends', () => { const a = accOf(socket.id); if (a) socket.emit('friends', friendEntries(a)); });
  socket.on('joinFriend', (d) => {
    const me = accOf(socket.id), f = byNameAcc(d && d.name);
    if (!me || !f || !me.friends.includes(f.id)) return reply('friendMsg', false, 'フレンドが見つかりません');
    let room = null;
    for (const sid of socksOf(f)) { const r = sockRoom.get(sid); if (r && !r.solo) { room = r; break; } }
    if (!room) return reply('friendMsg', false, f.name + ' さんは今ルームにいません');
    if (room.players.size >= MAX_PLAYERS && !room.players.has(socket.id)) return reply('friendMsg', false, 'ルームが満員です');
    if (sockRoom.get(socket.id) !== room) { leaveRoom(socket.id); addPlayer(room, socket, me.name, 'auto', d && d.skin); }
    sendLobby(room);
  });
  socket.on('invite', (d) => {
    const me = accOf(socket.id), room = sockRoom.get(socket.id), f = byNameAcc(d && d.name);
    if (!me || !f || !me.friends.includes(f.id)) return reply('friendMsg', false, 'フレンドが見つかりません');
    if (!room || room.solo) return reply('friendMsg', false, '先にルームを作ってください');
    if (!socksOf(f).size) return reply('friendMsg', false, f.name + ' さんはオフラインです');
    tellAcc(f, 'invite', { from: me.name, code: room.code });
    reply('friendMsg', true, f.name + ' さんに招待を送った');
  });

  socket.on('setRules', (r) => {
    const room = sockRoom.get(socket.id);
    if (!room || room.host !== socket.id || room.state !== 'lobby' || room.solo) return;
    room.rules = cleanRules(r);
    sendLobby(room);
  });
  socket.on('chat', (i) => {
    i = parseInt(i, 10);
    const room = sockRoom.get(socket.id);
    if (!room || !(i >= 0 && i < CHATS.length)) return;
    const p = room.players.get(socket.id), now = Date.now();
    if (!p || now - (p.lastChat || 0) < 600) return;
    p.lastChat = now;
    for (const id of room.players.keys()) io.to(id).emit('chat', { id: socket.id, i });
  });
  socket.on('leave', () => leaveRoom(socket.id));
  socket.on('disconnect', () => { leaveRoom(socket.id); detach(socket); });
});

const PORT = process.env.PORT || 3000;
server.listen(PORT, () => console.log('Server listening on ' + PORT));
