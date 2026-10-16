'use strict';
const express = require('express');
const http = require('http');
const path = require('path');
const { Server } = require('socket.io');

const app = express();
const server = http.createServer(app);
const io = new Server(server);
app.use(express.static(path.join(__dirname, 'public')));

// ================= 定数 =================
const N = 19, T = 80, MAP = N * T, MID = (N - 1) / 2;
// エレベーター：0=上 1=右 2=下 3=左（時計回り）。dx,dy は迷路内側への向き
const ELEVS = [
  { tx: MID, ty: 0, dx: 0, dy: 1 },
  { tx: N - 1, ty: MID, dx: -1, dy: 0 },
  { tx: MID, ty: N - 1, dx: 0, dy: -1 },
  { tx: 0, ty: MID, dx: 1, dy: 0 }
];
const CFG = {
  zoom: 1.9,
  lightR: { runner: 230, oni: 270 },   // 明るく照らされる範囲
  ghostR: { runner: 320, oni: 370 }    // この範囲までは暗がりに「影」として見える
};
const RUNNER_R = 18, ONI_R = 22;
const SPEED = { runner: 236, carrier: 214, oni: 230, cpu: 204, cpuAngry: 224 };
const ELEV_OPEN_SEC = 20, CLOSE_PHASE = 8, DOOR_PASS = 0.15;
const INVULN = 3, STUN = 2, START_STUN = 2, MATCH_TIME = 300;
const PLACE_TIME = 15, PLACE_MIN = 300, HINT_AFTER = 45;
const MAX_PLAYERS = 8;

const elevIndexAt = (tx, ty) => { for (let i = 0; i < 4; i++) if (ELEVS[i].tx === tx && ELEVS[i].ty === ty) return i; return -1; };
const elevCenter = (i) => ({ x: ELEVS[i].tx * T + T / 2, y: ELEVS[i].ty * T + T / 2 });
function shuffle(a) { for (let i = a.length - 1; i > 0; i--) { const j = Math.floor(Math.random() * (i + 1)); [a[i], a[j]] = [a[j], a[i]]; } return a; }

// ================= 迷路生成（毎回ランダム・全通路が必ず連結）=================
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
  for (let k = 0; k < 14; k++) {              // 周回路
    const x = 1 + Math.floor(Math.random() * (N - 2));
    const y = 1 + Math.floor(Math.random() * (N - 2));
    if ((x + y) % 2 === 1) g[y][x] = 0;
  }
  for (const E of ELEVS) g[E.ty][E.tx] = 0;   // 4辺のエレベーター
  return g;
}

// ================= 衝突 =================
// ent: 判定対象（runner は自分のエレベーターだけ扉が開いていれば入れる）。null は視線判定用（エレベーター=壁）
function isSolid(g, tx, ty, ent) {
  if (tx < 0 || ty < 0 || tx >= N || ty >= N) return true;
  if (g.grid[ty][tx] === 1) return true;
  const i = elevIndexAt(tx, ty);
  if (i >= 0) return !(ent && ent.role === 'runner' && ent.side === i && g.elev.door > DOOR_PASS);
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
function losClear(g, x0, y0, x1, y1) {
  const n = Math.ceil(Math.hypot(x1 - x0, y1 - y0) / 12);
  for (let i = 1; i < n; i++) {
    const t = i / n;
    if (isSolid(g, Math.floor((x0 + (x1 - x0) * t) / T), Math.floor((y0 + (y1 - y0) * t) / T), null)) return false;
  }
  return true;
}

// BFS（CPU鬼用）
const bfsParent = new Int16Array(N * N), bfsQueue = new Int16Array(N * N);
function nextTileToward(g, fx, fy, tx, ty, ent) {
  if (fx === tx && fy === ty) return null;
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
  let cur = goal;
  while (bfsParent[cur] !== start) cur = bfsParent[cur];
  return { tx: cur % N, ty: (cur / N) | 0 };
}

// ================= ルーム管理（5桁コード）=================
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
  const players = [...room.players.values()].map((p) => ({ id: p.id, name: p.name, role: p.role }));
  for (const id of room.players.keys()) io.to(id).emit('lobby', { code: room.code, state: room.state, host: room.host, players, you: id });
}
function toLobby(room) { room.state = 'lobby'; room.game = null; sendLobby(room); }
function makeRoom(socket) {
  const code = newCode();
  if (!code) { socket.emit('errmsg', 'ルームを作れませんでした'); return null; }
  const room = { code, players: new Map(), host: socket.id, state: 'lobby', game: null };
  rooms.set(code, room);
  return room;
}
function addPlayer(room, socket, name, role) {
  room.players.set(socket.id, { id: socket.id, name: cleanName(name), role });
  sockRoom.set(socket.id, room);
}
function leaveRoom(id) {
  const room = sockRoom.get(id);
  if (!room) return;
  sockRoom.delete(id);
  room.players.delete(id);
  const g = room.game;
  if (g) {
    const ent = g.ents.find((e) => e.id === id);
    if (ent) {
      if (ent.hasEraser) dropEraser(g, ent);
      g.ents = g.ents.filter((e) => e !== ent);
      if (!g.ents.some((e) => e.role === 'oni')) addEnt(g, 'cpu' + Date.now(), 'CPU鬼', 'oni', true, Math.floor(Math.random() * 4));
    }
  }
  if (room.players.size === 0) { rooms.delete(room.code); return; }
  if (room.host === id) room.host = room.players.keys().next().value;
  sendLobby(room);
}

// ================= ゲーム開始 =================
function addEnt(g, id, name, role, cpu, side) {
  const E = ELEVS[side];
  const k = g.ents.filter((e) => e.side === side).length;
  const off = [0, 16, -16][k % 3];
  const px = E.dy !== 0 ? 1 : 0, py = E.dx !== 0 ? 1 : 0;
  g.ents.push({
    id, name, role, cpu, side,
    x: (E.tx + E.dx) * T + T / 2 + px * off, y: (E.ty + E.dy) * T + T / 2 + py * off,
    input: { u: 0, d: 0, l: 0, r: 0 }, alive: true, hasEraser: false, invuln: 0, stun: 0, next: null, repath: 0
  });
}

function startGame(room) {
  const list = [...room.players.values()];
  const target = list.length >= 2 ? Math.max(1, Math.floor(list.length / 3)) : 0;
  let oniCount = list.filter((p) => p.role === 'oni').length;
  for (const p of list) p.assigned = p.role;
  for (const p of shuffle(list.filter((p) => p.role === 'auto'))) {
    if (oniCount < target) { p.assigned = 'oni'; oniCount++; } else p.assigned = 'runner';
  }
  if (!list.some((p) => p.assigned === 'runner')) shuffle(list.filter((p) => p.assigned === 'oni'))[0].assigned = 'runner';

  const ang = Math.random() * Math.PI * 2, mag = 40 + Math.random() * 80;
  const g = {
    room, grid: generateMaze(), status: 'playing', phase: 'place', placeLeft: PLACE_TIME,
    time: MATCH_TIME, playT: 0, endAt: 0, pingClock: 0, ents: [],
    hintOff: { x: Math.cos(ang) * mag, y: Math.sin(ang) * mag },
    eraser: { x: 0, y: 0, home: { x: 0, y: 0 }, placed: false, carried: false, cool: 0 },
    elev: { open: false, left: 0, door: 0 }
  };
  const sides = shuffle([0, 1, 2, 3]);
  let si = 0;
  for (const p of list) if (p.assigned === 'runner') addEnt(g, p.id, p.name, 'runner', false, sides[si++ % 4]);
  for (const p of list) if (p.assigned === 'oni') addEnt(g, p.id, p.name, 'oni', false, sides[si++ % 4]);
  if (!g.ents.some((e) => e.role === 'oni')) addEnt(g, 'cpu1', 'CPU鬼', 'oni', true, sides[si++ % 4]);

  room.game = g; room.state = 'playing';
  for (const e of g.ents) if (!e.cpu) {
    io.to(e.id).emit('init', { grid: g.grid.map((r) => r.join('')), T, N, map: MAP, elevs: ELEVS, cfg: CFG, role: e.role, side: e.side, name: e.name, matchTime: MATCH_TIME, placeTime: PLACE_TIME });
  }
  sendLobby(room);
}

// ================= ゲームロジック =================
function ev(g, msg) { for (const e of g.ents) if (!e.cpu) io.to(e.id).emit('ev', msg); }

function validSpot(g, x, y) {
  const tx = Math.floor(x / T), ty = Math.floor(y / T);
  if (tx < 0 || ty < 0 || tx >= N || ty >= N || g.grid[ty][tx] === 1 || elevIndexAt(tx, ty) >= 0) return false;
  for (let i = 0; i < 4; i++) { const c = elevCenter(i); if (Math.hypot(x - c.x, y - c.y) < PLACE_MIN) return false; }
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
  if (el.open) {
    el.left -= dt;
    if (el.left <= 0) { el.left = 0; resetEraser(g, '⏰ エレベーターが閉まった！消しゴムは設置場所に戻った'); }
  }
  const target = el.open ? Math.min(1, el.left / CLOSE_PHASE) : 0;
  if (target > el.door) el.door = Math.min(target, el.door + dt * 1.2);
  else el.door = Math.max(target, el.door - dt * (el.open ? 2 : 3));
}

function moveByInput(g, e, dt) {
  const ix = e.input.r - e.input.l, iy = e.input.d - e.input.u;
  if (!ix && !iy) return;
  const len = Math.hypot(ix, iy);
  const sp = e.role === 'oni' ? SPEED.oni : (e.hasEraser ? SPEED.carrier : SPEED.runner);
  moveEnt(g, e, (ix / len) * sp * dt, (iy / len) * sp * dt);
}
function cpuMove(g, e, dt, tgt, angry) {
  e.repath -= dt;
  const otx = Math.floor(e.x / T), oty = Math.floor(e.y / T), ptx = Math.floor(tgt.x / T), pty = Math.floor(tgt.y / T);
  if (e.repath <= 0) { e.next = nextTileToward(g, otx, oty, ptx, pty, e); e.repath = 0.1; }
  let tx = tgt.x, ty = tgt.y;
  if (e.next && !(otx === ptx && oty === pty)) { tx = e.next.tx * T + T / 2; ty = e.next.ty * T + T / 2; }
  const dx = tx - e.x, dy = ty - e.y, d = Math.hypot(dx, dy);
  if (d > 0.5) {
    const m = Math.min((angry ? SPEED.cpuAngry : SPEED.cpu) * dt, d);
    moveEnt(g, e, (dx / d) * m, (dy / d) * m);
  }
}

function stepPlace(g, dt) {
  g.placeLeft -= dt;
  for (const e of g.ents) if (e.role === 'oni' && !e.cpu) moveByInput(g, e, dt);   // 逃げ側は待機、鬼は自由に動いて設置場所を選ぶ
  const er = g.eraser;
  if (!er.placed) {
    const human = g.ents.find((e) => e.role === 'oni' && !e.cpu);
    if (!human && g.placeLeft <= PLACE_TIME - 3) { const p = randomSpot(g); placeEraser(g, p.x, p.y); }
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
  for (const e of g.ents) { if (e.invuln > 0) e.invuln -= dt; if (e.stun > 0) e.stun -= dt; }
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
    if (!e.cpu) {
      if (e.role === 'oni' && e.stun > 0) continue;
      moveByInput(g, e, dt);
    } else if (e.stun <= 0 && runnersAlive.length) {
      let tgt = carrier && carrier.role === 'runner' ? carrier : null;
      if (!tgt) {
        let best = 1e9;
        for (const r of runnersAlive) { const d = Math.hypot(r.x - e.x, r.y - e.y); if (d < best) { best = d; tgt = r; } }
      }
      cpuMove(g, e, dt, tgt, !!carrier);
    }
  }
  if (carrier) { er.x = carrier.x; er.y = carrier.y; }

  // 取得
  if (!er.carried && er.cool <= 0) {
    for (const r of runnersAlive) {
      if (Math.hypot(r.x - er.x, r.y - er.y) < RUNNER_R + 22) {
        er.carried = true; r.hasEraser = true;
        el.open = true; el.left = ELEV_OPEN_SEC;
        ev(g, '📦 ' + r.name + ' が消しゴムを奪った！エレベーターが開く');
        break;
      }
    }
  }
  // 奪還（落ちた消しゴムに鬼が触れると設置場所へ戻る）
  if (!er.carried && er.cool <= 0 && Math.hypot(er.x - er.home.x, er.y - er.home.y) > 10) {
    for (const o of g.ents) {
      if (o.role === 'oni' && o.stun <= 0 && Math.hypot(o.x - er.x, o.y - er.y) < ONI_R + 22) {
        resetEraser(g, '👹 鬼が消しゴムを奪還した！'); break;
      }
    }
  }
  // 脱出：自分がスポーンしたエレベーターだけ
  for (const r of runnersAlive) {
    if (!r.hasEraser || !el.open || el.door <= DOOR_PASS) continue;
    const c = elevCenter(r.side);
    if (Math.abs(r.x - c.x) < T / 2 && Math.abs(r.y - c.y) < T / 2) { g.status = 'runwin'; g.slide = el.left; return; }
  }
  // 捕獲
  for (const o of g.ents) {
    if (o.role !== 'oni' || o.stun > 0) continue;
    for (const r of runnersAlive) {
      if (!r.alive || r.invuln > 0) continue;
      if (Math.hypot(r.x - o.x, r.y - o.y) < RUNNER_R + ONI_R - 4) {
        if (r.hasEraser) {
          dropEraser(g, r); r.invuln = INVULN; o.stun = STUN;
          ev(g, '💥 ' + r.name + ' が捕まり消しゴムを落とした！');
        } else { r.alive = false; ev(g, '☠ ' + r.name + ' が捕まった'); }
        break;
      }
    }
  }
  if (!g.ents.some((e) => e.role === 'runner' && e.alive)) g.status = 'oniwin';
}

// ================= 受信者ごとの状態（見えない情報は送らない）=================
function snapshot(g, r) {
  let ref = r;
  if (r.role === 'runner' && !r.alive) ref = g.ents.find((e) => e.role === 'runner' && e.alive) || r;
  const ghost = r.role === 'oni' ? CFG.ghostR.oni : CFG.ghostR.runner;
  const ents = [];
  for (const e of g.ents) {
    if (e === r) continue;
    const info = { id: e.id, n: e.name, x: e.x, y: e.y, role: e.role, al: e.alive, e: e.hasEraser, st: e.stun > 0, inv: e.invuln > 0, sd: e.side };
    if (e.role === r.role) ents.push(info);
    else if (e.alive && Math.hypot(e.x - ref.x, e.y - ref.y) < ghost && losClear(g, ref.x, ref.y, e.x, e.y)) ents.push(info);
  }
  const E = g.eraser;
  let er = null, hint = null;
  if (E.placed) {
    if (r.role === 'oni') er = E.carried ? { c: true } : { x: E.x, y: E.y, c: false };
    else if (E.carried) er = { c: true, x: E.x, y: E.y };
    else if (Math.hypot(E.x - ref.x, E.y - ref.y) < ghost && losClear(g, ref.x, ref.y, E.x, E.y)) er = { x: E.x, y: E.y, c: false };
    if (r.role === 'runner' && !E.carried && g.playT > HINT_AFTER) hint = { x: E.x + g.hintOff.x, y: E.y + g.hintOff.y, r: 260 };
  }
  let ping = null;
  if (r.role === 'oni' && g.phase === 'play' && g.pingClock % 7 < 1.5) {
    const c = g.ents.find((e) => e.hasEraser);
    if (c) ping = { x: c.x, y: c.y };
  }
  return {
    s: g.status, ph: g.phase, pl: Math.max(0, g.placeLeft), placed: E.placed,
    t: g.time, slide: g.slide || 0, role: r.role, side: ref.side,
    me: { x: r.x, y: r.y, al: r.alive, e: r.hasEraser, inv: r.invuln > 0, st: r.stun > 0 },
    cam: { x: ref.x, y: ref.y }, ents, ping, er, hint,
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
    if (prev !== g.status) g.endAt = Date.now() + 8000;
    for (const e of g.ents) {
      if (e.cpu) continue;
      const s = io.sockets.sockets.get(e.id);
      if (!s) continue;
      const snap = snapshot(g, e);
      if (changed) s.emit('state', snap); else s.volatile.emit('state', snap);
    }
    if (g.status !== 'playing' && Date.now() > g.endAt) toLobby(room);
  }
}, 1000 / 60);

// ================= Socket.io =================
io.on('connection', (socket) => {
  socket.on('create', (d) => {
    leaveRoom(socket.id);
    const room = makeRoom(socket);
    if (!room) return;
    addPlayer(room, socket, d && d.name, 'auto');
    sendLobby(room);
  });
  socket.on('solo', (d) => {                       // CPUと戦う：1人で即スタート（鬼はCPU）
    leaveRoom(socket.id);
    const room = makeRoom(socket);
    if (!room) return;
    addPlayer(room, socket, d && d.name, 'runner');
    startGame(room);
  });
  socket.on('join', (d) => {
    const code = String((d && d.code) || '').replace(/\D/g, '').slice(0, 5);
    if (code.length !== 5) { socket.emit('errmsg', '5桁のルームコードを入力してください'); return; }
    const room = rooms.get(code);
    if (!room) { socket.emit('errmsg', 'そのルームは見つかりません'); return; }
    if (room.players.size >= MAX_PLAYERS && !room.players.has(socket.id)) { socket.emit('errmsg', 'ルームが満員です'); return; }
    leaveRoom(socket.id);
    addPlayer(room, socket, d && d.name, 'auto');
    sendLobby(room);
  });
  socket.on('setRole', (role) => {
    const room = sockRoom.get(socket.id);
    if (!room || room.state !== 'lobby' || !['auto', 'runner', 'oni'].includes(role)) return;
    room.players.get(socket.id).role = role;
    sendLobby(room);
  });
  socket.on('start', () => {
    const room = sockRoom.get(socket.id);
    if (!room || room.host !== socket.id || room.state !== 'lobby') return;
    startGame(room);
  });
  socket.on('input', (inp) => {
    const room = sockRoom.get(socket.id);
    if (!room || !room.game || !inp) return;
    const e = room.game.ents.find((x) => x.id === socket.id);
    if (e) e.input = { u: inp.u ? 1 : 0, d: inp.d ? 1 : 0, l: inp.l ? 1 : 0, r: inp.r ? 1 : 0 };
  });
  socket.on('place', () => {                       // 鬼が消しゴムを設置
    const room = sockRoom.get(socket.id);
    const g = room && room.game;
    if (!g || g.phase !== 'place' || g.eraser.placed) return;
    const o = g.ents.find((e) => e.id === socket.id && e.role === 'oni');
    if (!o) return;
    if (validSpot(g, o.x, o.y)) placeEraser(g, o.x, o.y);
    else socket.emit('ev', '❌ ここには置けない（エレベーターに近すぎる）');
  });
  socket.on('leave', () => leaveRoom(socket.id));
  socket.on('disconnect', () => leaveRoom(socket.id));
});

const PORT = process.env.PORT || 3000;
server.listen(PORT, () => console.log('Server listening on ' + PORT));
