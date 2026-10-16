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
const N = 19;                    // タイル数（奇数）→ 小型マップ
const T = 80;                    // 1タイル(px)
const MAP = N * T;               // 1520 x 1520
const MID = (N - 1) / 2;         // 中央列(=奇数なのでセル列)
const ELEV = { tx: MID, ty: N - 1 };
const CFG = {
  zoom: 1.9,
  lightR: { runner: 230, oni: 270 },   // 自分を照らす範囲
  seeR: { runner: 235, oni: 300 }      // 敵が見える範囲（かつ視線が通る場合のみ）
};
const RUNNER_R = 18, ONI_R = 22;
const SPEED = { runner: 236, carrier: 214, oni: 230, cpu: 204, cpuAngry: 224 };
const ELEV_OPEN_SEC = 20;        // 消しゴム取得後に開く時間
const CLOSE_PHASE = 8;           // 残りこの秒数からドアが閉まり始める
const DOOR_PASS = 0.15;          // これ以上開いていれば滑り込める
const INVULN = 3, STUN = 2, START_STUN = 3, MATCH_TIME = 300;
const MAX_PLAYERS = 8;

// ================= 迷路生成（毎回ランダム・必ず全通路が連結）=================
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
  // 周回路を少し作る（鬼ごっこが行き止まりで詰まらないように）
  for (let k = 0; k < 14; k++) {
    const x = 1 + Math.floor(Math.random() * (N - 2));
    const y = 1 + Math.floor(Math.random() * (N - 2));
    if ((x + y) % 2 === 1) g[y][x] = 0;
  }
  g[ELEV.ty][ELEV.tx] = 0; // エレベーター（扉が閉じている間は別途ソリッド）
  return g;
}

// ================= 衝突 =================
function isSolid(g, tx, ty, oni) {
  if (tx < 0 || ty < 0 || tx >= N || ty >= N) return true;
  if (g.grid[ty][tx] === 1) return true;
  if (tx === ELEV.tx && ty === ELEV.ty) return oni || g.elev.door <= DOOR_PASS;
  return false;
}
function collides(g, x, y, r, oni) {
  const x0 = Math.floor((x - r) / T), x1 = Math.floor((x + r) / T);
  const y0 = Math.floor((y - r) / T), y1 = Math.floor((y + r) / T);
  for (let ty = y0; ty <= y1; ty++) for (let tx = x0; tx <= x1; tx++) {
    if (!isSolid(g, tx, ty, oni)) continue;
    const cx = Math.max(tx * T, Math.min(x, tx * T + T));
    const cy = Math.max(ty * T, Math.min(y, ty * T + T));
    const dx = x - cx, dy = y - cy;
    if (dx * dx + dy * dy < r * r) return true;
  }
  return false;
}
function moveEnt(g, e, dx, dy) {
  const r = e.role === 'oni' ? ONI_R : RUNNER_R, oni = e.role === 'oni';
  if (dx !== 0 && !collides(g, e.x + dx, e.y, r, oni)) e.x += dx;
  if (dy !== 0 && !collides(g, e.x, e.y + dy, r, oni)) e.y += dy;
}
function losClear(g, x0, y0, x1, y1) {
  const n = Math.ceil(Math.hypot(x1 - x0, y1 - y0) / 12);
  for (let i = 1; i < n; i++) {
    const t = i / n;
    if (isSolid(g, Math.floor((x0 + (x1 - x0) * t) / T), Math.floor((y0 + (y1 - y0) * t) / T), false)) return false;
  }
  return true;
}

// BFS（CPU鬼用）
const bfsParent = new Int16Array(N * N), bfsQueue = new Int16Array(N * N);
function nextTileToward(g, fx, fy, tx, ty) {
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
      if (isSolid(g, nx, ny, true)) continue;
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

// ================= ルーム管理 =================
const rooms = new Map();      // code -> room
const sockRoom = new Map();   // socket.id -> room
function shuffle(a) { for (let i = a.length - 1; i > 0; i--) { const j = Math.floor(Math.random() * (i + 1)); [a[i], a[j]] = [a[j], a[i]]; } return a; }

function sendLobby(room) {
  const players = [...room.players.values()].map((p) => ({ id: p.id, name: p.name, role: p.role }));
  for (const id of room.players.keys()) io.to(id).emit('lobby', { code: room.code, state: room.state, host: room.host, players, you: id });
}
function toLobby(room) {
  room.state = 'lobby'; room.game = null;
  sendLobby(room);
}
function leaveRoom(socketId) {
  const room = sockRoom.get(socketId);
  if (!room) return;
  sockRoom.delete(socketId);
  room.players.delete(socketId);
  if (room.game) {
    const g = room.game;
    const ent = g.ents.find((e) => e.id === socketId);
    if (ent) {
      if (ent.hasEraser) dropEraser(g, ent);
      g.ents = g.ents.filter((e) => e !== ent);
    }
  }
  if (room.players.size === 0) { rooms.delete(room.code); return; }
  if (room.host === socketId) room.host = room.players.keys().next().value;
  sendLobby(room);
}

// ================= ゲーム開始 =================
function startGame(room) {
  const list = [...room.players.values()];
  // 役割の確定
  const target = list.length >= 2 ? Math.max(1, Math.floor(list.length / 3)) : 0;
  let oniCount = list.filter((p) => p.role === 'oni').length;
  for (const p of list) p.assigned = p.role;
  for (const p of shuffle(list.filter((p) => p.role === 'auto'))) {
    if (oniCount < target) { p.assigned = 'oni'; oniCount++; } else p.assigned = 'runner';
  }
  if (!list.some((p) => p.assigned === 'runner')) shuffle(list.filter((p) => p.assigned === 'oni'))[0].assigned = 'runner';

  const g = {
    room, grid: generateMaze(), status: 'playing', time: MATCH_TIME, endAt: 0, pingClock: 0, ents: [],
    eraser: { x: MID * T + T / 2, y: 1 * T + T / 2, carried: false, cool: 0 },
    elev: { open: false, left: 0, door: 0 }
  };
  const rx = [9, 7, 11, 5, 13, 3, 15, 1, 17], ox = [9, 5, 13, 3, 15, 7, 11, 1];
  let ri = 0, oi = 0;
  const mk = (id, name, role, cpu) => {
    const cx = role === 'runner' ? rx[ri++ % rx.length] : ox[oi++ % ox.length];
    const cy = role === 'runner' ? N - 2 : 5;
    g.ents.push({
      id, name, role, cpu, x: cx * T + T / 2, y: cy * T + T / 2, input: { u: 0, d: 0, l: 0, r: 0 },
      alive: true, hasEraser: false, invuln: 0, stun: role === 'oni' ? START_STUN : 0, next: null, repath: 0
    });
  };
  for (const p of list) mk(p.id, p.name, p.assigned, false);
  if (!g.ents.some((e) => e.role === 'oni')) mk('cpu1', 'CPU鬼', 'oni', true);
  room.game = g; room.state = 'playing';
  for (const e of g.ents) if (!e.cpu) {
    io.to(e.id).emit('init', { grid: g.grid.map((r) => r.join('')), T, N, map: MAP, elev: ELEV, cfg: CFG, role: e.role, name: e.name, matchTime: MATCH_TIME });
  }
  sendLobby(room);
}

// ================= ゲームロジック =================
function ev(g, msg) { for (const e of g.ents) if (!e.cpu) io.to(e.id).emit('ev', msg); }

function dropEraser(g, holder) {
  const er = g.eraser;
  holder.hasEraser = false;
  er.carried = false; er.x = holder.x; er.y = holder.y; er.cool = 2.5;
}
function resetEraser(g, msg) {
  const er = g.eraser;
  for (const e of g.ents) e.hasEraser = false;
  er.x = MID * T + T / 2; er.y = T + T / 2; er.carried = false; er.cool = 3;
  g.elev.open = false; g.elev.left = 0;
  ev(g, msg);
}

function updateElevator(g, dt) {
  const el = g.elev;
  if (el.open) {
    el.left -= dt;
    if (el.left <= 0) { el.left = 0; resetEraser(g, '⏰ エレベーターが閉まった！消しゴムは最奥に戻された'); }
  }
  const target = el.open ? Math.min(1, el.left / CLOSE_PHASE) : 0;
  if (target > el.door) el.door = Math.min(target, el.door + dt * 1.2);
  else el.door = Math.max(target, el.door - dt * (el.open ? 2 : 3));
}

function step(g, dt) {
  if (g.status !== 'playing') return;
  g.time -= dt;
  if (g.time <= 0) { g.status = 'timeup'; return; }
  g.pingClock += dt;
  const er = g.eraser, el = g.elev;
  if (er.cool > 0) er.cool -= dt;
  updateElevator(g, dt);

  const runnersAlive = g.ents.filter((e) => e.role === 'runner' && e.alive);
  const carrier = g.ents.find((e) => e.hasEraser);

  for (const e of g.ents) {
    if (e.invuln > 0) e.invuln -= dt;
    if (e.stun > 0) e.stun -= dt;
    if (!e.alive) continue;

    if (!e.cpu) {
      if (e.role === 'oni' && e.stun > 0) continue;
      const ix = e.input.r - e.input.l, iy = e.input.d - e.input.u;
      if (ix || iy) {
        const len = Math.hypot(ix, iy);
        const sp = e.role === 'oni' ? SPEED.oni : (e.hasEraser ? SPEED.carrier : SPEED.runner);
        moveEnt(g, e, (ix / len) * sp * dt, (iy / len) * sp * dt);
      }
    } else if (e.stun <= 0 && runnersAlive.length) {
      // CPU鬼：消しゴム所持者優先、なければ最寄りの逃げ側
      let tgt = carrier && carrier.role === 'runner' ? carrier : null;
      if (!tgt) {
        let best = 1e9;
        for (const r of runnersAlive) { const d = Math.hypot(r.x - e.x, r.y - e.y); if (d < best) { best = d; tgt = r; } }
      }
      e.repath -= dt;
      const otx = Math.floor(e.x / T), oty = Math.floor(e.y / T), ptx = Math.floor(tgt.x / T), pty = Math.floor(tgt.y / T);
      if (e.repath <= 0) { e.next = nextTileToward(g, otx, oty, ptx, pty); e.repath = 0.1; }
      let tx = tgt.x, ty = tgt.y;
      if (e.next && !(otx === ptx && oty === pty)) { tx = e.next.tx * T + T / 2; ty = e.next.ty * T + T / 2; }
      const dx = tx - e.x, dy = ty - e.y, d = Math.hypot(dx, dy);
      if (d > 0.5) {
        const m = Math.min((carrier ? SPEED.cpuAngry : SPEED.cpu) * dt, d);
        moveEnt(g, e, (dx / d) * m, (dy / d) * m);
      }
    }
  }

  // 消しゴム所持中は追従
  if (carrier) { er.x = carrier.x; er.y = carrier.y; }

  // 取得（逃げ側）
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
  // 奪還（鬼側）：落ちている消しゴムに触れると最奥へ戻る
  if (!er.carried && er.cool <= 0) {
    const sx = MID * T + T / 2, sy = T + T / 2;
    if (Math.hypot(er.x - sx, er.y - sy) > 10) {
      for (const o of g.ents) {
        if (o.role === 'oni' && o.stun <= 0 && Math.hypot(o.x - er.x, o.y - er.y) < ONI_R + 22) {
          resetEraser(g, '👹 鬼が消しゴムを奪還した！');
          break;
        }
      }
    }
  }

  // 脱出
  const ex = ELEV.tx * T + T / 2, ey = ELEV.ty * T + T / 2;
  for (const r of runnersAlive) {
    if (r.hasEraser && el.open && el.door > DOOR_PASS && Math.abs(r.x - ex) < T / 2 && Math.abs(r.y - ey) < T / 2) {
      g.status = 'runwin'; g.slide = el.left; return;
    }
  }

  // 捕獲
  for (const o of g.ents) {
    if (o.role !== 'oni' || o.stun > 0) continue;
    for (const r of runnersAlive) {
      if (!r.alive || r.invuln > 0) continue;
      if (Math.hypot(r.x - o.x, r.y - o.y) < RUNNER_R + ONI_R - 4) {
        if (r.hasEraser) {
          dropEraser(g, r);
          r.invuln = INVULN; o.stun = STUN;
          ev(g, '💥 ' + r.name + ' が捕まり消しゴムを落とした！');
        } else {
          r.alive = false;
          ev(g, '☠ ' + r.name + ' が捕まった');
        }
        break;
      }
    }
  }
  if (!g.ents.some((e) => e.role === 'runner' && e.alive)) g.status = 'oniwin';
}

// ================= 受信者ごとの状態（見えない敵は送らない）=================
function snapshot(g, r) {
  let ref = r;
  if (r.role === 'runner' && !r.alive) ref = g.ents.find((e) => e.role === 'runner' && e.alive) || r;
  const see = r.role === 'oni' ? CFG.seeR.oni : CFG.seeR.runner;
  const ents = [];
  for (const e of g.ents) {
    if (e === r) continue;
    const info = { id: e.id, n: e.name, x: e.x, y: e.y, role: e.role, al: e.alive, e: e.hasEraser, st: e.stun > 0, inv: e.invuln > 0 };
    if (e.role === r.role) ents.push(info);
    else if (e.alive && Math.hypot(e.x - ref.x, e.y - ref.y) < see && losClear(g, ref.x, ref.y, e.x, e.y)) ents.push(info);
  }
  let ping = null;
  if (r.role === 'oni' && g.pingClock % 7 < 1.5) {
    const c = g.ents.find((e) => e.hasEraser);
    if (c) ping = { x: c.x, y: c.y };
  }
  return {
    s: g.status, t: g.time, slide: g.slide || 0, role: r.role,
    me: { x: r.x, y: r.y, al: r.alive, e: r.hasEraser, inv: r.invuln > 0, st: r.stun > 0 },
    cam: { x: ref.x, y: ref.y }, ents, ping,
    er: { x: g.eraser.x, y: g.eraser.y, c: g.eraser.carried },
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
    const prev = g.status;
    step(g, dt);
    const changed = prev !== g.status;
    if (changed) g.endAt = Date.now() + 8000;
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
  socket.on('join', (d) => {
    d = d || {};
    leaveRoom(socket.id);
    const name = String(d.name || '').trim().slice(0, 12) || 'プレイヤー';
    const code = String(d.room || '').trim().toUpperCase().replace(/[^A-Z0-9_\-ぁ-んァ-ヶ一-龠]/g, '').slice(0, 10) || 'PUBLIC';
    let room = rooms.get(code);
    if (!room) { room = { code, players: new Map(), host: socket.id, state: 'lobby', game: null }; rooms.set(code, room); }
    if (room.players.size >= MAX_PLAYERS) { socket.emit('errmsg', 'ルームが満員です'); return; }
    const role = ['auto', 'runner', 'oni'].includes(d.role) ? d.role : 'auto';
    room.players.set(socket.id, { id: socket.id, name, role });
    sockRoom.set(socket.id, room);
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
  socket.on('leave', () => leaveRoom(socket.id));
  socket.on('disconnect', () => leaveRoom(socket.id));
});

const PORT = process.env.PORT || 3000;
server.listen(PORT, () => console.log('Server listening on ' + PORT));
