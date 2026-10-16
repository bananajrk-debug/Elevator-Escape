'use strict';
const express = require('express');
const http = require('http');
const path = require('path');
const { Server } = require('socket.io');

const app = express();
const server = http.createServer(app);
const io = new Server(server);
app.use(express.static(path.join(__dirname, 'public')));

// ===== 定数 =====
const MAP = 2000;
const N = 25;                 // タイル数（奇数）
const T = MAP / N;            // 1タイル = 80px
const PLAYER_R = 20;
const ONI_R = 24;
const PLAYER_SPEED = 240;
const ONI_SPEED = 200;
const ONI_SPEED_ANGRY = 222;  // 消しゴム奪取後
const ELEVATOR_OPEN_SEC = 20;
const INVULN_SEC = 3;
const ONI_STUN_SEC = 2;
const MID = (N - 1) / 2;      // 中央タイル列 = 12
const ELEV = { tx: MID, ty: N - 1 };

// ===== 迷路生成（タイル方式：壁と通路が同一グリッドなので判定が完全一致）=====
function mulberry32(a) {
  return function () {
    a |= 0; a = (a + 0x6d2b79f5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

function generateMaze(seed) {
  const rnd = mulberry32(seed);
  const g = [];
  for (let y = 0; y < N; y++) g.push(new Array(N).fill(1));
  // 再帰バックトラッカー（反復版）
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
    const [dx, dy] = opts[Math.floor(rnd() * opts.length)];
    g[cy + dy / 2][cx + dx / 2] = 0;
    g[cy + dy][cx + dx] = 0;
    stack.push([cx + dx, cy + dy]);
  }
  // 行き止まりだらけで詰まないよう、少しだけ壁を抜いて周回路を作る
  for (let k = 0; k < 24; k++) {
    const x = 1 + Math.floor(rnd() * (N - 2));
    const y = 1 + Math.floor(rnd() * (N - 2));
    if ((x + y) % 2 === 1) g[y][x] = 0;
  }
  // 最奥中央（消しゴム）と最下部中央（エレベーター）への口を確保
  g[1][MID] = 0;
  g[N - 2][MID] = 0;
  g[ELEV.ty][ELEV.tx] = 0; // エレベーター（閉鎖時は別途ソリッド扱い）
  return g;
}

// ===== ゲーム =====
const games = new Map(); // socket.id -> game

function newGame(id, name) {
  const grid = generateMaze((Math.random() * 2 ** 31) | 0);
  return {
    id,
    grid,
    status: 'playing',
    p: {
      name,
      x: MID * T + T / 2, y: (N - 2) * T + T / 2,
      input: { u: 0, d: 0, l: 0, r: 0 },
      hasEraser: false, invuln: 0
    },
    oni: { x: 11 * T + T / 2, y: 9 * T + T / 2, stun: 1.5, next: null, repath: 0 },
    eraser: { x: MID * T + T / 2, y: 1 * T + T / 2, carried: false, cool: 0 },
    elev: { open: false, left: 0 }
  };
}

function isSolid(g, tx, ty) {
  if (tx < 0 || ty < 0 || tx >= N || ty >= N) return true;
  if (g.grid[ty][tx] === 1) return true;
  if (tx === ELEV.tx && ty === ELEV.ty && !g.elev.open) return true;
  return false;
}

function collides(g, x, y, r) {
  const x0 = Math.floor((x - r) / T), x1 = Math.floor((x + r) / T);
  const y0 = Math.floor((y - r) / T), y1 = Math.floor((y + r) / T);
  for (let ty = y0; ty <= y1; ty++) {
    for (let tx = x0; tx <= x1; tx++) {
      if (!isSolid(g, tx, ty)) continue;
      const cx = Math.max(tx * T, Math.min(x, tx * T + T));
      const cy = Math.max(ty * T, Math.min(y, ty * T + T));
      const dx = x - cx, dy = y - cy;
      if (dx * dx + dy * dy < r * r) return true;
    }
  }
  return false;
}

function moveEntity(g, e, dx, dy, r) {
  if (dx !== 0 && !collides(g, e.x + dx, e.y, r)) e.x += dx;
  if (dy !== 0 && !collides(g, e.x, e.y + dy, r)) e.y += dy;
}

// BFS：from -> to の最初の一歩（タイル座標）を返す
const bfsParent = new Int16Array(N * N);
const bfsQueue = new Int16Array(N * N);
function nextTileToward(g, fx, fy, tx, ty) {
  if (fx === tx && fy === ty) return null;
  bfsParent.fill(-2);
  const start = fy * N + fx, goal = ty * N + tx;
  let head = 0, tail = 0;
  bfsQueue[tail++] = start;
  bfsParent[start] = -1;
  while (head < tail) {
    const cur = bfsQueue[head++];
    if (cur === goal) break;
    const cx = cur % N, cy = (cur / N) | 0;
    for (const [dx, dy] of [[1, 0], [-1, 0], [0, 1], [0, -1]]) {
      const nx = cx + dx, ny = cy + dy;
      if (isSolid(g, nx, ny)) continue;
      const ni = ny * N + nx;
      if (bfsParent[ni] !== -2) continue;
      bfsParent[ni] = cur;
      bfsQueue[tail++] = ni;
    }
  }
  if (bfsParent[goal] === -2) return null;
  let cur = goal;
  while (bfsParent[cur] !== start) cur = bfsParent[cur];
  return { tx: cur % N, ty: (cur / N) | 0 };
}

function step(g, dt) {
  if (g.status !== 'playing') return;
  const p = g.p, o = g.oni, er = g.eraser, el = g.elev;

  // --- プレイヤー移動 ---
  let ix = p.input.r - p.input.l, iy = p.input.d - p.input.u;
  if (ix || iy) {
    const len = Math.hypot(ix, iy);
    moveEntity(g, p, (ix / len) * PLAYER_SPEED * dt, (iy / len) * PLAYER_SPEED * dt, PLAYER_R);
  }
  if (p.invuln > 0) p.invuln -= dt;
  if (er.cool > 0) er.cool -= dt;

  // --- 消しゴム取得 ---
  if (!er.carried && er.cool <= 0 && Math.hypot(p.x - er.x, p.y - er.y) < PLAYER_R + 22) {
    er.carried = true;
    p.hasEraser = true;
    el.open = true;
    el.left = ELEVATOR_OPEN_SEC;
  }
  if (er.carried) { er.x = p.x; er.y = p.y; }

  // --- エレベータータイマー ---
  if (el.open) {
    el.left -= dt;
    if (el.left <= 0) { el.open = false; el.left = 0; }
  }

  // --- 脱出判定 ---
  if (p.hasEraser && el.open) {
    const ex = ELEV.tx * T + T / 2, ey = ELEV.ty * T + T / 2;
    if (Math.abs(p.x - ex) < T / 2 && Math.abs(p.y - ey) < T / 2) {
      g.status = 'won';
      return;
    }
  }

  // --- 鬼AI ---
  if (o.stun > 0) {
    o.stun -= dt;
  } else {
    o.repath -= dt;
    const otx = Math.floor(o.x / T), oty = Math.floor(o.y / T);
    const ptx = Math.floor(p.x / T), pty = Math.floor(p.y / T);
    if (o.repath <= 0) {
      o.next = nextTileToward(g, otx, oty, ptx, pty);
      o.repath = 0.1;
    }
    let tx = p.x, ty = p.y;
    if (o.next && !(otx === ptx && oty === pty)) {
      tx = o.next.tx * T + T / 2;
      ty = o.next.ty * T + T / 2;
    }
    const dx = tx - o.x, dy = ty - o.y, d = Math.hypot(dx, dy);
    if (d > 0.5) {
      const sp = (p.hasEraser || er.carried ? ONI_SPEED_ANGRY : ONI_SPEED) * dt;
      const m = Math.min(sp, d);
      moveEntity(g, o, (dx / d) * m, (dy / d) * m, ONI_R);
    }
  }

  // --- 捕獲判定 ---
  if (o.stun <= 0 && p.invuln <= 0 && Math.hypot(p.x - o.x, p.y - o.y) < PLAYER_R + ONI_R - 4) {
    if (p.hasEraser) {
      p.hasEraser = false;
      er.carried = false;
      er.x = p.x; er.y = p.y;
      er.cool = 2.5;
      p.invuln = INVULN_SEC;
      o.stun = ONI_STUN_SEC;
    } else {
      g.status = 'lost';
    }
  }
}

function snapshot(g) {
  const p = g.p, o = g.oni;
  const near = Math.hypot(p.x - o.x, p.y - o.y) < 650; // 遠い鬼は送らない（チート対策）
  return {
    s: g.status,
    p: { x: p.x, y: p.y, e: p.hasEraser, inv: p.invuln > 0 },
    o: near ? { x: o.x, y: o.y, st: o.stun > 0 } : null,
    er: { x: g.eraser.x, y: g.eraser.y, c: g.eraser.carried },
    el: { open: g.elev.open, left: g.elev.left }
  };
}

// ===== 60fps ループ =====
let last = process.hrtime.bigint();
setInterval(() => {
  const now = process.hrtime.bigint();
  const dt = Math.min(Number(now - last) / 1e9, 0.05);
  last = now;
  for (const g of games.values()) {
    const prev = g.status;
    step(g, dt);
    const sock = io.sockets.sockets.get(g.id);
    if (sock) sock.volatile.emit('state', snapshot(g));
    if (prev !== g.status && sock) sock.emit('state', snapshot(g)); // 終了通知は確実に送る
  }
}, 1000 / 60);

// ===== Socket.io =====
io.on('connection', (socket) => {
  socket.on('join', (data) => {
    let name = String((data && data.name) || '').trim().slice(0, 12) || 'プレイヤー';
    const g = newGame(socket.id, name);
    games.set(socket.id, g);
    socket.emit('init', { grid: g.grid.map((r) => r.join('')), T, N, map: MAP, elev: ELEV, name });
  });
  socket.on('input', (inp) => {
    const g = games.get(socket.id);
    if (!g || !inp) return;
    g.p.input = { u: inp.u ? 1 : 0, d: inp.d ? 1 : 0, l: inp.l ? 1 : 0, r: inp.r ? 1 : 0 };
  });
  socket.on('disconnect', () => games.delete(socket.id));
});

const PORT = process.env.PORT || 3000;
server.listen(PORT, () => console.log('Server listening on ' + PORT));
