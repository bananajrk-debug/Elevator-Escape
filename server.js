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
// エレベーター：0=上 1=右 2=下 3=左。dx,dy は迷路内側への向き
const ELEVS = [
  { tx: MID, ty: 0, dx: 0, dy: 1 },
  { tx: N - 1, ty: MID, dx: -1, dy: 0 },
  { tx: MID, ty: N - 1, dx: 0, dy: -1 },
  { tx: 0, ty: MID, dx: 1, dy: 0 }
];
const CFG = { zoom: 1.9, lightR: { runner: 230, oni: 270 }, ghostR: { runner: 320, oni: 370 } };
const RUNNER_R = 18, ONI_R = 22;
const SPEED = { runner: 236, carrier: 214, oni: 230, cpu: 204, cpuAngry: 224 };
const RUSH_MUL = 1.5;                                   // エレベーター突入時の鬼の加速
const ELEV_OPEN_SEC = 20, CLOSE_PHASE = 8, DOOR_PASS = 0.15;
const BOARD_TIME = 4, BOARD_CATCH = 110;                // 突入後に扉が閉まるまで／鬼がここまで来たら阻止
const MAX_HP = 100, HIT_DMG = 50, HEAL = 50;
const INVULN = 3, START_STUN = 2, ONI_RESPAWN = 5, MATCH_TIME = 300;
const PLACE_TIME = 30, PLACE_MIN = 300, HINT_AFTER = 45;
const WARP_CD = 5, WARP_R = 28;
const BOOST_SEC = 10, BOOST_MUL = 1.4, INVIS_SEC = 10;
const GRENADE_STUN = 8, GRENADE_R = 240;                // 自動スタン：半径3ブロック・8秒
const CHEST_RESPAWN = 45, POTION_RESPAWN = 40, POTION_COUNT = 3;
const ONI_TP_CD = 30;
const SKIN_COUNT = 8, RESULT_WAIT = 15000, MAX_PLAYERS = 8;
const ITEMS = ['stun', 'boots', 'invis'];
const ITEM_NAME = { stun: 'スタングレネード', boots: 'スピードブーツ', invis: '透明化' };

const cleanSkin = (v) => { v = parseInt(v, 10); return v >= 0 && v < SKIN_COUNT ? v : 0; };
const elevIndexAt = (tx, ty) => { for (let i = 0; i < 4; i++) if (ELEVS[i].tx === tx && ELEVS[i].ty === ty) return i; return -1; };
const elevCenter = (i) => ({ x: ELEVS[i].tx * T + T / 2, y: ELEVS[i].ty * T + T / 2 });
const elevFront = (i) => ({ x: (ELEVS[i].tx + ELEVS[i].dx) * T + T / 2, y: (ELEVS[i].ty + ELEVS[i].dy) * T + T / 2 });
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
  for (let k = 0; k < 14; k++) {
    const x = 1 + Math.floor(Math.random() * (N - 2));
    const y = 1 + Math.floor(Math.random() * (N - 2));
    if ((x + y) % 2 === 1) g[y][x] = 0;
  }
  for (const E of ELEVS) g[E.ty][E.tx] = 0;
  return g;
}

// ================= 衝突 =================
// 逃げ側は「消しゴムを持って」「自分のエレベーター」の「扉が開いている」ときだけ入れる
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
  const players = [...room.players.values()].map((p) => ({ id: p.id, name: p.name, role: p.role, skin: p.skin }));
  for (const id of room.players.keys()) io.to(id).emit('lobby', { code: room.code, state: room.state, host: room.host, players, you: id });
}
function toLobby(room) { room.state = 'lobby'; room.game = null; sendLobby(room); }
function makeRoom(socket, solo) {
  const code = newCode();
  if (!code) { socket.emit('errmsg', 'ルームを作れませんでした'); return null; }
  const room = { code, players: new Map(), host: socket.id, state: 'lobby', game: null, solo: !!solo };
  rooms.set(code, room);
  return room;
}
function addPlayer(room, socket, name, role, skin) {
  room.players.set(socket.id, { id: socket.id, name: cleanName(name), role, skin: cleanSkin(skin) });
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

// ================= ゲーム開始 =================
function addEnt(g, id, name, role, cpu, side, skin) {
  const E = ELEVS[side];
  const k = g.ents.filter((e) => e.side === side).length;
  const off = [0, 16, -16][k % 3];
  const px = E.dy !== 0 ? 1 : 0, py = E.dx !== 0 ? 1 : 0;
  const x = (E.tx + E.dx) * T + T / 2 + px * off, y = (E.ty + E.dy) * T + T / 2 + py * off;
  g.ents.push({
    id, name, role, cpu, side, skin: skin || 0, x, y, spawn: { x, y },
    input: { u: 0, d: 0, l: 0, r: 0 }, alive: true, hp: MAX_HP, hasEraser: false, board: false,
    invuln: 0, stun: 0, resp: false, tpCd: ONI_TP_CD, item: null, boost: 0, invis: 0, wcd: 0, armed: true, msgCd: 0,
    next: null, repath: 0
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
    time: MATCH_TIME, playT: 0, endAt: 0, pingClock: 0, ents: [], board: null, slide: 0,
    hintOff: { x: Math.cos(ang) * mag, y: Math.sin(ang) * mag },
    eraser: { x: 0, y: 0, home: { x: 0, y: 0 }, placed: false, carried: false, cool: 0 },
    elev: { open: false, left: 0, door: 0 }
  };
  setupSpots(g);
  const sides = shuffle([0, 1, 2, 3]);
  let si = 0;
  for (const p of list) if (p.assigned === 'runner') addEnt(g, p.id, p.name, 'runner', false, sides[si++ % 4], p.skin);
  for (const p of list) if (p.assigned === 'oni') addEnt(g, p.id, p.name, 'oni', false, sides[si++ % 4], p.skin);
  if (!g.ents.some((e) => e.role === 'oni')) addEnt(g, 'cpu1', 'CPU鬼', 'oni', true, sides[si++ % 4], 0);

  room.game = g; room.state = 'playing';
  for (const e of g.ents) if (!e.cpu) {
    io.to(e.id).emit('init', {
      grid: g.grid.map((r) => r.join('')), T, N, map: MAP, elevs: ELEVS, cfg: CFG, role: e.role, side: e.side, name: e.name,
      skin: e.skin, matchTime: MATCH_TIME, placeTime: PLACE_TIME, warpCd: WARP_CD, tpCd: ONI_TP_CD, boardTime: BOARD_TIME, solo: room.solo,
      pads: g.pads, chests: g.chests.map((c) => ({ x: c.x, y: c.y })), potions: g.potions.map((p) => ({ x: p.x, y: p.y }))
    });
  }
  sendLobby(room);
}

// ================= 配置（ワープ・宝箱・回復薬は通路の中央セル）=================
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
  let sp = [];
  for (const mb of [450, 350, 250, 0]) { sp = pickSpots(4, mb, []); if (sp.length === 4) break; }
  const d = (a, b) => Math.hypot(sp[a].x - sp[b].x, sp[a].y - sp[b].y);
  const opts = [[0, 1, 2, 3], [0, 2, 1, 3], [0, 3, 1, 2]];
  opts.sort((p, q) => Math.min(d(q[0], q[1]), d(q[2], q[3])) - Math.min(d(p[0], p[1]), d(p[2], p[3])));
  g.pads = opts[0].map((i, k) => ({ x: sp[i].x, y: sp[i].y, pair: k >> 1 }));
  g.chests = pickSpots(2, 400, g.pads).map((c) => ({ x: c.x, y: c.y, open: false, respawn: 0 }));
  g.potions = pickSpots(POTION_COUNT, 300, g.pads.concat(g.chests)).map((c) => ({ x: c.x, y: c.y, taken: false, respawn: 0 }));
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
  for (const p of g.pads.concat(g.chests, g.potions)) if (Math.hypot(x - p.x, y - p.y) < 70) return false;
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
  if (g.board) return;                                  // 突入演出中は扉と時間を専用処理に任せる
  if (el.open) {
    el.left -= dt;
    if (el.left <= 0) { el.left = 0; resetEraser(g, '⏰ エレベーターが閉まった！消しゴムは設置場所に戻った'); }
  }
  const target = el.open ? Math.min(1, el.left / CLOSE_PHASE) : 0;
  if (target > el.door) el.door = Math.min(target, el.door + dt * 1.2);
  else el.door = Math.max(target, el.door - dt * (el.open ? 2 : 3));
}

// 逃げ側がダメージを受ける（HP50%減。0で脱落）
function hurtRunner(g, r, oni) {
  r.hp = Math.max(0, r.hp - HIT_DMG);
  r.invuln = INVULN;
  if (r.hasEraser) dropEraser(g, r);
  if (oni) { oni.stun = ONI_RESPAWN; oni.resp = true; }
  if (r.hp <= 0) { r.alive = false; ev(g, '☠ ' + r.name + ' が力尽きた'); }
  else ev(g, '💥 ' + r.name + ' がやられた！HP ' + r.hp + '%');
}

function moveByInput(g, e, dt) {
  if (e.board) return;
  const ix = e.input.r - e.input.l, iy = e.input.d - e.input.u;
  if (!ix && !iy) return;
  const len = Math.hypot(ix, iy);
  let sp = e.role === 'oni' ? SPEED.oni * (g.board ? RUSH_MUL : 1) : (e.hasEraser ? SPEED.carrier : SPEED.runner) * (e.boost > 0 ? BOOST_MUL : 1);
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
    const slow = tgt.invis > 0 && Math.hypot(tgt.x - e.x, tgt.y - e.y) > 110 ? 0.6 : 1;
    const m = Math.min((angry ? SPEED.cpuAngry : SPEED.cpu) * slow * (g.board ? RUSH_MUL : 1) * dt, d);
    moveEnt(g, e, (dx / d) * m, (dy / d) * m);
  }
}

function stepPlace(g, dt) {
  g.placeLeft -= dt;
  for (const e of g.ents) if (e.role === 'oni' && !e.cpu) moveByInput(g, e, dt);
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
  for (const e of g.ents) {
    if (e.invuln > 0) e.invuln -= dt;
    if (e.stun > 0) e.stun -= dt; else e.resp = false;
    if (e.boost > 0) e.boost -= dt;
    if (e.invis > 0) e.invis -= dt;
    if (e.wcd > 0) e.wcd -= dt;
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
    if (!e.cpu) {
      if (e.role === 'oni' && e.stun > 0) continue;
      moveByInput(g, e, dt);
    } else if (e.stun <= 0) {
      if (g.board) cpuMove(g, e, dt, elevFront(g.board.side), true);            // 突入を察知して急行
      else if (runnersAlive.length) {
        let tgt = carrier && carrier.role === 'runner' ? carrier : null;
        if (!tgt) {
          let best = 1e9;
          for (const r of runnersAlive) { const d = Math.hypot(r.x - e.x, r.y - e.y); if (d < best) { best = d; tgt = r; } }
        }
        cpuMove(g, e, dt, tgt, !!carrier);
      }
    }
  }
  if (carrier) { er.x = carrier.x; er.y = carrier.y; }

  // 自動スタングレネード：所持中に鬼が240px以内へ来たら発動して8秒停止
  for (const r of runnersAlive) {
    if (r.item !== 'stun' || r.board) continue;
    const near = g.ents.filter((o) => o.role === 'oni' && o.stun <= 0 && Math.hypot(o.x - r.x, o.y - r.y) < GRENADE_R);
    if (!near.length) continue;
    r.item = null;
    for (const o of g.ents) if (o.role === 'oni' && Math.hypot(o.x - r.x, o.y - r.y) < GRENADE_R) { o.stun = Math.max(o.stun, GRENADE_STUN); o.resp = false; }
    fxNear(g, 'stun', r.x, r.y);
    ev(g, '💫 スタングレネード自動発動！鬼が8秒間停止');
  }

  // ワープ
  for (const e of g.ents) {
    if (e.cpu || !e.alive || e.board) continue;
    let on = -1;
    for (let i = 0; i < g.pads.length; i++) if (Math.hypot(e.x - g.pads[i].x, e.y - g.pads[i].y) < WARP_R) on = i;
    if (on < 0) e.armed = true;
    else if (e.armed && e.wcd <= 0) {
      const dst = g.pads[on ^ 1];
      fxNear(g, 'warp', e.x, e.y);
      e.x = dst.x; e.y = dst.y; e.wcd = WARP_CD; e.armed = false;
      fxNear(g, 'warp', e.x, e.y);
    }
  }
  // 宝箱・回復薬の復活、回復薬の拾得（HPが減っているときだけ）
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

  // 消しゴム取得
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
  // 奪還（落ちた消しゴムに鬼が触れると設置場所へ戻る）
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
      if (arrived) {                                       // 扉が閉まる前に鬼が到達 → 阻止される
        const f = elevFront(b.side);
        r.board = false; r.x = f.x; r.y = f.y; g.board = null;
        hurtRunner(g, r, arrived);
        ev(g, '⚠ ドアが閉まる前に鬼が追いついた！');
      } else if (b.left <= 0) {
        let nd = 9999;
        for (const o of g.ents) if (o.role === 'oni') nd = Math.min(nd, Math.hypot(o.x - c.x, o.y - c.y));
        g.status = 'runwin'; g.slide = nd; return;
      }
    }
  }

  // 接触ダメージ（無敵中・突入中は除く）
  for (const o of g.ents) {
    if (o.role !== 'oni' || o.stun > 0) continue;
    for (const r of runnersAlive) {
      if (!r.alive || r.invuln > 0 || r.board) continue;
      if (Math.hypot(r.x - o.x, r.y - o.y) < RUNNER_R + ONI_R - 4) { hurtRunner(g, r, o); break; }
    }
  }
  if (!g.ents.some((e) => e.role === 'runner' && e.alive)) g.status = 'oniwin';
}

// ================= 入力アクション =================
function doAction(g, e) {                                   // SPACE：設置／テレポート／宝箱
  if (g.status !== 'playing' || !e.alive) return;
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
    e.x = e.spawn.x; e.y = e.spawn.y; e.next = null;
    if (respawning) e.resp = false; else e.tpCd = ONI_TP_CD;
    fxNear(g, 'warp', e.x, e.y);
    evTo(e.id, '🌀 スポーン位置へテレポート');
    return;
  }
  if (e.board) return;
  const c = nearestChest(g, e);
  if (!c) return;
  if (e.item) { evTo(e.id, '⚠ アイテムは1個までしか持てない'); return; }
  e.item = ITEMS[Math.floor(Math.random() * ITEMS.length)];
  c.open = true; c.respawn = CHEST_RESPAWN;
  evTo(e.id, '🎁 ' + ITEM_NAME[e.item] + ' を入手！' + (e.item === 'stun' ? '（鬼が近づくと自動発動）' : '（Qキー / ボタンで使用）'));
}
function nearestChest(g, e) {
  for (const c of g.chests) if (!c.open && Math.hypot(e.x - c.x, e.y - c.y) < RUNNER_R + 36) return c;
  return null;
}
function useItem(g, e) {                                    // Q：ブーツ／透明化（スタンは自動）
  if (g.phase !== 'play' || g.status !== 'playing' || !e.alive || e.role !== 'runner' || !e.item || e.board) return;
  if (e.item === 'stun') { evTo(e.id, '💫 スタングレネードは鬼が近づくと自動で発動する'); return; }
  const it = e.item; e.item = null;
  if (it === 'boots') { e.boost = BOOST_SEC; evTo(e.id, '👟 スピードアップ！'); }
  else if (it === 'invis') { e.invis = INVIS_SEC; evTo(e.id, '👻 透明化！鬼から完全に見えない'); }
}

// ================= 受信者ごとの状態 =================
// 明るい視界は壁越しでも見える（視線判定はしない）。範囲外の情報はサーバーが送らない
function snapshot(g, r) {
  let ref = r;
  if (r.role === 'runner' && !r.alive) ref = g.ents.find((e) => e.role === 'runner' && e.alive) || r;
  const boarding = !!(g.board && g.board.id === r.id);
  const ghost = boarding ? 650 : (r.role === 'oni' ? CFG.ghostR.oni : CFG.ghostR.runner);
  const ents = [];
  for (const e of g.ents) {
    if (e === r) continue;
    const info = { id: e.id, n: e.name, x: e.x, y: e.y, role: e.role, al: e.alive, e: e.hasEraser, st: e.stun > 0, inv: e.invuln > 0, sd: e.side, sk: e.skin, iv: e.invis > 0, hp: e.hp };
    if (e.role === r.role) ents.push(info);
    else if (e.alive && !(e.invis > 0) && Math.hypot(e.x - ref.x, e.y - ref.y) < ghost) ents.push(info);
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
    if (c && !(c.invis > 0) && !c.board) ping = { x: c.x, y: c.y };
  }
  let rev = null;                                           // 突入したエレベーターの位置（鬼にだけピンポイント公開）
  if (r.role === 'oni' && g.board) { const c = elevCenter(g.board.side); rev = { x: c.x, y: c.y, side: g.board.side, left: g.board.left }; }
  return {
    s: g.status, ph: g.phase, pl: Math.max(0, g.placeLeft), placed: E.placed, t: g.time, slide: g.slide, role: r.role, side: ref.side,
    me: {
      x: r.x, y: r.y, al: r.alive, hp: r.hp, e: r.hasEraser, inv: r.invuln > 0, st: r.stun > 0, rs: r.stun > 0 && r.resp,
      item: r.item, boost: Math.max(0, r.boost), iv: Math.max(0, r.invis), wcd: Math.max(0, r.wcd), tp: Math.max(0, r.tpCd),
      board: boarding, nc: r.role === 'runner' && r.alive && !r.board && !!nearestChest(g, r)
    },
    cam: { x: ref.x, y: ref.y }, ents, ping, rev, er, hint, eh,
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
    if (prev !== g.status) g.endAt = Date.now() + RESULT_WAIT;
    for (const e of g.ents) {
      if (e.cpu) continue;
      const s = io.sockets.sockets.get(e.id);
      if (!s) continue;
      const snap = snapshot(g, e);
      if (changed) s.emit('state', snap); else s.volatile.emit('state', snap);
    }
    // CPU戦は自動でロビーに戻さない（タイトルへ戻るのはプレイヤーの操作）
    if (g.status !== 'playing' && !room.solo && Date.now() > g.endAt) toLobby(room);
  }
}, 1000 / 60);

// ================= Socket.io =================
io.on('connection', (socket) => {
  socket.on('create', (d) => {
    leaveRoom(socket.id);
    const room = makeRoom(socket, false);
    if (!room) return;
    addPlayer(room, socket, d && d.name, 'auto', d && d.skin);
    sendLobby(room);
  });
  socket.on('solo', (d) => {                       // CPUと戦う：1人で即スタート。終了後はタイトルへ
    leaveRoom(socket.id);
    const room = makeRoom(socket, true);
    if (!room) return;
    addPlayer(room, socket, d && d.name, 'runner', d && d.skin);
    startGame(room);
  });
  socket.on('join', (d) => {
    const code = String((d && d.code) || '').replace(/\D/g, '').slice(0, 5);
    if (code.length !== 5) { socket.emit('errmsg', '5桁のルームコードを入力してください'); return; }
    const room = rooms.get(code);
    if (!room || room.solo) { socket.emit('errmsg', 'そのルームは見つかりません'); return; }
    if (room.players.size >= MAX_PLAYERS && !room.players.has(socket.id)) { socket.emit('errmsg', 'ルームが満員です'); return; }
    leaveRoom(socket.id);
    addPlayer(room, socket, d && d.name, 'auto', d && d.skin);
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
    room.players.get(socket.id).skin = cleanSkin(v);
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
  socket.on('action', () => {
    const room = sockRoom.get(socket.id);
    const g = room && room.game;
    const e = g && g.ents.find((x) => x.id === socket.id);
    if (e) doAction(g, e);
  });
  socket.on('useItem', () => {
    const room = sockRoom.get(socket.id);
    const g = room && room.game;
    const e = g && g.ents.find((x) => x.id === socket.id);
    if (e) useItem(g, e);
  });
  socket.on('backToLobby', () => {
    const room = sockRoom.get(socket.id);
    if (room && !room.solo && room.game && room.game.status !== 'playing') toLobby(room);
  });
  socket.on('leave', () => leaveRoom(socket.id));
  socket.on('disconnect', () => leaveRoom(socket.id));
});

const PORT = process.env.PORT || 3000;
server.listen(PORT, () => console.log('Server listening on ' + PORT));
