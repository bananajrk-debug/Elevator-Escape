const express = require('express');
const http = require('http');
const { Server } = require('socket.io');

const app = express();
const server = http.createServer(app);
const io = new Server(server);

app.use(express.static('public'));

const MAP_WIDTH = 2000;
const MAP_HEIGHT = 2000;

let rooms = {};

// 通路の幅を均一（幅60pxの通路ができる格子状の迷路壁）にしたデータ
const walls = [
  // 外枠
  { x: 0, y: 0, w: MAP_WIDTH, h: 40 },
  { x: 0, y: MAP_HEIGHT - 40, w: MAP_WIDTH, h: 40 },
  { x: 0, y: 0, w: 40, h: MAP_HEIGHT },
  { x: MAP_WIDTH - 40, y: 0, w: 40, h: MAP_HEIGHT },

  // 均一なグリッド迷路壁
  { x: 160, y: 0, w: 40, h: 400 },
  { x: 160, y: 520, w: 40, h: 1040 },
  { x: 320, y: 160, w: 40, h: 1400 },
  { x: 480, y: 0, w: 40, h: 400 },
  { x: 480, y: 520, w: 40, h: 1200 },
  { x: 640, y: 160, w: 40, h: 1400 },
  { x: 800, y: 320, w: 40, h: 1200 },
  { x: 960, y: 0, w: 40, h: 1400 },
  { x: 1120, y: 160, w: 40, h: 1400 },
  { x: 1280, y: 320, w: 40, h: 1200 },
  { x: 1440, y: 0, w: 40, h: 1400 },
  { x: 1600, y: 160, w: 40, h: 1400 },
  { x: 1800, y: 400, w: 40, h: 1200 },

  // 横方向の接続壁（一本道に仕切る）
  { x: 160, y: 400, w: 320, h: 40 },
  { x: 480, y: 800, w: 320, h: 40 },
  { x: 200, y: 1200, w: 280, h: 40 },
  { x: 640, y: 1200, w: 320, h: 40 },
  { x: 960, y: 800, w: 320, h: 40 },
  { x: 1280, y: 400, w: 320, h: 40 },
  { x: 1440, y: 1200, w: 360, h: 40 }
];

function checkRectCollision(x, y, radius, rect) {
  let closestX = Math.max(rect.x, Math.min(x, rect.x + rect.w));
  let closestY = Math.max(rect.y, Math.min(y, rect.y + rect.h));
  let distX = x - closestX;
  let distY = y - closestY;
  return (distX * distX + distY * distY) < (radius * radius);
}

function canMove(x, y, radius) {
  for (let w of walls) {
    if (checkRectCollision(x, y, radius, w)) return false;
  }
  return true;
}

io.on('connection', (socket) => {
  console.log(`接続: ${socket.id}`);

  socket.on('join_game', (data) => {
    const { name, mode } = data;
    
    // 初期位置（エレベーター近くのスタート地点）
    let x = MAP_WIDTH / 2;
    let y = MAP_HEIGHT - 120;
    
    rooms[socket.id] = {
      player: {
        id: socket.id,
        name: name || 'プレイヤー',
        x: x,
        y: y,
        radius: 16,
        role: 'runner',
        hasEraser: false,
        escaped: false,
        color: '#2ed573'
      },
      gameData: {
        // 消しゴムの場所：エレベーターから一番遠いマップの最奥（上部中央）
        eraser: { x: MAP_WIDTH / 2, y: 100, holder: null, isTaken: false },
        elevator: { x: MAP_WIDTH / 2, y: MAP_HEIGHT - 80, isOpen: false, timer: 0 },
        mode: mode,
        gameOver: false
      },
      cpu: mode === 'cpu' ? {
        id: 'cpu_oni',
        name: 'CPU鬼',
        x: MAP_WIDTH / 2,
        y: 800,
        radius: 16,
        role: 'oni',
        color: '#ff4757',
        speed: 2.8
      } : null
    };

    socket.emit('init', rooms[socket.id]);
  });

  socket.on('move', (data) => {
    let room = rooms[socket.id];
    if (!room || room.gameData.gameOver || room.player.escaped) return;

    let speed = 4.5;
    let newX = room.player.x;
    let newY = room.player.y;

    if (data.up) newY -= speed;
    if (data.down) newY += speed;
    if (data.left) newX -= speed;
    if (data.right) newX += speed;

    if (canMove(newX, room.player.y, room.player.radius)) room.player.x = newX;
    if (canMove(room.player.x, newY, room.player.radius)) room.player.y = newY;

    // 消しゴムの取得判定
    let e = room.gameData.eraser;
    if (!e.isTaken) {
      let dist = Math.hypot(room.player.x - e.x, room.player.y - e.y);
      if (dist < room.player.radius + 15) {
        e.isTaken = true;
        e.holder = room.player.id;
        room.player.hasEraser = true;
        room.gameData.elevator.isOpen = true;
        room.gameData.elevator.timer = 1200; // 脱出までの制限時間（約20秒）
      }
    }

    // エレベーターでの脱出判定
    let el = room.gameData.elevator;
    if (room.player.hasEraser && el.isOpen) {
      let elDist = Math.hypot(room.player.x - el.x, room.player.y - el.y);
      if (elDist < 35) {
        room.player.escaped = true;
        room.gameData.gameOver = true;
      }
    }
  });

  socket.on('disconnect', () => {
    delete rooms[socket.id];
  });
});

setInterval(() => {
  for (let id in rooms) {
    let room = rooms[id];
    if (!room || room.gameData.gameOver) continue;

    if (room.gameData.elevator.isOpen) {
      room.gameData.elevator.timer--;
      if (room.gameData.elevator.timer <= 0) {
        room.gameData.elevator.isOpen = false;
      }
    }

    let cpu = room.cpu;
    if (cpu && !room.player.escaped) {
      let p = room.player;
      let angle = Math.atan2(p.y - cpu.y, p.x - cpu.x);
      let nextX = cpu.x + Math.cos(angle) * cpu.speed;
      let nextY = cpu.y + Math.sin(angle) * cpu.speed;

      if (canMatch = canMove(nextX, cpu.y, cpu.radius)) cpu.x = nextX;
      if (canMatch = canMove(cpu.x, nextY, cpu.radius)) cpu.y = nextY;

      let catchDist = Math.hypot(cpu.x - p.x, cpu.y - p.y);
      if (catchDist < cpu.radius + p.radius) {
        if (p.hasEraser) {
          p.hasEraser = false;
          room.gameData.eraser.isTaken = false;
          room.gameData.eraser.holder = null;
          room.gameData.eraser.x = p.x;
          room.gameData.eraser.y = p.y;
        } else {
          room.gameData.gameOver = true;
        }
      }
    }

    io.to(id).emit('update', {
      player: room.player,
      cpu: room.cpu,
      gameData: room.gameData
    });
  }
}, 1000 / 60);

const PORT = process.env.PORT || 10000;
server.listen(PORT, () => {
  console.log(`サーバー起動中: http://localhost:${PORT}`);
});
