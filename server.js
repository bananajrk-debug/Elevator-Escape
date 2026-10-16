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

// 画像の迷路構造をベースに90度回転させ、均一な通路（幅約100px〜120px）を確保した迷路の壁データ
const walls = [
  // 外枠
  { x: 0, y: 0, w: MAP_WIDTH, h: 60 },
  { x: 0, y: MAP_HEIGHT - 60, w: MAP_WIDTH, h: 60 },
  { x: 0, y: 0, w: 60, h: MAP_HEIGHT },
  { x: MAP_WIDTH - 60, y: 0, w: 60, h: MAP_HEIGHT },

  // 迷路内部の仕切り壁（画像ベースを90度回転＆調整）
  { x: 300, y: 300, w: 1400, h: 60 },
  { x: 300, y: 360, w: 60, h: 400 },
  { x: 700, y: 500, w: 60, h: 800 },
  { x: 1100, y: 360, w: 60, h: 500 },
  { x: 500, y: 900, w: 1000, h: 60 },
  { x: 300, y: 1200, w: 900, h: 60 },
  { x: 1500, y: 600, w: 60, h: 1000 },
  { x: 900, y: 1500, w: 700, h: 60 },
  { x: 500, y: 1500, w: 60, h: 300 }
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
    
    // 初期位置：エレベーター付近（下部中央）
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
        // 消しゴムの場所：エレベーターから一番遠いマップ最奥（上部中央）
        eraser: { x: MAP_WIDTH / 2, y: 150, holder: null, isTaken: false },
        elevator: { x: MAP_WIDTH / 2, y: MAP_HEIGHT - 100, isOpen: false, timer: 0 },
        mode: mode,
        gameOver: false
      },
      cpu: mode === 'cpu' ? {
        id: 'cpu_oni',
        name: 'CPU鬼',
        x: MAP_WIDTH / 2,
        y: MAP_HEIGHT / 2,
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
      if (dist < room.player.radius + 20) {
        e.isTaken = true;
        e.holder = room.player.id;
        room.player.hasEraser = true;
        room.gameData.elevator.isOpen = true;
        room.gameData.elevator.timer = 1200; // 約20秒間オープン
      }
    }

    // エレベーターでの脱出判定
    let el = room.gameData.elevator;
    if (room.player.hasEraser && el.isOpen) {
      let elDist = Math.hypot(room.player.x - el.x, room.player.y - el.y);
      if (elDist < 40) {
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

      if (canMove(nextX, cpu.y, cpu.radius)) cpu.x = nextX;
      if (canMove(cpu.x, nextY, cpu.radius)) cpu.y = nextY;

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
