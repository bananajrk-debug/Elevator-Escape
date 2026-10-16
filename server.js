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

// 迷路の壁データ（外壁 + 迷路を仕切るブロックの配置）
const walls = [
  // 外枠
  { x: 0, y: 0, w: MAP_WIDTH, h: 40 },
  { x: 0, y: MAP_HEIGHT - 40, w: MAP_WIDTH, h: 40 },
  { x: 0, y: 0, w: 40, h: MAP_HEIGHT },
  { x: MAP_WIDTH - 40, y: 0, w: 40, h: MAP_HEIGHT },
  // 迷路の内部壁（一本道で繋がった迷路風の障害物）
  { x: 200, y: 200, w: 1400, h: 40 },
  { x: 200, y: 400, w: 40, h: 1000 },
  { x: 600, y: 600, w: 1200, h: 40 },
  { x: 600, y: 800, w: 40, h: 800 },
  { x: 1000, y: 300, w: 40, h: 1200 },
  { x: 1400, y: 700, w: 40, h: 1100 },
  { x: 400, y: 1600, w: 1200, h: 40 }
];

// 矩形同士の当たり判定
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
    const { name, mode } = data; // mode: 'pvp' or 'cpu'
    
    // 初期位置（マップの上部付近）
    let x = 200 + Math.random() * 200;
    let y = 100;
    
    rooms[socket.id] = {
      player: {
        id: socket.id,
        name: name || 'プレイヤー',
        x: x,
        y: y,
        radius: 18,
        role: 'runner',
        hasEraser: false,
        escaped: false,
        color: '#2ed573'
      },
      gameData: {
        eraser: { x: 1000, y: 1800, holder: null, isTaken: false },
        elevator: { x: MAP_WIDTH / 2, y: MAP_HEIGHT - 80, isOpen: false, timer: 0 },
        mode: mode,
        gameOver: false
      },
      cpu: mode === 'cpu' ? {
        id: 'cpu_oni',
        name: 'CPU鬼',
        x: MAP_WIDTH / 2,
        y: MAP_HEIGHT / 2,
        radius: 18,
        role: 'oni',
        color: '#ff4757',
        speed: 3
      } : null
    };

    socket.emit('init', rooms[socket.id]);
  });

  socket.on('move', (data) => {
    let room = rooms[socket.id];
    if (!room || room.gameData.gameOver || room.player.escaped) return;

    let speed = 5;
    let newX = room.player.x;
    let newY = room.player.y;

    if (data.up) newY -= speed;
    if (data.down) newY += speed;
    if (data.left) newX -= speed;
    if (data.right) newX += speed;

    // 壁との衝突判定を行いながら移動
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
        room.gameData.elevator.timer = 900; // 約15秒間オープン
      }
    }

    // エレベーターでの脱出判定（一番下の真ん中）
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
    console.log(`切断: ${socket.id}`);
  });
});

// ゲームの定期ループ（60fps相当でCPUの動きやタイマーを更新）
setInterval(() => {
  for (let id in rooms) {
    let room = rooms[id];
    if (!room || room.gameData.gameOver) continue;

    // エレベータータイマーの処理
    if (room.gameData.elevator.isOpen) {
      room.gameData.elevator.timer--;
      if (room.gameData.elevator.timer <= 0) {
        room.gameData.elevator.isOpen = false; // ヒヤヒヤのタイムアップ！
      }
    }

    // CPU（鬼）のAI処理
    let cpu = room.cpu;
    if (cpu && !room.player.escaped) {
      let p = room.player;
      let angle = Math.atan2(p.y - cpu.y, p.x - cpu.x);
      let nextX = cpu.x + Math.cos(angle) * cpu.speed;
      let nextY = cpu.y + Math.sin(angle) * cpu.speed;

      if (canMove(nextX, cpu.y, cpu.radius)) cpu.x = nextX;
      if (canMove(cpu.x, nextY, cpu.radius)) cpu.y = nextY;

      // 鬼がプレイヤーに追いついたか
      let catchDist = Math.hypot(cpu.x - p.x, cpu.y - p.y);
      if (catchDist < cpu.radius + p.radius) {
        // 捕まったらゲームオーバー（消しゴムを落とす）
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
