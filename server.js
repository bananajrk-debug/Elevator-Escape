const express = require('express');
const http = require('http');
const { Server } = require('socket.io');

const app = express();
const server = http.createServer(app);
const io = new Server(server);

app.use(express.static('public'));

// ゲームの状態管理
const players = {};
let gameData = {
  eraser: { x: 400, y: 300, holder: null, isTaken: false },
  elevator: { x: 700, y: 50, isOpen: false, timer: 0 },
  escapees: 0
};

io.on('connection', (socket) => {
  console.log(`ユーザー接続: ${socket.id}`);

  // プレイヤーの初期化（ランダムに「鬼」か「逃げ」を割り当て。最初は逃げ多め）
  const role = Object.keys(players).length % 3 === 0 ? 'oni' : 'runner';
  players[socket.id] = {
    id: socket.id,
    x: Math.random() * 600 + 100,
    y: Math.random() * 400 + 100,
    radius: 15,
    role: role,
    hasEraser: false,
    escaped: false,
    color: role === 'oni' ? '#ff4757' : '#2ed573'
  };

  // クライアントへ初期状態を送信
  socket.emit('init', { id: socket.id, players, gameData });

  // 移動の同期
  socket.on('move', (data) => {
    if (players[socket.id] && !players[socket.id].escaped) {
      players[socket.id].x = data.x;
      players[socket.id].y = data.y;

      // 消しゴムの当たり判定（逃げ側のみ取得可能）
      const e = gameData.eraser;
      if (!e.isTaken && players[socket.id].role === 'runner') {
        const dist = Math.hypot(players[socket.id].x - e.x, players[socket.id].y - e.y);
        if (dist < players[socket.id].radius + 15) {
          e.isTaken = true;
          e.holder = socket.id;
          players[socket.id].hasEraser = true;
          // 消しゴムを取るとエレベーターが開き始める
          gameData.elevator.isOpen = true;
          gameData.elevator.timer = 600; // 約10秒間開く (60fps * 10)
        }
      }

      // 消しゴムを持っているプレイヤーがエレベーターに到達したか判定
      const el = gameData.elevator;
      if (players[socket.id].hasEraser && el.isOpen) {
        const elDist = Math.hypot(players[socket.id].x - el.x, players[socket.id].y - el.y);
        if (elDist < 30) {
          players[socket.id].escaped = true;
          gameData.escapees++;
          // ゲームリセット等の処理はシンプル化
        }
      }

      // 鬼が逃げに触れた場合の判定
      if (players[socket.id].role === 'oni') {
        for (let id in players) {
          if (players[id].role === 'runner' && !players[id].escaped) {
            const hitDist = Math.hypot(players[socket.id].x - players[id].x, players[socket.id].y - players[id].y);
            if (hitDist < players[socket.id].radius + players[id].radius) {
              // 捕まったら消しゴムを落とす
              if (players[id].hasEraser) {
                players[id].hasEraser = false;
                gameData.eraser.isTaken = false;
                gameData.eraser.holder = null;
                gameData.eraser.x = players[id].x;
                gameData.eraser.y = players[id].y;
              }
            }
          }
        }
      }
    }
  });

  socket.on('disconnect', () => {
    console.log(`ユーザー切断: ${socket.id}`);
    if (players[socket.id] && players[socket.id].hasEraser) {
      gameData.eraser.isTaken = false;
      gameData.eraser.holder = null;
    }
    delete players[socket.id];
  });
});

// ゲームのメインループ（サーバー側でエレベーターのタイマー等を管理）
setInterval(() => {
  if (gameData.elevator.isOpen) {
    gameData.elevator.timer--;
    if (gameData.elevator.timer <= 0) {
      gameData.elevator.isOpen = false; // ギリギリで閉まるヒヤヒヤ要素！
    }
  }
  io.emit('update', { players, gameData });
}, 1000 / 60);

const PORT = process.env.PORT || 3000;
server.listen(PORT, () => {
  console.log(`サーバー起動中: http://localhost:${PORT}`);
});
