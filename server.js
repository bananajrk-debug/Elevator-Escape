// server.js に追加・変更する主なSocketイベント

// 参加申請を受け付ける一時的なキュー
const joinRequests = new Map(); // roomCode -> [{ socketId, name, skin, socket }]

// joinイベントの代わりに「参加申請」を送る
socket.on('requestJoin', (d) => {
  const code = String((d && d.code) || '').replace(/\D/g, '').slice(0, 5);
  const room = rooms.get(code);
  if (!room || room.solo) {
    socket.emit('errmsg', 'そのルームは見つかりません');
    return;
  }
  if (room.players.size >= MAX_PLAYERS) {
    socket.emit('errmsg', 'ルームが満員です');
    return;
  }

  // ホストに申請を通知
  const hostSocketId = room.host;
  io.to(hostSocketId).emit('joinRequest', {
    id: socket.id,
    name: cleanName(d.name),
    skin: cleanSkin(d.skin),
    code: code
  });
  socket.emit('ev', 'ホストに参加申請を送信しました…返答を待っています');
});

// ホストが承認したとき
socket.on('approveJoin', (data) => {
  const room = sockRoom.get(socket.id);
  if (!room || room.host !== socket.id) return;
  
  const targetSocket = io.sockets.sockets.get(data.targetId);
  if (!targetSocket) return;

  leaveRoom(data.targetId);
  addPlayer(room, targetSocket, data.name, 'auto', data.skin);
  sendLobby(room);
  targetSocket.emit('ev', '参加申請が承認されました！');
});

// ホストが拒否したとき
socket.on('rejectJoin', (data) => {
  const targetSocket = io.sockets.sockets.get(data.targetId);
  if (targetSocket) {
    targetSocket.emit('errmsg', 'ホストに参加を拒否されました');
  }
});
```[cite: 8]

---

### 2. クライアント側のコード (`index.html`)

ハンバーガーメニュー、承認モーダル、全員が横並びになるロビー（頭上名前＋👑、足元ロールアイコン）を実装したHTML/JSの構造です。

```html
<!-- index.html のUI・スクリプトのアップデート部分 -->

<!-- タイトル画面に追加するハンバーガーボタン -->
<button id="burgerBtn" class="btn gray" style="position:fixed; top:16px; right:16px; z-index:10; width:50px; height:50px; font-size:24px; border-radius:50%;">☰</button>

<!-- ハンバーガーメニューモーダル -->
<div id="burgerMenu" class="overlay" style="background:rgba(0,0,0,0.7); justify-content:flex-end;">
  <div style="width:300px; height:100%; background:#1e1b4b; border-left:4px solid #ffd23f; padding:24px; display:flex; flex-direction:column; gap:16px;">
    <h2>メニュー</h2>
    <button class="btn yellow" id="menuLogin">👤 ログイン / アカウント</button>
    <button class="btn blue" id="menuFriends">👥 フレンド一覧 (<span id="friendCount">0</span>)</button>
    <button class="btn gray" id="menuClose" style="margin-top:auto;">閉じる</button>
  </div>
</div>

<!-- ホスト用：参加申請モーダル -->
<div id="requestModal" class="overlay" style="background:rgba(0,0,0,0.8); align-items:center; justify-content:center;">
  <div class="panel" style="text-align:center;">
    <h2 style="color:#ffd23f;">📩 参加申請</h2>
    <p id="reqMsg" style="font-size:18px; margin:20px 0; font-weight:800;"></p>
    <div style="display:flex; gap:16px; justify-content:center;">
      <button class="btn red" id="reqReject" style="padding:12px 28px;">拒否する</button>
      <button class="btn yellow" id="reqAccept" style="padding:12px 28px;">承認する</button>
    </div>
  </div>
</div>
```[cite: 7]

```javascript
/* JavaScript側：全員横並びロビー＆頭上名前・足元アイコン描画のアップデート */

// ハンバーガーメニューの開閉
$('burgerBtn').onclick = () => show('burgerMenu', true);$('menuClose').onclick = () => show('burgerMenu', false);

// ホストに申請が届いたとき
let pendingReqId = null;
socket.on('joinRequest', (req) => {
  pendingReqId = req.id;
  $('reqMsg').textContent = `「${req.name}」さんがルーム (${req.code}) への参加を希望しています`;
  show('requestModal', true);
});

$('reqAccept').onclick = () => {
  if (pendingReqId) {
    socket.emit('approveJoin', { targetId: pendingReqId, name: $('reqMsg').textContent }); // 修正：対象IDを渡す
    show('requestModal', false);
    pendingReqId = null;
  }
};
$('reqReject').onclick = () => {
  if (pendingReqId) {
    socket.emit('rejectJoin', { targetId: pendingReqId });
    show('requestModal', false);
    pendingReqId = null;
  }
};

// ロビー描画のアップデート（フォスタ/ブロスタ風：全員を横に並べる）
function renderLobby() {
  const d = lobbyData;
  $('codeNum').textContent = d.code; 
  $('codeBig').textContent = d.code;
  
  // 左側の簡易リスト（従来のロースター）
  const ro = $('roster'); ro.innerHTML = '';
  
  // ステージ中央に全員のキャラクターを横並びで表示するコンテナ
  let stageContainer = $('lobbyStageAvatars');
  if (!stageContainer) {
    stageContainer = document.createElement('div');
    stageContainer.id = 'lobbyStageAvatars';
    stageContainer.style.cssText = 'position:absolute; bottom:180px; left:50%; transform:translateX(-50%); display:flex; gap:20px; align-items:flex-end; z-index:3;';
    document.querySelector('#lobby').appendChild(stageContainer);
  }
  stageContainer.innerHTML = '';

  for (const p of d.players) {
    const isHost = (p.id === d.host);
    const isMe = (p.id === d.you);
    const sk = SKINS[p.skin || 0];

    // リスト用カード
    const c = document.createElement('div'); 
    c.className = 'card ' + p.role + (isMe ? ' me' : ''); 
    c.innerHTML = `<span>${p.name} ${isHost ? '👑' : ''}</span><span class="badge ${p.role}">${roleLabel[p.role]}</span>`;
    ro.appendChild(c);

    // ステージ上のキャラクター表示（ブロスタ風）
    const avBox = document.createElement('div');
    avBox.style.cssText = 'display:flex; flex-direction:column; align-items:center; position:relative;';

    // 1. 頭上の名前 ＋ ホストの👑
    const nameTag = document.createElement('div');
    nameTag.style.cssText = 'background:rgba(0,0,0,0.7); padding:4px 10px; border-radius:8px; font-weight:900; font-size:14px; margin-bottom:8px; white-space:nowrap; border:2px solid ' + (isMe ? '#ffd23f' : '#fff');
    nameTag.textContent = p.name + (isHost ? ' 👑' : '');
    avBox.appendChild(nameTag);

    // 2. キャラクター本体（アバター円）
    const avatar = document.createElement('div');
    avatar.className = 'avatar ' + p.role;
    avatar.style.cssText = `width:90px; height:90px; border-radius:50%; display:flex; align-items:center; justify-content:center; font-size:42px; background:radial-gradient(circle at 35% 30%, rgba(255,255,255,.55), ${p.role === 'oni' ? sk.o : sk.c} 60%); border:4px solid #fff; box-shadow:0 8px 0 rgba(0,0,0,.35);`;
    avatar.textContent = roleEmoji[p.role];
    avBox.appendChild(avatar);

    // 3. 足元のロールアイコン
    const footBadge = document.createElement('div');
    footBadge.style.cssText = 'margin-top:6px; font-size:18px; background:rgba(0,0,0,0.6); padding:2px 8px; border-radius:12px;';
    footBadge.textContent = roleEmoji[p.role] + ' ' + roleLabel[p.role];
    avBox.appendChild(footBadge);

    stageContainer.appendChild(avBox);
  }

  // 自身のスキン設定など
  const me = d.players.find((p) => p.id === d.you) || { name: '', role: 'auto', skin: 0 };
  const currentSk = SKINS[me.skin || 0];
  skinSel = me.skin || 0; 
  try { localStorage.setItem('pskin', skinSel); } catch (e) {}
  $('skname').textContent = 'スキン：' + currentSk.n; 
  buildSkins();

  document.querySelectorAll('#lobby [data-role]').forEach((b) => b.classList.toggle('active', b.dataset.role === me.role));
  const host = d.host === d.you;
  $('start').style.display = host ? '' : 'none';
  $('start').disabled = d.state !== 'lobby';
  $('rulesBtn').style.display = '';$('rulesBtn').textContent = host ? '⚙ ルール設定' : '📋 ルール確認';
  $('lnote').textContent = d.state === 'playing' ? '試合中です。終了までお待ちください。' : (host ? '準備ができたらゲーム開始を押してね！' : 'ホストの開始を待っています…');
}
```[cite: 7]

---

### フレンド機能についての相談

フレンド機能について、さらに使いやすくするためにどういう仕様にするか一緒に決めていきましょう！

1. **フレンドの登録方法**: 
   * 一緒に遊んだ履歴（直近のプレイヤー）から「フレンド申請」を送れるようにする？
   * あるいは、フレンドコード（専用の短いID）をお互いに入力して追加する？
2. **フレンド欄からの参加・招待**:
   * フレンド欄を開くと、そのフレンドが「ロビーにいる」「試合中」などがリアルタイムで表示され、ロビーにいるフレンドの横にある**「参加する ▶」**ボタンを押すだけで、自動で参加申請（またはルーム入室）が飛ぶようにすると超スムーズになります！

このあたりのフレンド機能のこだわりや、「こうしたい！」という希望があればぜひ教えてください！
