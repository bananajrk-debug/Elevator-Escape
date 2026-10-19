// ================= ショップ（スキン）・クエスト（実績・称号）=================
function openShop(tab) {
  if (inGame) return;
  initAudio(); 
  show('menu', false); 
  showShopTab(tab || 'shop'); 
  try {
    renderShop(); 
    renderQuest(); 
  } catch (e) {
    console.error('Shop render error:', e);
  }
  show('shop', true);
}
function showShopTab(t) {
  $('tabShop').style.display = t === 'shop' ? 'block' : 'none'; 
  $('tabQuest').style.display = t === 'quest' ? 'block' : 'none';
  $('tabShopBtn').className = 'btn ' + (t === 'shop' ? 'yellow' : 'gray'); 
  $('tabQuestBtn').className = 'btn ' + (t === 'quest' ? 'yellow' : 'gray');
}
$('tabShopBtn').onclick = () => showShopTab('shop'); 
$('tabQuestBtn').onclick = () => showShopTab('quest');
$('shopClose').onclick = () => show('shop', false);
$('shop').addEventListener('click', (e) => { if (e.target === $('shop')) show('shop', false); });
$('btnShopT').onclick = () => openShop('shop'); 
$('btnShopL').onclick = () => openShop('shop');
$('titleOff').onclick = () => socket.emit('setTitle', { id: null });

function afterWallet() { 
  try {
    renderShop(); 
    renderQuest(); 
  } catch (e) {}
  if (lobbyData && !inGame) buildSkins(); 
}

function equipSkin(i) {
  skinSel = i; 
  try { localStorage.setItem('pskin', i); } catch (e) {}
  if (lobbyData && lobbyData.state === 'lobby') socket.emit('setSkin', i);
  renderShop();
}

function drawSkinPreview(c2, idx) {                       
  if (!c2) return;
  const c = c2.getContext('2d');
  if (!c) return;
  const ctx0 = ctx, th0 = TH;
  c.clearRect(0, 0, c2.width, c2.height);
  ctx = c; TH = 0;
  c.save(); 
  c.translate(c2.width / 2, c2.height * 0.7); 
  c.scale(2.4, 2.4);
  try { 
    drawHuman({ role: 'runner', al: true, sk: idx, hp: 100, noLabel: true, noHp: true }, { x: 0, y: 0, fx: 1, mv: 0, ph: 0 }, 1, false, 0); 
  } catch (err) {
    // 描画エラー時のフォールバック
  } finally { 
    c.restore(); 
    ctx = ctx0; 
    TH = th0; 
  }
}

function renderShop() {
  const row = $('skRow'); if (!row) return; row.innerHTML = '';
  const owned = ownedSkins(), price = (catalog && catalog.price) ? catalog.price : 50;
  if ($('egNum')) $('egNum').textContent = (wallet && wallet.eg != null) ? wallet.eg : 0;
  if ($('shopNote')) {
    $('shopNote').textContent = profile.name ? 'スキンは1着 ' + price + ' EG。購入したスキンはアカウントに保存されます。左右にスワイプ／スクロールで他のスキンも見られます。'
      : '⚠ ユーザー名を登録（☰メニュー）すると、EGを貯めてスキンを購入できます。（スカイ・ミント・サンセットは無料）';
  }
  SKINS.forEach((sk, i) => {
    const has = owned.includes(i), eq = has && i === skinSel;
    const card = document.createElement('div'); card.className = 'skcard' + (eq ? ' equipped' : '') + (has ? '' : ' locked');
    const nmEl = document.createElement('div'); nmEl.className = 'nm'; nmEl.textContent = sk.n;                  
    const c2 = document.createElement('canvas'); c2.width = 130; c2.height = 160;
    card.append(nmEl, c2);
    if (has) {
      const b = document.createElement('button'); b.className = 'btn ' + (eq ? 'gray' : 'blue') + ' pr'; b.textContent = eq ? '装備中 ✓' : '装備する'; b.disabled = eq;
      b.onclick = () => equipSkin(i); card.appendChild(b);
    } else {
      const b = document.createElement('button'); b.className = 'btn yellow pr'; b.textContent = '🪙 ' + price + ' EG';                
      b.onclick = () => { if (confirm(sk.n + ' を ' + price + ' EG で購入しますか？')) socket.emit('buySkin', { id: i }); };
      card.appendChild(b);
    }
    row.appendChild(card); 
    drawSkinPreview(c2, i);
  });
}

function renderQuest() {
  const box = $('questList'); if (!box) return; box.innerHTML = '';
  const cat = catalog || { ach: [], egCpu: 15, egLead: 2, ptsLead: 100 };
  if ($('questInfo')) {
    $('questInfo').textContent = '✏ サブクエスト：迷路に現れる「シャー芯」を拾うと +' + cat.ptsLead + 'pt と +' + cat.egLead + ' EG！ 🤖 CPU戦を最上階までクリアすると +' + cat.egCpu + ' EG。実績を達成すると EG と称号がもらえ、称号はここで装備できます（ロビーでも表示）。';
  }
  const got = (wallet && wallet.ach) ? wallet.ach : [], st = (wallet && wallet.stats) ? wallet.stats : {}, cur = (wallet && wallet.title) ? wallet.title : null;
  if (!cat.ach) return;
  for (const a of cat.ach) {
    const done = got.includes(a.id);
    const row = document.createElement('div'); row.className = 'qitem' + (done ? ' done' : '');
    const left = document.createElement('div');
    const n = document.createElement('div'); n.className = 'qn'; n.textContent = (done ? '✅ ' : '⬜ ') + a.n;
    const d = document.createElement('div'); d.className = 'qd'; d.textContent = a.d;
    const r = document.createElement('div'); r.className = 'qr'; r.textContent = '報酬：+' + a.eg + ' EG ／ 称号『' + a.t + '』';
    left.append(n, d, r);
    if (a.need) {
      const v = Math.min(a.need, (st && st[a.stat]) || 0);
      const bar = document.createElement('div'); bar.className = 'qbar'; const fill = document.createElement('i'); fill.style.width = (v / a.need * 100) + '%'; bar.appendChild(fill);
      const pv = document.createElement('div'); pv.className = 'qd'; pv.textContent = v + ' / ' + a.need;
      left.append(bar, pv);
    }
    row.appendChild(left);
    if (done) {
      const b = document.createElement('button'); b.className = 'btn ' + (cur === a.id ? 'gray' : 'yellow') + ' mini'; b.textContent = cur === a.id ? '装備中 ✓' : '称号を装備'; b.disabled = cur === a.id;
      b.onclick = () => socket.emit('setTitle', { id: a.id }); row.appendChild(b);
    }
    box.appendChild(row);
  }
  if (!profile.name) { const w = document.createElement('div'); w.className = 'note2'; w.textContent = '⚠ ユーザー名を登録すると、実績の記録・EG・称号が保存されます。'; box.appendChild(w); }
}
