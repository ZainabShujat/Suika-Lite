/* suika-physics.js — full updated file
   - Scoring helper centralized & tuned (classic/tight/generous presets)
   - Fruit radii computed as percentage of board width (responsive)
   - Dynamic gravity, spin clamping, increased inertia for big fruits
   - Next-preview deterministic (spawn consumes nextPick then immediately refill)
   - Client->canvas coordinate mapping + resize scaling to avoid zoom cheats
   - Achievement popups for Level 8 ("Almost there") and Level 9 ("WATERMELON")
   - Slight UI improvements: chain shout, float pops, charge UI updates (inline styles where needed)
   - Keep previous mechanics: ClearSmall (level <=2), merge scheduling, supernova easter
*/

(() => {
  const { Engine, World, Bodies, Body, Events, Composite, Vector } = Matter;

  // -------------------------
  // CONFIG
  // -------------------------
  const MAX_LEVEL = 9;
  const SPAWN_MAX_LEVEL = 4;
  const SPAWN_WEIGHTS = [0.40, 0.32, 0.18, 0.10];

  // Fruit sizing (fraction of board width)
  // Level 1 radius fraction of boardW
  const RADIUS_BASE_FRAC = 0.02; // level1 radius = boardW * 0.06
  const RADIUS_GROWTH = 1.4;    // per-level growth multiplier
  const MAX_RADIUS_FRAC = 0.26;  // clamp so fruit never bigger than this fraction of boardW

  const MERGE_MIN_DIST = 1.0; // exact contact (sum of radii)
  const SPAWN_DEBOUNCE = 200;
  const SPAWN_GRACE_MS = 900;
  const CLEAR_UNLOCK_SCORE = 500;
  const CLEAR_RECHARGE_POINTS = 300;

  // Visual tuning
  const VISUAL_DIAMETER_FACTOR = 1.02; // draw slightly larger to hide solver gaps

  // scoring preset: 'classic', 'tight', 'generous'
  const SCORE_PRESET = 'classic';

  // -------------------------
  // RUNTIME STATE
  // -------------------------
  let engine, world;
  let bodies = [];
  let ground, leftWall, rightWall;
  let isRunning = false, gameOver = false;
  let score = 0, high = 0;
  let mergedThisStep = new Set();

  let nextPick = null;
  let lastSpawnAt = 0;
  let lastSpawnTime = 0;

  // ClearSmall state
  let clearUnlocked = false;
  let clearAvailable = false;
  let pointsAccumSinceClear = 0;
  let clearUsed = false;

  // chain detection
  let chainCount = 0;
  let chainTimer = null;
  const CHAIN_TIMEOUT = 900;
  let lastMergeTime = 0;

  // UI / DOM
  let chainShoutEl = null;
  let FRUIT_IMAGES = {};
  let canvasElem = null;
  let previousBoardRect = null;

  // particles
  let particles = [];

  // -------------------------
  // Utilities
  // -------------------------
  function el(id){ return document.getElementById(id); }

  function computeBoardRect(){
    const isMobile = window.innerWidth < 760;
    const boardW = Math.min(window.innerWidth * (isMobile ? 0.94 : 0.78), window.innerHeight * 0.78);
    const boardX = (window.innerWidth - boardW) / 2;
    const boardY = (window.innerHeight - boardW) / 2;
    return { boardW, boardX, boardY };
  }

  // radius proportional to boardW
  function radiusForLevel(l){
    const lvl = Math.max(1, Math.min(l, MAX_LEVEL));
    const { boardW } = computeBoardRect();
    const raw = boardW * RADIUS_BASE_FRAC * Math.pow(RADIUS_GROWTH, lvl - 1);
    const clamped = Math.min(raw, boardW * MAX_RADIUS_FRAC);
    return Math.round(Math.max(4, clamped));
  }

  // -------------------------
  // Particles & audio
  // -------------------------
  function spawnParticles(x,y,level, count=18){
    const hueBase = 28 + (level*18) % 320;
    for(let i=0;i<count;i++){
      const ang = Math.random()*Math.PI*2;
      const speed = 1 + Math.random()*3;
      particles.push({
        x, y,
        vx: Math.cos(ang)*speed,
        vy: Math.sin(ang)*speed - 1.3,
        life: 26 + Math.floor(Math.random()*12),
        size: 2 + Math.random()*5,
        col: `hsl(${(hueBase + Math.random()*40)%360} 84% 58%)`
      });
    }
  }
  function updateParticles(){
    for(const p of particles){
      p.x += p.vx; p.y += p.vy; p.vy += 0.12; p.life--;
      p.vx *= 0.996; p.vy *= 0.996;
    }
    particles = particles.filter(p => p.life > 0);
  }
  function drawParticles(){
    noStroke();
    for(const p of particles){
      const alpha = map(p.life, 0, 40, 0, 1);
      drawingContext.globalAlpha = alpha;
      fill(p.col);
      circle(p.x, p.y, p.size);
      drawingContext.globalAlpha = 1;
    }
  }

  let audioCtx = null;
  function ensureAudio(){ if(!audioCtx) audioCtx = new (window.AudioContext || window.webkitAudioContext)(); if(audioCtx.state === 'suspended') audioCtx.resume().catch(()=>{}); }
  function playPop(level){
    try{
      ensureAudio();
      const t0 = audioCtx.currentTime;
      const o = audioCtx.createOscillator();
      const g = audioCtx.createGain();
      o.type = 'sine';
      const base = 420 + (level * 22);
      o.frequency.setValueAtTime(base + Math.random()*35, t0);
      g.gain.setValueAtTime(0.08, t0);
      g.gain.exponentialRampToValueAtTime(0.001, t0 + 0.14);
      o.connect(g); g.connect(audioCtx.destination);
      o.start(t0); o.stop(t0 + 0.14);
    }catch(e){}
  }

  // -------------------------
  // Gravity & spin control
  // -------------------------
  function updateGravity(){
    if(!world || !world.gravity) return;
    const levels = bodies
      .filter(b => b && b._fruit && Number.isFinite(b._fruit.level))
      .map(b => b._fruit.level);
    if(levels.length === 0) {
      world.gravity.y = 1.06;
      return;
    }
    const highestLevel = Math.max(...levels);
    const gravityBase = 0.9;
    const gravityGainPerLevel = 0.06;
    const gravityCap = 1.9;
    const proposed = gravityBase + gravityGainPerLevel * (highestLevel - 1);
    const newG = Number.isFinite(proposed) ? Math.min(proposed, gravityCap) : world.gravity.y;
    if(!Number.isFinite(newG) || newG <= 0 || newG > 10) return;
    world.gravity.y = newG;
  }

  function clampSpinForFruit(b){
    if(!b || !b._fruit || b.isStatic) return;
    const level = Math.max(1, Math.floor(b._fruit.level || 1));
    const maxSpin = Math.max(0.002, 0.02 - 0.0025 * level);
    const current = (b.angularVelocity || 0);
    if(Math.abs(current) > maxSpin){
      Body.setAngularVelocity(b, Math.sign(current) * maxSpin);
    } else {
      if(level >= 6){
        const damping = 0.94;
        Body.setAngularVelocity(b, current * damping);
      }
    }
  }

  // -------------------------
  // Scoring helper
  // -------------------------
  function scoreForMerge(level, chainCount=1){
    let base = 8;
    let chainPower = 0.12;
    if(SCORE_PRESET === 'tight'){ base = 6; chainPower = 0.08; }
    else if(SCORE_PRESET === 'generous'){ base = 12; chainPower = 0.18; }
    const levelPts = Math.round(base * Math.pow(2, Math.max(0, level - 1)));
    const chainMultiplier = 1 + Math.min(0.6, chainPower * Math.max(0, chainCount - 1));
    const pts = Math.round(levelPts * chainMultiplier);
    return Math.max(1, Math.min(999999, pts));
  }

  // -------------------------
  // Bounds & spawn picks
  // -------------------------
  function createBounds(){
    try{
      if(ground) World.remove(world, ground);
      if(leftWall) World.remove(world, leftWall);
      if(rightWall) World.remove(world, rightWall);
    }catch(e){}
    const { boardW, boardX, boardY } = computeBoardRect();
    const thickness = Math.max(120, boardW*0.14);
    ground = Bodies.rectangle(boardX + boardW/2, boardY + boardW + thickness/2, boardW + thickness*2, thickness, { isStatic:true, restitution:0.02, friction:0.92 });
    leftWall = Bodies.rectangle(boardX - thickness/2, boardY + boardW/2, thickness, boardW + thickness*2, { isStatic:true, restitution:0.02, friction:0.92 });
    rightWall = Bodies.rectangle(boardX + boardW + thickness/2, boardY + boardW/2, thickness, boardW + thickness*2, { isStatic:true, restitution:0.02, friction:0.92 });
    World.add(world, [ground, leftWall, rightWall]);
  }

  function weightedPick(){ const weights = SPAWN_WEIGHTS.slice(0, SPAWN_MAX_LEVEL); const total = weights.reduce((a,b)=>a+b,0); const r = Math.random() * total; let cum = 0; for(let i=0;i<weights.length;i++){ cum += weights[i]; if(r < cum) return i+1; } return weights.length; }
  function generateNextPick(){ nextPick = weightedPick(); updateNextPreviewDom(); positionNextPreview(); }

  // -------------------------
  // Clamp inside board (prevents leaks)
  // -------------------------
  function clampBodyInsideBoard(b){
    if(!b || !b.position || !b._fruit) return;
    const { boardW, boardX, boardY } = computeBoardRect();
    const topLineY = boardY + 8;
    const leftBound = boardX + 16 + b._fruit.radius;
    const rightBound = boardX + boardW - 16 - b._fruit.radius;
    if(b.position.x < leftBound) Body.setPosition(b, { x: leftBound, y: b.position.y });
    if(b.position.x > rightBound) Body.setPosition(b, { x: rightBound, y: b.position.y });
    const topOfFruit = b.position.y - b._fruit.radius;
    if(topOfFruit < topLineY + 2){
      Body.setPosition(b, { x: b.position.x, y: topLineY + 2 + b._fruit.radius });
      Body.setVelocity(b, { x: b.velocity.x * 0.3, y: Math.max(0.1, b.velocity.y * 0.2) });
    }
  }

  // -------------------------
  // Create / spawn fruits (use radiusForLevel)
  // -------------------------
  function createFruitAt(level, x, y){
    const r = radiusForLevel(level);
    // density proportional to area
    const areaScale = (r * r) / Math.max(1, Math.round((computeBoardRect().boardW * RADIUS_BASE_FRAC) ** 2));
    const baseDensity = 0.0018;
    const density = baseDensity * Math.max(1.0, areaScale * 1.12);
    const options = { restitution: 0.02, friction: 0.98, frictionAir: 0.06, density: density, label: 'fruit' };
    const b = Bodies.circle(x, y, r, options);
    const inertiaScale = 90;
    const inertia = (r * r) * inertiaScale;
    try { Body.setInertia(b, inertia); } catch(e){}
    b._fruit = { level, radius: r, wobble: 0 };
    World.add(world, b);
    bodies.push(b);
    Body.setVelocity(b, { x: (Math.random()-0.5)*0.04, y: -0.15 + Math.random()*0.22 });
    Body.setAngularVelocity(b, (Math.random()-0.5)*0.005);
    clampSpinForFruit(b);
    b._spawnTime = millis();
    clampBodyInsideBoard(b);
    return b;
  }

  function spawnFruit(screenX, forcedLevel){
    if(!isRunning || gameOver) return null;
    lastSpawnTime = millis();
    const { boardW, boardX, boardY } = computeBoardRect();
    const pad = 18;
    const spawnX = (typeof screenX === 'number') ? constrain(screenX, boardX + pad, boardX + boardW - pad) : boardX + boardW/2;

    // determine spawnLevel and immediately refill preview
    let spawnLevel;
    if(forcedLevel){
      spawnLevel = Math.min(forcedLevel, MAX_LEVEL);
    } else {
      spawnLevel = Math.min(nextPick || weightedPick(), SPAWN_MAX_LEVEL);
      // refill preview so the UI shows incoming fruit
      generateNextPick();
    }

    const r = radiusForLevel(spawnLevel);
    const spawnY = boardY + r + 6;

    // create
    const areaScale = (r * r) / Math.max(1, Math.round((computeBoardRect().boardW * RADIUS_BASE_FRAC) ** 2));
    const baseDensity = 0.0018;
    const density = baseDensity * Math.max(1.0, areaScale * 1.12);
    const options = { restitution: 0.02, friction: 0.98, frictionAir: 0.06, density: density, label: 'fruit' };
    const b = Bodies.circle(spawnX, spawnY, r, options);
    const inertiaScale = 90;
    const inertia = (r * r) * inertiaScale;
    try { Body.setInertia(b, inertia); } catch(e){}
    b._fruit = { level: spawnLevel, radius: r, wobble: 0 };
    b._spawnTime = millis();
    World.add(world, b);
    bodies.push(b);
    Body.setVelocity(b, { x: (Math.random()-0.5)*0.04, y: 0.28 + Math.random()*0.22 });
    Body.setAngularVelocity(b, (Math.random()-0.5) * 0.005);
    clampSpinForFruit(b);
    spawnParticles(spawnX, spawnY + 2, spawnLevel, 8);
    clampBodyInsideBoard(b);
    return b;
  }

  // -------------------------
  // Merge scheduling & collision
  // -------------------------
  function scheduleMergeCheck(A,B, delay = 50 + Math.floor(Math.random()*90)){
    const idA = A.id, idB = B.id;
    const lev = A._fruit.level;
    if(lev >= MAX_LEVEL) return;
    setTimeout(() => {
      const bodyA = bodies.find(b => b.id === idA);
      const bodyB = bodies.find(b => b.id === idB);
      if(!bodyA || !bodyB) return;
      if(!bodyA._fruit || !bodyB._fruit) return;
      if(bodyA._fruit.level !== lev || bodyB._fruit.level !== lev) return;
      const d = Vector.magnitude(Vector.sub(bodyA.position, bodyB.position));
      const minDist = (bodyA._fruit.radius + bodyB._fruit.radius) * MERGE_MIN_DIST;
      const relVel = Vector.magnitude(Vector.sub(bodyA.velocity, bodyB.velocity));
      if(d <= minDist && relVel <= 2.8){
        tryMergePair(bodyA, bodyB);
      }
    }, delay);
  }

  function onCollision(event){
    for(const pair of event.pairs){
      const A = pair.bodyA, B = pair.bodyB;
      if(!A._fruit || !B._fruit) continue;
      if(A.isStatic || B.isStatic) continue;
      if(A._fruit.level === B._fruit.level && A._fruit.level < MAX_LEVEL){
        const d = Vector.magnitude(Vector.sub(A.position, B.position));
        const minDist = (A._fruit.radius + B._fruit.radius) * MERGE_MIN_DIST;
        if(d <= minDist) scheduleMergeCheck(A,B);
      }
    }
  }

  // -------------------------
  // Merge action & scoring & achievements
  // -------------------------
  function tryMergePair(A,B){
    if(mergedThisStep.has(A.id) || mergedThisStep.has(B.id)) return;
    if(!A._fruit || !B._fruit) return;
    if(A._fruit.level >= MAX_LEVEL) return;
    mergedThisStep.add(A.id); mergedThisStep.add(B.id);
    if(!Composite.get(world, A.id, 'body') || !Composite.get(world, B.id, 'body')) return;

    const level = Math.min(A._fruit.level + 1, MAX_LEVEL);
    const pos = { x: (A.position.x + B.position.x)/2, y: (A.position.y + B.position.y)/2 };

    try{ World.remove(world, A); } catch(e){}
    try{ World.remove(world, B); } catch(e){}
    bodies = bodies.filter(bb => bb.id !== A.id && bb.id !== B.id);

    const nb = createFruitAt(level, pos.x, pos.y - 6);
    if(nb){
      Body.applyForce(nb, nb.position, { x: (Math.random()-0.5)*0.002, y: -0.012 - Math.random()*0.006 });
      nb._fruit.wobble = 1.2;
      clampSpinForFruit(nb);
    }

    spawnParticles(pos.x, pos.y, level, 24);
    playPop(level);
    recordMergeForChain();

    // scoring via helper
    const ptsFinal = scoreForMerge(level, chainCount);
    spawnFloatPop(pos.x, pos.y - 8, '+' + ptsFinal);
    score += ptsFinal;
    const scoreEl = el('score'); if(scoreEl) scoreEl.innerText = 'Score ' + score;
    pointsAccumSinceClear += ptsFinal;
    if(score > high){ high = score; localStorage.setItem('suika_physics_high', String(high)); const hEl = el('high'); if(hEl) hEl.innerText = high; }

    if(!clearUnlocked && score >= CLEAR_UNLOCK_SCORE){ clearUnlocked = true; clearAvailable = true; updateClearDom(); }
    if(clearUnlocked && !clearAvailable && pointsAccumSinceClear >= CLEAR_RECHARGE_POINTS){ clearAvailable = true; pointsAccumSinceClear = 0; updateClearDom(); }

    // Achievements: level 8 and final level 9 shoutouts
    if(level === 8){
      showAchievement('Almost there!', { subtitle: 'Level 8 reached', duration: 1900 });
    } else if(level === MAX_LEVEL){
      showAchievement('WATERMELON!', { subtitle: 'Final fruit achieved', duration: 2600, big:true });
    }
  }

  function clearMergeTrackers(){ mergedThisStep.clear(); }

  // -------------------------
  // Float pop & chain shout
  // -------------------------
  function spawnFloatPop(x,y,text){
    const node = document.createElement('div');
    node.className = 'float-pop';
    // inline minimal styling so it shows even if CSS missing
    node.style.position = 'absolute';
    node.style.left = `${x}px`;
    node.style.top = `${y}px`;
    node.style.transform = 'translate(-50%,0)';
    node.style.padding = '6px 8px';
    node.style.borderRadius = '10px';
    node.style.background = 'rgba(255,255,255,0.95)';
    node.style.boxShadow = '0 6px 18px rgba(0,0,0,0.12)';
    node.style.fontWeight = '700';
    node.style.color = '#111';
    node.style.pointerEvents = 'none';
    node.innerText = text;
    document.body.appendChild(node);
    requestAnimationFrame(() => {
      node.style.transition = 'transform 0.82s ease-out, opacity 0.82s ease-out';
      node.style.transform = 'translate(-50%,-36px) scale(1.02)';
      node.style.opacity = '0';
    });
    setTimeout(()=>{ if(node && node.parentNode) node.parentNode.removeChild(node); }, 900);
  }

  function recordMergeForChain(){
    const now = millis();
    if(lastMergeTime && (now - lastMergeTime) <= CHAIN_TIMEOUT && lastSpawnTime <= lastMergeTime){
      chainCount = (chainCount || 0) + 1;
    } else {
      chainCount = 1;
    }
    lastMergeTime = now;
    if(chainTimer) clearTimeout(chainTimer);
    chainTimer = setTimeout(() => {
      if(chainCount > 1) showChainShout(chainCount);
      chainCount = 0;
      chainTimer = null;
    }, CHAIN_TIMEOUT);
  }

  function showChainShout(n){
    if(!chainShoutEl){
      chainShoutEl = document.createElement('div');
      chainShoutEl.className = 'chain-shout';
      chainShoutEl.style.position = 'absolute';
      chainShoutEl.style.left = '50%';
      chainShoutEl.style.top = '8%';
      chainShoutEl.style.transform = 'translateX(-50%)';
      chainShoutEl.style.padding = '10px 18px';
      chainShoutEl.style.borderRadius = '999px';
      chainShoutEl.style.background = 'linear-gradient(90deg,#ffd27a,#ff9b9b)';
      chainShoutEl.style.boxShadow = '0 8px 24px rgba(0,0,0,0.12)';
      chainShoutEl.style.fontWeight = '800';
      chainShoutEl.style.color = '#3a1f00';
      chainShoutEl.style.opacity = '0';
      chainShoutEl.style.pointerEvents = 'none';
      document.body.appendChild(chainShoutEl);
    }
    chainShoutEl.innerText = `CHAIN x${n}!`;
    chainShoutEl.style.transition = 'opacity 0.18s ease-out, transform 0.28s ease-out';
    chainShoutEl.style.opacity = '1';
    chainShoutEl.style.transform = 'translateX(-50%) translateY(-6px)';
    setTimeout(()=>{ chainShoutEl.style.opacity = '0'; chainShoutEl.style.transform = 'translateX(-50%) translateY(-26px)'; }, 900);
  }

  // -------------------------
  // Next preview DOM & positioning
  // -------------------------
  function updateNextPreviewDom(){
    const np = el('nextPreview'); if(!np) return;
    const lvl = nextPick || 1;
    np.innerHTML = '';
    const img = document.createElement('img');
    img.alt = 'next fruit';
    img.src = `fruit${lvl}.png`;
    img.style.width = '64px';
    img.style.height = '64px';
    img.style.objectFit = 'contain';
    img.onerror = function(){ np.innerText = 'Lvl '+lvl; };
    np.appendChild(img);
    // minimal styling fallback
    np.style.position = 'absolute';
    np.style.zIndex = 999;
  }

  function positionNextPreview(){
    const np = el('nextPreview'); if(!np) return;
    const { boardW, boardX, boardY } = computeBoardRect();
    const gap = 12;
    const previewW = np.offsetWidth || 88;
    const previewH = np.offsetHeight || 88;
    let left = Math.round(boardX + boardW + gap);
    let top = Math.round(boardY + 12);
    if(left + previewW > window.innerWidth - 8){
      left = Math.round(boardX + (boardW - previewW)/2);
      top = Math.round(boardY - previewH - gap);
      if(top < 12) top = boardY + 12;
    }
    if(top < 64) top = Math.max(12, boardY + 12);
    np.style.left = left + 'px';
    np.style.top = top + 'px';
  }

  // -------------------------
  // Mobile hint & Clear UI
  // -------------------------
  function renderMobileMergeHint(){
    const container = document.getElementById('mobileMergeIcons');
    if(!container) return;
    container.innerHTML = '';
    for(let i=1;i<=Math.min(SPAWN_MAX_LEVEL, MAX_LEVEL); i++){
      const elIcon = document.createElement('div');
      elIcon.className = 'mobile-merge-icon';
      elIcon.style.display = 'inline-flex';
      elIcon.style.alignItems = 'center';
      elIcon.style.justifyContent = 'center';
      elIcon.style.marginRight = '8px';
      elIcon.style.width = '36px';
      elIcon.style.height = '36px';
      elIcon.style.borderRadius = '8px';
      elIcon.style.background = 'rgba(255,255,255,0.9)';
      const img = document.createElement('img');
      img.style.width = '22px'; img.style.height = '22px';
      img.alt = `lvl${i}`;
      img.src = `fruit${i}.png`;
      img.onerror = function(){ elIcon.innerText = i; };
      elIcon.appendChild(img);
      container.appendChild(elIcon);
    }
  }

  function updateClearDom(){
    const btn = el('btnClear'); if(!btn) return;
    const fill = el('chargeFill'); const label = el('chargeLabel');
    const pct = Math.min(1, pointsAccumSinceClear / CLEAR_RECHARGE_POINTS);
    if(fill) fill.style.width = `${Math.round(pct*100)}%`;
    if(label) {
      if(!clearUnlocked) label.innerText = `Unlock: ${CLEAR_UNLOCK_SCORE}`;
      else if(clearAvailable) label.innerText = 'Ready';
      else label.innerText = `Charge ${Math.round(pct*100)}%`;
    }
    if(!clearUnlocked){
      btn.classList.add('disabled'); btn.setAttribute('data-locked','true'); btn.innerText = 'Clear Small';
    } else {
      btn.removeAttribute('data-locked');
      if(clearAvailable){ btn.classList.remove('disabled'); btn.innerText = 'Clear Small'; }
      else { btn.classList.add('disabled'); btn.innerText = 'Clear (recharging)'; }
    }
  }

  function handleClearSmall(){
    if(!clearUnlocked || !clearAvailable) return;
    for(const b of bodies.slice()){
      if(!b || !b._fruit) continue;
      if(b._fruit.level <= 2){
        try{ World.remove(world, b); } catch(e){}
      }
    }
    bodies = bodies.filter(b => b && b._fruit && b._fruit.level > 2);
    clearAvailable = false;
    pointsAccumSinceClear = 0;
    clearUsed = true;
    updateClearDom();
    showAchievement('Cleared small fruits', { duration: 1400 });
  }

  // -------------------------
  // Achievements / Popups (inline styles)
  // -------------------------
  function showAchievement(title, opts = {}){
    const subtitle = opts.subtitle || '';
    const duration = opts.duration || 1800;
    const big = !!opts.big;
    const node = document.createElement('div');
    node.className = 'suika-achievement';
    node.style.position = 'fixed';
    node.style.left = '50%';
    node.style.top = '22%';
    node.style.transform = 'translateX(-50%) scale(0.92)';
    node.style.zIndex = 2000;
    node.style.padding = big ? '18px 26px' : '12px 18px';
    node.style.borderRadius = '14px';
    node.style.background = 'linear-gradient(180deg, rgba(255,255,255,0.98), rgba(250,250,255,0.98))';
    node.style.boxShadow = '0 18px 36px rgba(12,14,20,0.12)';
    node.style.textAlign = 'center';
    node.style.pointerEvents = 'none';
    node.style.opacity = '0';
    node.innerHTML = `<div style="font-weight:900; font-size:${big?'34px':'20px'}; letter-spacing:1px; color:${big?'#0b3d2e':'#24323a'}">${title}</div>${subtitle?`<div style="margin-top:6px; font-size:${big?'14px':'12px'}; color:#4b5a63">${subtitle}</div>`:''}`;
    document.body.appendChild(node);
    requestAnimationFrame(()=>{
      node.style.transition = 'opacity 0.18s ease-out, transform 0.36s cubic-bezier(.2,.9,.26,1)';
      node.style.opacity = '1';
      node.style.transform = 'translateX(-50%) translateY(-6px) scale(1)';
    });
    setTimeout(()=>{
      node.style.opacity = '0';
      node.style.transform = 'translateX(-50%) translateY(-36px) scale(0.98)';
      setTimeout(()=>{ if(node && node.parentNode) node.parentNode.removeChild(node); }, 420);
    }, duration);
  }

  // -------------------------
  // Merge flow UI, overlays
  // -------------------------
  function renderMergeRingDom(){
    const container = el('mergeRing'); if(!container) return;
    container.innerHTML = '';
    const title = document.createElement('div'); title.className = 'title'; title.innerText = 'Merge order';
    container.appendChild(title);
    const wrap = document.createElement('div'); wrap.className = 'levels';
    for(let i=1;i<=MAX_LEVEL;i++){
      const item = document.createElement('div');
      item.style.display='flex'; item.style.flexDirection='column'; item.style.alignItems='center';
      item.style.width='68px'; item.style.padding='6px'; item.style.borderRadius='10px';
      item.style.background = '#fff'; item.style.border = '1px solid rgba(0,0,0,0.04)';
      item.style.marginBottom = '8px';
      const img = document.createElement('img');
      img.style.width='44px'; img.style.height='44px'; img.style.objectFit='contain';
      img.src = `fruit${i}.png`;
      img.onerror = function(){ this.style.display='none'; };
      const fallback = document.createElement('div');
      fallback.style.fontSize='20px'; fallback.style.fontWeight='800'; fallback.style.marginTop='6px';
      fallback.innerText = ('Lvl'+i);
      item.appendChild(img);
      item.appendChild(fallback);
      const lbl = document.createElement('div'); lbl.style.fontSize='12px'; lbl.style.marginTop = '6px'; lbl.innerText = 'Lvl ' + i;
      item.appendChild(lbl);
      wrap.appendChild(item);
    }
    container.appendChild(wrap);
    const hint = document.createElement('div');
    hint.style.fontSize = '13px'; hint.style.color = 'var(--muted)'; hint.style.marginTop = '8px'; hint.style.textAlign = 'center';
    hint.innerText = 'Merge two same fruits to get the next level. Level ' + MAX_LEVEL + ' is terminal.';
    container.appendChild(hint);
  }

  function showStartOverlay(visible){ const ov = el('overlayStart'); if(!ov) return; ov.style.display = visible ? 'flex' : 'none'; }
  function closeStartOverlay(){ const ov = el('overlayStart'); if(ov) ov.style.display = 'none'; }

  function triggerGameOver(){
    gameOver = true;
    isRunning = false;
    try { engine.world.gravity.y = 0; } catch(e){}
    const ov = el('overlayGameOver'); if(ov) ov.style.display = 'flex';
    const gs = el('gameOverScore'); if(gs) gs.innerText = 'Score ' + score;
    showAchievement('Game Over', { subtitle: `Final score ${score}`, duration: 2200 });
  }

  function triggerFruitSupernova(){
    gameOver = true;
    isRunning = false;
    for(let i=0;i<250;i++){ spawnParticles(Math.random()*width, Math.random()*height, Math.floor(Math.random()*MAX_LEVEL)+1, 1); }
    for(const b of bodies){ try{ World.remove(world, b); }catch(e){} }
    bodies = [];
    const ov = el('overlayGameOver'); if(ov){
      ov.style.display = 'flex';
      const gs = el('gameOverScore'); if(gs) gs.innerText = 'Fruit Supernova! Score ' + score;
    } else {
      alert('Fruit Supernova! Score ' + score);
    }
  }

  // -------------------------
  // p5 hooks: preload, setup, resize, draw
  // -------------------------
  function preload(){
    for(let i=1;i<=MAX_LEVEL;i++){
      const fname = `fruit${i}.png`;
      FRUIT_IMAGES[i] = loadImage(fname, ()=>{}, ()=>{ FRUIT_IMAGES[i] = null; });
    }
  }
  window.preload = preload;

  function setup(){
    const cnv = createCanvas(window.innerWidth, window.innerHeight);
    cnv.style('display','block');
    pixelDensity(1); // avoid DPR scaling mismatch
    canvasElem = cnv.elt;
    if(canvasElem) canvasElem.style.touchAction = 'none';

    engine = Engine.create();
    world = engine.world;
    world.gravity.y = 1.06;

    createBounds();
    Events.on(engine, 'collisionStart', onCollision);

    // UI wiring
    const bReset = el('btnReset'), bClear = el('btnClear'), startBtn = el('startBtn'), restartBtn = el('restartBtn');
    if(bReset) bReset.addEventListener('click', startFromLanding);
    if(bClear) bClear.addEventListener('click', handleClearSmall);
    if(startBtn) startBtn.addEventListener('click', () => { closeStartOverlay(); startGame(); });
    if(restartBtn) restartBtn.addEventListener('click', () => { closeGameOver(); startGame(); });

    const md = el('mobileDrop'), mn = el('mobileNew');
    if(md) md.addEventListener('click', () => attemptSpawnAtScreenXFromClient(width/2));
    if(mn) mn.addEventListener('click', () => startFromLanding());

    const saved = localStorage.getItem('suika_physics_high');
    high = saved ? parseInt(saved) : 0;
    const hEl = el('high'); if(hEl) hEl.innerText = high;
    const sEl = el('score'); if(sEl) sEl.innerText = 'Score ' + score;

    // insert charge bar DOM next to Clear Small if not present
    const leftControls = document.querySelector('.left-controls');
    if(leftControls && !el('chargeBarWrap')){
      const wrap = document.createElement('div'); wrap.className = 'clear-wrap'; wrap.id = 'chargeBarWrap';
      wrap.style.display = 'flex'; wrap.style.alignItems = 'center'; wrap.style.gap = '8px';
      const bar = document.createElement('div'); bar.className = 'charge-bar'; bar.id = 'chargeBar';
      bar.style.width = '120px'; bar.style.height = '10px'; bar.style.background = 'rgba(0,0,0,0.06)'; bar.style.borderRadius = '8px';
      const fill = document.createElement('div'); fill.className = 'charge-fill'; fill.id = 'chargeFill'; fill.style.height = '100%'; fill.style.width = '0%'; fill.style.background = 'linear-gradient(90deg,#7be9a5,#4ec1ff)'; fill.style.borderRadius = '8px';
      bar.appendChild(fill);
      const label = document.createElement('div'); label.className = 'charge-label'; label.id = 'chargeLabel'; label.innerText = `Unlock: ${CLEAR_UNLOCK_SCORE}`;
      label.style.fontSize = '12px'; label.style.color = '#27323a';
      wrap.appendChild(bar); wrap.appendChild(label);
      leftControls.appendChild(wrap);
    }

    renderMergeRingDom();
    renderMobileMergeHint();

    // initial deterministic pick
    nextPick = 1;
    updateNextPreviewDom();
    positionNextPreview();
    updateClearDom();

    // store initial board rect
    previousBoardRect = computeBoardRect();

    showStartOverlay(true);
    frameRate(60);
    console.log('suika-physics.js loaded — ClearBar + chain shoutouts active');
  }

  function windowResized(){
    const oldRect = previousBoardRect || computeBoardRect();
    resizeCanvas(window.innerWidth, window.innerHeight);
    try{ World.remove(world, [ground, leftWall, rightWall]); }catch(e){}
    createBounds();
    const newRect = computeBoardRect();
    const sx = newRect.boardW / oldRect.boardW;
    const sy = sx;
    for(const b of bodies){
      if(!b || !b.position) continue;
      const relX = b.position.x - oldRect.boardX;
      const relY = b.position.y - oldRect.boardY;
      const newX = newRect.boardX + relX * sx;
      const newY = newRect.boardY + relY * sy;
      Body.setPosition(b, { x: newX, y: newY });
      if(b.velocity){
        Body.setVelocity(b, { x: b.velocity.x * sx, y: b.velocity.y * sy });
      }
      clampSpinForFruit(b);
    }
    positionNextPreview();
    previousBoardRect = newRect;
  }

  function draw(){
    background(242,248,252);
    Engine.update(engine, 1000/60);

    // dynamic gravity & spin clamping
    updateGravity();
    for (const b of bodies) clampSpinForFruit(b);

    clearMergeTrackers();
    updateParticles();

    const { boardW, boardX, boardY } = computeBoardRect();

    // board back
    push(); noStroke(); fill(250,253,255); rect(boardX - 18, boardY - 18, boardW + 36, boardW + 36, 20);
    stroke(210); strokeWeight(6); noFill(); rect(boardX - 14, boardY - 14, boardW + 28, boardW + 28, 18); pop();

    // draw bodies sorted by y
    const drawBodies = bodies.slice().filter(b => b && b._fruit && b.position).sort((a,b)=> (a.position.y - b.position.y));
    noStroke();
    for(const b of drawBodies){
      if(!b || !b.position || !b._fruit) continue;
      const x = b.position.x, y = b.position.y;
      const r = b._fruit.radius;

      push();
      drawingContext.shadowColor = "rgba(10,14,20,0.12)";
      drawingContext.shadowBlur = 14;
      fill(0,0,0,8);
      ellipse(x + 2, y + r*0.15, r*1.28, r*0.56);
      drawingContext.shadowBlur = 0;
      pop();

      const level = b._fruit.level;
      if(level === MAX_LEVEL){
        push();
        noFill();
        const glowSize = Math.min(r * 2.08, r * 2.6);
        stroke(255, 215, 100, 120);
        strokeWeight(Math.max(2, Math.round(r * 0.06)));
        ellipse(x, y, glowSize, glowSize);
        pop();
      }

      push();
      translate(x, y); rotate(b.angle);
      const wob = b._fruit.wobble || 0;
      scale(1 + wob*0.02, 1 - wob*0.02);
      const img = FRUIT_IMAGES[b._fruit.level];
      const visualDiameter = Math.max(6, Math.round(r * 2 * VISUAL_DIAMETER_FACTOR));
      if(img && img.width > 8){
        imageMode(CENTER);
        image(img, 0, 0, visualDiameter, visualDiameter);
      } else {
        textAlign(CENTER, CENTER);
        textSize(r * 0.92);
        text('?', 0, -2);
      }
      pop();

      if(b._fruit.wobble > 0) b._fruit.wobble = Math.max(0, b._fruit.wobble - 0.06);
      clampBodyInsideBoard(b);
    }

    drawParticles();

    // top dashed line
    push();
    stroke(170); strokeWeight(1);
    const lineY = boardY + 8; const seg = 12;
    for(let sx = boardX + 10; sx < boardX + boardW - 10; sx += seg*2) line(sx, lineY, Math.min(sx + seg, boardX + boardW - 10), lineY);
    pop();

    if(isRunning && !gameOver) drawShooterProjection(boardX, boardW, boardY);

    bodies = bodies.filter(b => {
      if(!b) return false;
      if(b.position.y > height + 900){
        try{ World.remove(world, b); } catch(e){}
        return false;
      }
      return true;
    });

    if(!gameOver){
      const terminalCount = bodies.reduce((acc, bb) => acc + ((bb && bb._fruit && bb._fruit.level === MAX_LEVEL) ? 1 : 0), 0);
      if(terminalCount >= 5){
        triggerFruitSupernova();
      }
    }

    // game over detection
    if(!gameOver){
      const now = millis();
      const topLineY = boardY + 8;
      for(const b of bodies){
        if(!b || !b.position || !b._fruit) continue;
        if(b._spawnTime && (now - b._spawnTime) < SPAWN_GRACE_MS) continue;
        const topOfFruit = b.position.y - b._fruit.radius;
        if(topOfFruit < topLineY + 2){
          triggerGameOver();
          break;
        }
        const speed = Math.sqrt((b.velocity.x||0)*(b.velocity.x||0) + (b.velocity.y||0)*(b.velocity.y||0));
        if(topOfFruit < topLineY + 8 && speed < 0.12){
          triggerGameOver();
          break;
        }
      }
    }

    positionNextPreview();
    updateClearDom();
  }

  // -------------------------
  // Shooter projection
  // -------------------------
  function drawShooterProjection(boardX, boardW, boardY){
    let px = mouseX;
    if(typeof touches !== 'undefined' && touches.length > 0 && touches[0] && typeof touches[0].x !== 'undefined'){
      px = clientToCanvasX(touches[0].x);
    }
    px = constrain(px, boardX + 16, boardX + boardW - 16);

    push();
    stroke(110, 90); strokeWeight(1);
    const segH = 10;
    for(let y = boardY + 6; y < boardY + boardW - 10; y += segH*2) line(px, y, px, Math.min(y + segH, boardY + boardW - 10));
    noStroke();
    fill(255,255,255,240);
    ellipse(px, boardY + 28, 30, 30);
    const lvl = nextPick || 1;
    push();
    translate(px, boardY + 28);
    const img = FRUIT_IMAGES[lvl];
    if(img && img.width > 8){
      imageMode(CENTER);
      image(img, 0, 0, 28, 28);
    } else {
      textAlign(CENTER, CENTER);
      textSize(16);
      fill(10);
      text('?', 0, 1);
    }
    pop();
    pop();
  }

  // -------------------------
  // Input mapping
  // -------------------------
  function clientToCanvasX(clientX){
    if(!canvasElem) return clientX;
    const rect = canvasElem.getBoundingClientRect();
    const x = (clientX - rect.left) * (canvas.width / rect.width);
    return x;
  }

  function attemptSpawnAtScreenXFromClient(clientX){
    const cx = clientToCanvasX(clientX);
    attemptSpawnAtScreenX(cx);
  }

  function attemptSpawnAtScreenX(screenX){
    if(millis() - lastSpawnAt < SPAWN_DEBOUNCE) return;
    lastSpawnAt = millis();
    const { boardW, boardX } = computeBoardRect();
    if(screenX < boardX + 4 || screenX > boardX + boardW - 4) return;
    const x = constrain(screenX, boardX + 16, boardX + boardW - 16);
    spawnFruit(x);
  }

  function mousePressed(){ if(!isRunning || gameOver) return; if(typeof touches !== 'undefined' && touches.length > 0) return; const { boardW, boardX } = computeBoardRect(); if(mouseX < boardX || mouseX > boardX + boardW) return; attemptSpawnAtScreenX(mouseX); }
  function touchStarted(){ if(!isRunning || gameOver) return; const tx = (touches && touches[0] && typeof touches[0].x !== 'undefined') ? touches[0].x : mouseX; attemptSpawnAtScreenXFromClient(tx); return false; }
  function keyPressed(){ if(!isRunning || gameOver) return; if(keyCode === 32) spawnFruit(width/2); }

  // -------------------------
  // Game control
  // -------------------------
  function startGame(){
    clearAllFruits();
    score = 0; const sEl = el('score'); if(sEl) sEl.innerText = 'Score ' + score;
    gameOver = false; isRunning = true;
    nextPick = 1; updateNextPreviewDom(); positionNextPreview();
    if(!clearUnlocked){ clearAvailable = false; pointsAccumSinceClear = 0; } else { if(!clearUsed) clearAvailable = true; pointsAccumSinceClear = 0; }
    updateClearDom();
    showStartOverlay(false);
    const gow = el('overlayGameOver'); if(gow) gow.style.display = 'none';
    try { engine.world.gravity.y = 1.06; } catch(e){}
  }

  function startFromLanding(){ showStartOverlay(true); isRunning = false; gameOver = false; const ov = el('overlayGameOver'); if(ov) ov.style.display = 'none'; if(!nextPick) nextPick = 1; updateNextPreviewDom(); positionNextPreview(); }
  function closeGameOver(){ const ov = el('overlayGameOver'); if(ov) ov.style.display = 'none'; }

  function clearAllFruits(){ for(const b of bodies){ try{ World.remove(world, b); }catch(e){} } bodies = []; }

  // -------------------------
  // Expose hooks
  // -------------------------
  window.preload = preload;
  window.setup = setup;
  window.draw = draw;
  window.windowResized = windowResized;
  window.mousePressed = mousePressed;
  window.touchStarted = touchStarted;
  window.keyPressed = keyPressed;

})();
