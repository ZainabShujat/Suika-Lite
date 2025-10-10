/* suika-physics.js
   Fixed full-file replacement:
   - tighter packing + image-overdraw for "touch" feel
   - bigger size progression (level1 much smaller)
   - fast merges + short randomized check
   - pop sound (lazy AudioContext) + particle burst on merge
   - spawn-inside-bin + grace period to avoid instant game-over
   - UI wiring kept (index.html expected)
*/

(() => {
  // Matter aliases
  const { Engine, World, Bodies, Body, Events, Composite, Vector } = Matter;

  // CONFIG
  const MAX_LEVEL = 7;
  const EMOJIS = {1:'🍒',2:'🍓',3:'🍇',4:'🍊',5:'🍋',6:'🍉',7:'🥭'}; // fallback icons
  const RADIUS_BASE = 15;          // much smaller base fruit (level 1)
  const RADIUS_GROWTH = 1.4;      // each level multiplies radius by this
  const IMAGE_DRAW_SCALE = 2.28;   // drawn image size relative to radius (>2 draws images larger than collider)
  const MERGE_MIN_DIST = 1.01;     // permissive overlap threshold
  const MERGE_DELAY_MIN = 30;      // ms
  const MERGE_DELAY_MAX = 80;      // ms
  const SPAWN_GRACE_MS = 600;      // ignore newly-spawned fruits for this long for game-over checks
  const GAME_OVER_LINE_Y_RATIO = 0.12;

  // scoring table (triangular-ish)
  const POINTS = {1:1,2:3,3:6,4:10,5:15,6:21,7:28};

  // runtime state
  let FRUIT_IMAGES = {};
  let engine, world;
  let bodies = [];
  let ground, leftWall, rightWall;
  let score = 0, high = 0;
  let isRunning = false, gameOver = false;
  let mergedThisStep = new Set();
  function chooseSpawnLevel() {
  // Weighted random 1–3 spawn logic (Suika-like)
  // Normalized so sum of weights == 1
  const weights = [0.55, 0.30, 0.15]; // adjust to taste
  const levels  = [1, 2, 3];
  let total = 0;
  for (let w of weights) total += w;
  const r = Math.random() * total;
  let cumulative = 0;
  for (let i = 0; i < weights.length; i++) {
    cumulative += weights[i];
    if (r < cumulative) return levels[i];
  }
  return levels[levels.length - 1];
}


  // small particle system for merges
  let particles = [];
  function spawnParticles(x,y,color='#ff9c9c'){
    for(let i=0;i<12;i++){
      const ang = Math.random()*Math.PI*2;
      const speed = 1.4 + Math.random()*1.4;
      particles.push({
        x, y,
        vx: Math.cos(ang)*speed,
        vy: Math.sin(ang)*speed - 0.6,
        life: 26 + Math.floor(Math.random()*8),
        col: color
      });
    }
  }
  function updateParticles(){
    for(const p of particles){
      p.x += p.vx; p.y += p.vy; p.vy += 0.12; p.life--;
    }
    particles = particles.filter(p => p.life > 0);
  }
  function drawParticles(){
    noStroke();
    for(const p of particles){
      const alpha = map(p.life, 0, 34, 0, 1);
      fill(p.col);
      drawingContext.globalAlpha = alpha;
      circle(p.x, p.y, 3 + (p.life/12));
      drawingContext.globalAlpha = 1;
    }
  }

  // lazy AudioContext (resume on first user gesture)
  let audioCtx = null;
  function ensureAudio(){
    if(!audioCtx){
      audioCtx = new (window.AudioContext || window.webkitAudioContext)();
    }
    if(audioCtx.state === 'suspended') audioCtx.resume().catch(()=>{});
  }
  function playPop(){
    try{
      ensureAudio();
      const t0 = audioCtx.currentTime;
      const o = audioCtx.createOscillator();
      const g = audioCtx.createGain();
      o.type = 'triangle';
      o.frequency.setValueAtTime(560 + Math.random()*60, t0);
      g.gain.setValueAtTime(0.16, t0);
      g.gain.exponentialRampToValueAtTime(0.001, t0 + 0.22);
      o.connect(g); g.connect(audioCtx.destination);
      o.start(t0); o.stop(t0 + 0.22);
    }catch(e){
      // silent fail on weird browsers
      console.warn('Audio pop failed', e);
    }
  }

  // helper: DOM get
  function el(id){ return document.getElementById(id); }

  // radius calculation (float allowed)
  function radiusForLevel(l){
    return RADIUS_BASE * Math.pow(RADIUS_GROWTH, l - 1);
  }

  // preload images (p5 preload)
  function preload(){
    for(let i=1;i<=MAX_LEVEL;i++){
      const fname = `fruit${i}.png`;
      // loadImage success/fail handlers: if fail, fallback to null (draw emoji)
      FRUIT_IMAGES[i] = loadImage(fname, ()=>{}, ()=>{ FRUIT_IMAGES[i] = null; });
    }
  }
  window.preload = preload;

  // compute board rectangle used consistently by draw & bounds
  function computeBoardRect(){
    const boardW = Math.min(window.innerWidth * 0.78, window.innerHeight * 0.78);
    const boardX = (window.innerWidth - boardW) / 2;
    const boardY = (window.innerHeight - boardW) / 2;
    return { boardW, boardX, boardY };
  }

  // create static boundaries aligned to board
  function createBounds(){
    try{
      if(ground) World.remove(world, ground);
      if(leftWall) World.remove(world, leftWall);
      if(rightWall) World.remove(world, rightWall);
    }catch(e){}
    const { boardW, boardX, boardY } = computeBoardRect();
    const thickness = Math.max(120, boardW * 0.12);

    ground = Bodies.rectangle(boardX + boardW/2, boardY + boardW + thickness/2,
      boardW + thickness*2, thickness, { isStatic:true, restitution:0.05, friction:0.94 });
    leftWall = Bodies.rectangle(boardX - thickness/2, boardY + boardW/2,
      thickness, boardW + thickness*2, { isStatic:true, restitution:0.02, friction:0.94 });
    rightWall = Bodies.rectangle(boardX + boardW + thickness/2, boardY + boardW/2,
      thickness, boardW + thickness*2, { isStatic:true, restitution:0.02, friction:0.94 });

    World.add(world, [ground, leftWall, rightWall]);
  }

  // create fruit at arbitrary position (used for merged spawn)
  function createFruitAt(level, x, y){
    const r = radiusForLevel(level);
    const b = Bodies.circle(x, y, r, {
      restitution: 0.05, friction: 0.92, density: 0.0018 + level*0.0006, label: 'fruit'
    });
    b._fruit = { level, radius: r, wobble: 0 };
    World.add(world, b);
    bodies.push(b);
    Body.setVelocity(b, { x: (Math.random()-0.5)*0.08, y: -0.6 + Math.random()*0.6 });
    Body.setAngularVelocity(b, (Math.random()-0.5)*0.03);
    b._spawnTime = millis();
    return b;
  }

  // spawn fruit from player tap (spawns inside top of container)
  function spawnFruit(screenX, level=1){
    if(!isRunning || gameOver) return null;
    const { boardW, boardX, boardY } = computeBoardRect();
    const pad = 28;
    const x = constrain(screenX, boardX + pad, boardX + boardW - pad);
    const r = radiusForLevel(level);
    const spawnY = boardY + r + 4; // just inside top edge
    const b = Bodies.circle(x, spawnY, r, {
      restitution: 0.05, friction: 0.92, density: 0.0018 + level*0.0006, label: 'fruit'
    });
    b._fruit = { level, radius: r, wobble: 0 };
    b._spawnTime = millis();
    World.add(world, b);
    bodies.push(b);
    Body.setVelocity(b, { x: (Math.random()-0.5)*0.08, y: 0.7 + Math.random()*0.42 });
    Body.setAngularVelocity(b, (Math.random()-0.5)*0.03);
    return b;
  }

  // merge scheduling: short randomized re-check to avoid mid-air accidental merges but keep snappy feel
  function scheduleMergeCheck(A, B, delay = MERGE_DELAY_MIN + Math.random()*(MERGE_DELAY_MAX - MERGE_DELAY_MIN)){
    const idA = A.id, idB = B.id;
    const lev = A._fruit.level;
    setTimeout(() => {
      const bodyA = bodies.find(b => b.id === idA);
      const bodyB = bodies.find(b => b.id === idB);
      if(!bodyA || !bodyB) return;
      if(!bodyA._fruit || !bodyB._fruit) return;
      if(bodyA._fruit.level !== lev || bodyB._fruit.level !== lev) return;
      const d = Vector.magnitude(Vector.sub(bodyA.position, bodyB.position));
      const minDist = (bodyA._fruit.radius + bodyB._fruit.radius) * MERGE_MIN_DIST;
      const relVel = Vector.magnitude(Vector.sub(bodyA.velocity, bodyB.velocity));
      if(d < minDist && relVel <= 3.2){
        tryMergePair(bodyA, bodyB);
      }
    }, delay);
  }

  // collision handler
  function onCollision(event){
    for(const pair of event.pairs){
      const A = pair.bodyA, B = pair.bodyB;
      if(!A._fruit || !B._fruit) continue;
      if(A.isStatic || B.isStatic) continue;
      if(A._fruit.level === B._fruit.level){
        const d = Vector.magnitude(Vector.sub(A.position, B.position));
        const minDist = (A._fruit.radius + B._fruit.radius) * MERGE_MIN_DIST;
        if(d < minDist){
          scheduleMergeCheck(A, B);
        }
      }
    }
  }

  // perform merge (remove both, create new-level fruit at contact point)
  function tryMergePair(A, B){
    if(mergedThisStep.has(A.id) || mergedThisStep.has(B.id)) return;
    mergedThisStep.add(A.id); mergedThisStep.add(B.id);

    // ensure bodies still exist in world
    if(!Composite.get(world, A.id, 'body') || !Composite.get(world, B.id, 'body')) return;

    const newLevel = Math.min(A._fruit.level + 1, MAX_LEVEL);
    const pos = { x: (A.position.x + B.position.x)/2, y: (A.position.y + B.position.y)/2 };

    try{ World.remove(world, A); }catch(e){}
    try{ World.remove(world, B); }catch(e){}
    bodies = bodies.filter(bb => bb.id !== A.id && bb.id !== B.id);

    // create new fruit exactly at pos (slight pop)
    const nb = createFruitAt(newLevel, pos.x, pos.y - 4);
    if(nb) Body.applyForce(nb, nb.position, { x: (Math.random()-0.5)*0.002, y: -0.008 - Math.random()*0.004 });

    // score
    const pts = POINTS[newLevel] || (10 * newLevel);
    score += pts;
    el('score').innerText = 'Score ' + score;
    if(score > high){ high = score; localStorage.setItem('suika_physics_high', String(high)); el('high').innerText = high; }

    // pop & particles
    playPop();
    spawnParticles(pos.x, pos.y, '#ffb3b3');
  }

  function clearMergeTrackers(){ mergedThisStep.clear(); }

  // draw helpers: rule panel (display goal sequence)
  const RULE_SEQUENCE = [1,2,3,4,5,6,7];
  function renderRulePanel(){
    const panel = el('flowList');
    if(!panel) return;
    panel.innerHTML = '';
    const note = document.createElement('div');
    note.className = 'flowSmall';
    note.innerText = 'Merge two identical fruits to produce the next one (goal: big fruit).';
    panel.appendChild(note);

    const row = document.createElement('div');
    row.style.display = 'flex'; row.style.alignItems='center'; row.style.gap='8px'; row.style.marginTop='8px';
    for(let i=0;i<RULE_SEQUENCE.length;i++){
      const lvl = RULE_SEQUENCE[i];
      const card = document.createElement('div');
      card.style.display='flex'; card.style.flexDirection='column'; card.style.alignItems='center';
      card.style.width='48px'; card.style.padding='6px'; card.style.borderRadius='8px';
      card.style.background = '#fbfcfd'; card.style.border = '1px solid rgba(0,0,0,0.04)';
      const img = document.createElement('img');
      img.style.width='36px'; img.style.height='36px'; img.style.objectFit='contain';
      if(FRUIT_IMAGES[lvl]) img.src = `fruit${lvl}.png`; else img.src = 'data:image/svg+xml;utf8,' + encodeURIComponent(`<svg xmlns="http://www.w3.org/2000/svg" width="36" height="36"><text x="50%" y="50%" dominant-baseline="middle" text-anchor="middle" font-size="26">${EMOJIS[lvl]||'?'}</text></svg>`);
      card.appendChild(img);
      const lbl = document.createElement('div'); lbl.style.fontSize='12px'; lbl.style.marginTop='4px'; lbl.innerText = 'Lvl ' + lvl;
      card.appendChild(lbl);
      row.appendChild(card);
      if(i < RULE_SEQUENCE.length - 1){
        const arr = document.createElement('div'); arr.style.fontSize='18px'; arr.style.color='#c8cdd3'; arr.style.margin='0 4px'; arr.innerText='→';
        row.appendChild(arr);
      }
    }
    panel.appendChild(row);
    const hint = document.createElement('div'); hint.className='flowSmall'; hint.style.marginTop='8px';
    hint.innerText = 'Points per merge: ' + RULE_SEQUENCE.map(l => POINTS[l]).join(' / ');
    panel.appendChild(hint);
  }

  // P5 setup/draw & UI wiring
  function setup(){
    const cnv = createCanvas(window.innerWidth, window.innerHeight);
    cnv.style('display','block');
    engine = Engine.create(); world = engine.world; world.gravity.y = 1.02;

    createBounds();
    Events.on(engine, 'collisionStart', onCollision);

        // UI attach (defensive) — REPLACE the existing UI wiring block with this
    const bReset = el('btnReset'), bClear = el('btnClear'), startBtn = el('startBtn'), restartBtn = el('restartBtn');
    if(bReset) bReset.addEventListener('click', () => {
      // go to landing overlay but keep things ready to start
      showStartOverlay(true);
      isRunning = false;
      gameOver = false;
    });
    if(bClear) bClear.addEventListener('click', () => { clearAllFruits(); });
    if(startBtn) startBtn.addEventListener('click', () => {
      // start from landing: hide landing and begin the game
      showStartOverlay(false);
      startGame();
    });
    if(restartBtn) restartBtn.addEventListener('click', () => {
      // Play Again should immediately start a fresh game (no reload)
      // hide game over overlay, reset state, and begin
      try { el('overlayGameOver').style.display = 'none'; } catch(e){}
      showStartOverlay(false);
      startGame();
    });

    // highscore
    const saved = localStorage.getItem('suika_physics_high');
    high = saved ? parseInt(saved) : 0; el('high').innerText = high;
    el('score').innerText = 'Score ' + score;

    renderRulePanel();
    showStartOverlay(true);
    frameRate(60);
    console.log('suika-physics.js – fixed build loaded');
  }

  function windowResized(){
    resizeCanvas(window.innerWidth, window.innerHeight);
    try{ World.remove(world, [ground, leftWall, rightWall]); }catch(e){}
    createBounds();
  }

  function draw(){
    background(246,247,249);
    Engine.update(engine, 1000/60);
    clearMergeTrackers();

    // board
    const { boardW, boardX, boardY } = computeBoardRect();
    push();
    noStroke();
    fill(236,241,246);
    rect(boardX - 16, boardY - 16, boardW + 32, boardW + 32, 20);
    stroke(208); strokeWeight(6); noFill();
    rect(boardX - 12, boardY - 12, boardW + 24, boardW + 24, 18);
    pop();

    // fruits render
    noStroke();
    for(const b of bodies){
      if(!b || !b.position || !b._fruit) continue;
      const x = b.position.x, y = b.position.y;
      const r = b._fruit.radius;

      // shadow
      push();
      drawingContext.shadowColor = "rgba(0,0,0,0.18)";
      drawingContext.shadowBlur = 12;
      fill(0,0,0,8);
      ellipse(x + 2, y + r*0.15, r*1.35, r*0.6);
      drawingContext.shadowBlur = 0;
      pop();

      // image rotated (draw slightly larger than physics radius to hide tiny collider gaps)
      push();
      translate(x, y);
      rotate(b.angle);
      const wob = b._fruit.wobble || 0;
      scale(1 + wob*0.02, 1 - wob*0.02);

      const img = FRUIT_IMAGES[b._fruit.level];
      if(img && img.width > 8){
        imageMode(CENTER);
        image(img, 0, 0, r * IMAGE_DRAW_SCALE, r * IMAGE_DRAW_SCALE);
      } else {
        textAlign(CENTER, CENTER);
        textSize(r * 1.05);
        text(EMOJIS[b._fruit.level] || '?', 0, -2);
      }
      pop();

      if(b._fruit.wobble > 0) b._fruit.wobble = Math.max(0, b._fruit.wobble - 0.02);
    }

    // particles
    updateParticles(); drawParticles();

    // top game-over line
    push();
    stroke(200); strokeWeight(1);
    const lineY = height * GAME_OVER_LINE_Y_RATIO;
    line(12, lineY, width - 12, lineY);
    noStroke();
    fill(100);
    textSize(12);
    textAlign(LEFT, CENTER);
    text('Game over if fruit crosses this line', 16, lineY - 10);
    pop();

    // cleanup very-offscreen bodies
    bodies = bodies.filter(b => {
      if(!b) return false;
      if(b.position.y > height + 800){
        try{ World.remove(world, b); } catch(e){}
        return false;
      }
      return true;
    });

    // game-over detection with spawn grace
    if(!gameOver){
      const now = millis();
      for(const b of bodies){
        if(!b || !b.position || !b._fruit) continue;
        if(b._spawnTime && (now - b._spawnTime) < SPAWN_GRACE_MS) continue;
        if((b.position.y - b._fruit.radius) < lineY){
          triggerGameOver();
          break;
        }
      }
    }
  }

  // input: tap anywhere inside bin (suika-like)
  function mousePressed(){
    if(!isRunning || gameOver) return;
    const { boardW, boardX, boardY } = computeBoardRect();
    // require click inside horizontal bounds of board
    if(mouseX < boardX || mouseX > boardX + boardW) return;
    // allow vertical margin slightly above top (for comfortable tapping)
    const x = constrain(mouseX, boardX + 24, boardX + boardW - 24);
    spawnFruit(x, 1);
  }
  function keyPressed(){
    if(!isRunning || gameOver) return;
    if(keyCode === 32) spawnFruit(width / 2, 1);
  }

  // UI helpers
  function clearAllFruits(){
    for(const b of bodies) try{ World.remove(world, b); }catch(e){}
    bodies = [];
  }

  function showStartOverlay(visible){
    const ov = el('overlayStart');
    if(!ov) return;
    ov.style.display = visible ? 'flex' : 'none';
  }

  function startGame(){
    // ensure audio context resumes on start gesture
    try{ ensureAudio(); }catch(e){}
    clearAllFruits();
    score = 0; el('score').innerText = 'Score ' + score;
    gameOver = false; isRunning = true;
    renderRulePanel();
    showStartOverlay(false);
    const go = el('overlayGameOver'); if(go) go.style.display = 'none';
  }

  function startFromLanding(){
    showStartOverlay(true); isRunning = false; gameOver = false;
  }

  function triggerGameOver(){
    gameOver = true; isRunning = false;
    const ov = el('overlayGameOver'); if(ov) ov.style.display = 'flex';
    const gs = el('gameOverScore'); if(gs) gs.innerText = 'Score ' + score;
    const gt = el('gameOverTitle'); if(gt) gt.innerText = 'Game Over';
  }

  // expose p5 hooks
  window.preload = preload;
  window.setup = setup;
  window.draw = draw;
  window.windowResized = windowResized;
  window.mousePressed = mousePressed;
  window.keyPressed = keyPressed;

  // done IIFE
})(); 
