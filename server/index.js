const express = require('express');
const http = require('http');
const path = require('path');
const { WebSocketServer } = require('ws');
const { v4: uuidv4 } = require('uuid');

const CELL = 64;
const MAP_W = 32;
const MAP_H = 32;
const ATTACK = 0;
const DEFEND = 1;
const SCORE_LIMIT = 30;
const TICK_MS = 50;
const PLAYER_R = 14;
const HEADSHOT_ANGLE = 0.03;
const MOVE_SPEED = 3.2;
const BOT_COUNT = 6;
const MAX_HUMANS = 10;

const WEAPONS = {
  m4a1: { dmg: 28, spread: 0.018, range: 900, rpm: 600 },
  pistol: { dmg: 22, spread: 0.035, range: 450, rpm: 400 },
  dmr: { dmg: 55, spread: 0.008, range: 1100, rpm: 180 },
};

function getDefaultMap() {
  const N = 32;
  const map = Array.from({ length: N }, () => Array(N).fill(0));

  for (let i = 0; i < N; i++) {
    map[0][i] = 1;
    map[N - 1][i] = 1;
    map[i][0] = 1;
    map[i][N - 1] = 1;
  }

  const fill = (x1, y1, x2, y2, t) => {
    for (let y = y1; y <= y2; y++) {
      for (let x = x1; x <= x2; x++) {
        map[y][x] = t;
      }
    }
  };

  fill(10, 10, 21, 10, 1);
  fill(10, 21, 21, 21, 1);
  fill(10, 11, 10, 20, 1);
  fill(21, 11, 21, 20, 1);
  map[15][10] = 4;
  map[16][10] = 4;
  map[15][21] = 4;
  map[16][21] = 4;
  map[10][15] = 4;
  map[10][16] = 4;
  map[21][15] = 4;
  map[21][16] = 4;

  fill(3, 8, 3, 23, 2);
  fill(6, 8, 6, 23, 2);
  fill(N - 4, 8, N - 4, 23, 2);
  fill(N - 7, 8, N - 7, 23, 2);

  for (let y = 12; y <= 19; y++) {
    if (y !== 15 && y !== 16) {
      map[y][8] = 1;
      map[y][N - 9] = 1;
    }
  }

  const crates = [
    [14, 14], [17, 14], [14, 17], [17, 17], [15, 15], [16, 16],
    [13, 15], [18, 15], [15, 8], [16, 8], [15, N - 9], [16, N - 9],
    [12, 12], [19, 12], [12, 19], [19, 19],
  ];
  crates.forEach(([x, y]) => {
    map[y][x] = 3;
  });

  for (let y = 11; y <= 20; y++) {
    for (let x = 1; x <= 5; x++) map[y][x] = 0;
    for (let x = N - 6; x <= N - 2; x++) map[y][x] = 0;
  }

  map[15][5] = 0;
  map[16][5] = 0;
  map[15][N - 6] = 0;
  map[16][N - 6] = 0;

  return map;
}

function cloneMap(map) {
  return map.map((row) => row.slice());
}

function isSolid(cell) {
  return cell === 1 || cell === 2 || cell === 3;
}

function spawnForTeam(team) {
  const midY = (MAP_H / 2) * CELL;
  if (team === ATTACK) {
    return { x: 2.5 * CELL, y: midY, angle: 0 };
  }
  return { x: (MAP_W - 2.5) * CELL, y: midY, angle: Math.PI };
}

const app = express();
const server = http.createServer(app);
const wss = new WebSocketServer({ server });

app.use(express.static(path.join(__dirname, '../client')));

const wallState = cloneMap(getDefaultMap());
const players = new Map();
const bots = new Map();
let scores = { [ATTACK]: 0, [DEFEND]: 0 };
let killFeed = [];
let gameOver = false;

function wallAt(mx, my) {
  if (my < 0 || my >= MAP_H || mx < 0 || mx >= MAP_W) return 1;
  return wallState[my][mx];
}

function castRay(ox, oy, angle, maxDist) {
  const sin = Math.sin(angle);
  const cos = Math.cos(angle);
  let dist = 0;
  let mx = Math.floor(ox / CELL);
  let my = Math.floor(oy / CELL);
  const deltaDistX = Math.abs(1 / (cos || 1e-9));
  const deltaDistY = Math.abs(1 / (sin || 1e-9));
  let stepX;
  let stepY;
  let sideDistX;
  let sideDistY;

  if (cos < 0) {
    stepX = -1;
    sideDistX = (ox / CELL - mx) * deltaDistX;
  } else {
    stepX = 1;
    sideDistX = (mx + 1 - ox / CELL) * deltaDistX;
  }
  if (sin < 0) {
    stepY = -1;
    sideDistY = (oy / CELL - my) * deltaDistY;
  } else {
    stepY = 1;
    sideDistY = (my + 1 - oy / CELL) * deltaDistY;
  }

  let hitMx = mx;
  let hitMy = my;
  let hitType = 0;

  while (dist < maxDist) {
    if (sideDistX < sideDistY) {
      sideDistX += deltaDistX;
      mx += stepX;
    } else {
      sideDistY += deltaDistY;
      my += stepY;
    }
    const cell = wallAt(mx, my);
    if (isSolid(cell)) {
      hitMx = mx;
      hitMy = my;
      hitType = cell;
      const side = sideDistX < sideDistY ? 0 : 1;
      dist = side === 0 ? sideDistX - deltaDistX : sideDistY - deltaDistY;
      break;
    }
    dist = Math.min(sideDistX, sideDistY);
  }

  return {
    dist: Math.max(0, dist * CELL),
    mx: hitMx,
    my: hitMy,
    type: hitType,
  };
}

function canMoveAt(nx, ny) {
  const r = PLAYER_R;
  const corners = [
    [nx - r, ny - r],
    [nx + r, ny - r],
    [nx - r, ny + r],
    [nx + r, ny + r],
  ];
  for (const [cx, cy] of corners) {
    const mx = Math.floor(cx / CELL);
    const my = Math.floor(cy / CELL);
    if (mx < 0 || my < 0 || mx >= MAP_W || my >= MAP_H) return false;
    if (isSolid(wallAt(mx, my))) return false;
  }
  return true;
}

function teamCounts() {
  let atk = 0;
  let def = 0;
  for (const p of players.values()) {
    if (p.team === ATTACK) atk++;
    else def++;
  }
  for (const b of bots.values()) {
    if (b.team === ATTACK) atk++;
    else def++;
  }
  return { atk, def };
}

function assignTeam() {
  const { atk, def } = teamCounts();
  return atk <= def ? ATTACK : DEFEND;
}

function createEntity(id, name, team, isBot = false) {
  const spawn = spawnForTeam(team);
  return {
    id,
    name,
    team,
    x: spawn.x,
    y: spawn.y,
    angle: spawn.angle,
    health: 100,
    alive: true,
    weapon: 'm4a1',
    aiming: false,
    kills: 0,
    deaths: 0,
    respawnAt: 0,
    isBot,
    aiTimer: 40 + Math.random() * 40,
    aiTarget: null,
    shootCooldown: 0,
    ws: null,
  };
}

function respawnEntity(p) {
  const spawn = spawnForTeam(p.team);
  p.x = spawn.x;
  p.y = spawn.y;
  p.angle = spawn.angle;
  p.health = 100;
  p.alive = true;
  p.respawnAt = 0;
}

function initBots() {
  bots.clear();
  for (let i = 0; i < BOT_COUNT; i++) {
    const team = i % 2 === 0 ? DEFEND : ATTACK;
    const id = `bot-${i}`;
    bots.set(id, createEntity(id, `Operative ${i + 1}`, team, true));
  }
}

function allCombatants() {
  return [...players.values(), ...bots.values()];
}

function publicEntity(p) {
  return {
    id: p.id,
    name: p.name,
    team: p.team,
    x: p.x,
    y: p.y,
    angle: p.angle,
    health: p.health,
    alive: p.alive,
    weapon: p.weapon,
    aiming: p.aiming,
    kills: p.kills,
    deaths: p.deaths,
    isBot: !!p.isBot,
  };
}

function publicPlayers() {
  return allCombatants().map(publicEntity);
}

function broadcast(msg, except) {
  const data = JSON.stringify(msg);
  for (const [, p] of players) {
    if (p.ws && p.ws.readyState === 1 && p.ws !== except) {
      p.ws.send(data);
    }
  }
}

function broadcastAll(msg) {
  const data = JSON.stringify(msg);
  for (const [, p] of players) {
    if (p.ws && p.ws.readyState === 1) p.ws.send(data);
  }
}

function sendInit(ws, id) {
  ws.send(
    JSON.stringify({
      type: 'init',
      id,
      team: players.get(id).team,
      map: wallState,
      players: publicPlayers(),
      scores,
      scoreLimit: SCORE_LIMIT,
      killFeed,
      gameOver,
    })
  );
}

function resetRound() {
  const fresh = cloneMap(getDefaultMap());
  for (let y = 0; y < MAP_H; y++) {
    for (let x = 0; x < MAP_W; x++) {
      wallState[y][x] = fresh[y][x];
    }
  }
  scores = { [ATTACK]: 0, [DEFEND]: 0 };
  killFeed = [];
  gameOver = false;
  for (const e of allCombatants()) {
    respawnEntity(e);
  }
}

function handleShoot(shooterId, angle, weaponKey) {
  const shooter = players.get(shooterId) || bots.get(shooterId);
  if (!shooter || !shooter.alive || gameOver) return;

  const wpn = WEAPONS[weaponKey] || WEAPONS.m4a1;
  const spread = wpn.spread * (shooter.aiming ? 0.35 : 1);
  const rayAngle = angle + (Math.random() - 0.5) * spread * 2;

  let best = null;
  let bestDist = Infinity;

  for (const target of allCombatants()) {
    if (target.id === shooterId || !target.alive || target.team === shooter.team) continue;
    const dx = target.x - shooter.x;
    const dy = target.y - shooter.y;
    const dist = Math.hypot(dx, dy);
    if (dist > wpn.range) continue;
    let ang = Math.atan2(dy, dx) - rayAngle;
    while (ang > Math.PI) ang -= Math.PI * 2;
    while (ang < -Math.PI) ang += Math.PI * 2;
    const hitRadius = Math.atan2(PLAYER_R + 8, dist);
    if (Math.abs(ang) > hitRadius) continue;

    const wallHit = castRay(shooter.x, shooter.y, Math.atan2(dy, dx), dist);
    if (wallHit.dist < dist - 8) continue;

    if (dist < bestDist) {
      bestDist = dist;
      best = target;
    }
  }

  const wallRay = castRay(shooter.x, shooter.y, rayAngle, wpn.range);
  if (wallRay.type === 3) {
    wallState[wallRay.my][wallRay.mx] = 0;
    broadcastAll({ type: 'wallBreak', mx: wallRay.mx, my: wallRay.my });
  }

  if (!best) return;

  const toTarget = Math.atan2(best.y - shooter.y, best.x - shooter.x);
  let angDiff = toTarget - rayAngle;
  while (angDiff > Math.PI) angDiff -= Math.PI * 2;
  while (angDiff < -Math.PI) angDiff += Math.PI * 2;
  const headshot = Math.abs(angDiff) < HEADSHOT_ANGLE;
  const dmg = headshot ? wpn.dmg * 2.5 : wpn.dmg;

  best.health = Math.max(0, best.health - dmg);
  broadcastAll({
    type: 'hit',
    targetId: best.id,
    shooterId: shooter.id,
    damage: dmg,
    headshot,
    health: best.health,
  });

  if (best.health <= 0 && best.alive) {
    best.alive = false;
    best.deaths++;
    shooter.kills++;
    scores[shooter.team]++;
    const entry = {
      killer: shooter.name,
      victim: best.name,
      weapon: weaponKey,
      headshot,
      team: shooter.team,
      t: Date.now(),
    };
    killFeed.unshift(entry);
    if (killFeed.length > 8) killFeed.pop();

    broadcastAll({ type: 'kill', ...entry, killerId: shooter.id, victimId: best.id });
    best.respawnAt = Date.now() + 5000;

    if (scores[shooter.team] >= SCORE_LIMIT) {
      gameOver = true;
      broadcastAll({ type: 'gameOver', winner: shooter.team, scores });
      setTimeout(resetRound, 8000);
    }
  }
}

function botShoot(bot) {
  if (bot.shootCooldown > 0 || !bot.alive || gameOver) return;
  const wpn = WEAPONS[bot.weapon] || WEAPONS.m4a1;
  bot.shootCooldown = Math.ceil(60 / (wpn.rpm / 60));
  handleShoot(bot.id, bot.angle + (Math.random() - 0.5) * 0.08, bot.weapon);
}

function updateBots() {
  const centerX = (MAP_W / 2) * CELL;
  const centerY = (MAP_H / 2) * CELL;

  for (const bot of bots.values()) {
    if (!bot.alive) continue;

    bot.aiTimer -= 1;
    if (bot.shootCooldown > 0) bot.shootCooldown -= 1;
    if (bot.strafeDir === undefined) bot.strafeDir = 1;
    if (bot.patrolAngle === undefined) bot.patrolAngle = Math.random() * Math.PI * 2;

    if (bot.aiTimer <= 0) {
      bot.aiTimer = 20 + Math.random() * 35;
      const enemies = allCombatants().filter((e) => e.alive && e.team !== bot.team);
      bot.aiTarget = enemies[Math.floor(Math.random() * enemies.length)] || null;
      bot.strafeDir = Math.random() < 0.5 ? -1 : 1;
    }

    const spd = MOVE_SPEED * 0.8;
    let moveAngle = bot.patrolAngle;
    let shouldMove = true;

    if (bot.aiTarget && bot.aiTarget.alive) {
      const dx = bot.aiTarget.x - bot.x;
      const dy = bot.aiTarget.y - bot.y;
      bot.angle = Math.atan2(dy, dx);
      const dist = Math.hypot(dx, dy);
      bot.aiming = dist < 420;

      if (dist > 220) {
        moveAngle = bot.angle;
      } else if (dist > 90) {
        moveAngle = bot.angle + bot.strafeDir * (Math.PI / 2);
        if (bot.aiTimer < 8) bot.strafeDir *= -1;
      } else {
        moveAngle = bot.angle + Math.PI;
        shouldMove = dist < 70;
      }

      if (dist < 520 && bot.shootCooldown <= 0) {
        const chance = dist < 280 ? 0.2 : 0.11;
        if (Math.random() < chance) botShoot(bot);
      }
    } else {
      bot.patrolAngle += 0.02;
      moveAngle = bot.patrolAngle;
      const toCenter = Math.atan2(centerY - bot.y, centerX - bot.x);
      if (Math.hypot(bot.x - centerX, bot.y - centerY) > CELL * 10) moveAngle = toCenter;
      bot.angle = moveAngle;
    }

    if (shouldMove) {
      const nx = bot.x + Math.cos(moveAngle) * spd;
      const ny = bot.y + Math.sin(moveAngle) * spd;
      if (canMoveAt(nx, bot.y)) bot.x = nx;
      if (canMoveAt(bot.x, ny)) bot.y = ny;
    }
  }
}

function tick() {
  const now = Date.now();
  for (const e of allCombatants()) {
    if (!e.alive && e.respawnAt && now >= e.respawnAt) {
      respawnEntity(e);
    }
  }

  updateBots();

  broadcastAll({
    type: 'tick',
    players: publicPlayers(),
    scores,
    killFeed,
    gameOver,
    map: wallState,
  });
}

initBots();

wss.on('connection', (ws) => {
  if (players.size >= MAX_HUMANS) {
    ws.close();
    return;
  }

  const id = uuidv4();
  const player = createEntity(id, '', assignTeam(), false);
  player.ws = ws;
  players.set(id, player);

  sendInit(ws, id);
  broadcast({ type: 'join', player: publicEntity(player) }, ws);

  ws.on('message', (raw) => {
    let msg;
    try {
      msg = JSON.parse(raw);
    } catch {
      return;
    }
    const p = players.get(id);
    if (!p) return;

    switch (msg.type) {
      case 'setName':
        p.name = String(msg.name || p.name).slice(0, 16);
        break;
      case 'ping':
        if (p.ws && p.ws.readyState === 1) {
          p.ws.send(JSON.stringify({ type: 'pong', t: msg.t }));
        }
        break;
      case 'move':
        if (gameOver) break;
        p.x = Number(msg.x) || p.x;
        p.y = Number(msg.y) || p.y;
        p.angle = Number(msg.angle) || p.angle;
        p.aiming = !!msg.aiming;
        if (WEAPONS[msg.weapon]) p.weapon = msg.weapon;
        break;
      case 'shoot':
        if (!gameOver) handleShoot(id, Number(msg.angle), msg.weapon || p.weapon);
        break;
      default:
        break;
    }
  });

  ws.on('close', () => {
    players.delete(id);
    broadcast({ type: 'leave', id });
  });
});

setInterval(tick, TICK_MS);

const PORT = process.env.PORT || 3000;
server.listen(PORT, () => {
  console.log(`BREACH server running at http://localhost:${PORT}`);
});
