// server.js
const WebSocket = require('ws');
const fs = require('fs'); // We need the file system to save player data

// --- SETUP ---
const PORT = 8080;
const TICK_RATE = 30; // 30 updates per second
const wss = new WebSocket.Server({ port: PORT });
console.log(`[SERVER] Galactic OS server is operational on port ${PORT}`);

// --- GAME STATE ---
const players = {};
let entities = [];
const TILE_SIZE = 40;
const CHUNK_SIZE = 16;
const MAX_ENEMIES = 80;
const ENEMY_SPAWN_INTERVAL = 1;
let enemySpawnTimer = ENEMY_SPAWN_INTERVAL;
let lastTime = Date.now();
const bossRespawnTimers = {};

// --- PERSISTENT DATA ---
const banks = loadData('banks.json');
const marketListings = loadData('market.json');

function loadData(filename) {
    try {
        if (fs.existsSync(filename)) {
            const data = fs.readFileSync(filename);
            return JSON.parse(data);
        }
    } catch (err) {
        console.error(`Error loading ${filename}:`, err);
    }
    return {}; // Return empty object if file doesn't exist or is invalid
}

function saveData(filename, data) {
    fs.writeFile(filename, JSON.stringify(data, null, 2), (err) => {
        if (err) {
            console.error(`Error saving ${filename}:`, err);
        }
    });
}


// --- FULL WORLD GENERATION ---
const Perlin=function(t){this.seed=t||Math.random();const r=new Uint8Array(512);for(let t=0;t<256;t++)r[t]=t;let n=0;for(let t=255;t>0;t--)n=Math.floor((t+1)*(this.seed=(48271*this.seed)%2147483647)/2147483647),[r[t],r[n]]=[r[n],r[t]];for(let t=0;t<256;t++)r[t+256]=r[t];const e=t=>t*t*t*(t*(6*t-15)+10),o=(t,r,n)=>r+t*(n-r),s=(t,r,n,s)=>{const i=15&t,a=i<8?r:n,h=i<4?n:12===i||14===i?r:s;return((1&i)==0?a:-a)+((2&i)==0?h:-h)};this.get=(t,n,i=0)=>{const a=Math.floor(t)&255,h=Math.floor(n)&255,c=Math.floor(i)&255;t-=Math.floor(t),n-=Math.floor(n),i-=Math.floor(i);const u=e(t),l=e(n),f=e(i),d=r[a]+h,p=r[d]+c,g=r[d+1]+c,m=r[a+1]+h,C=r[m]+c,w=r[m+1]+h;return o(f,o(l,o(u,s(r[p],t,n,i),s(r[C],t-1,n,i)),o(u,s(r[g],t,n-1,i),s(r[w],t-1,n-1,i))),o(l,o(u,s(r[p+1],t,n,i-1),s(r[C+1],t-1,n,i-1)),o(u,s(r[g+1],t,n-1,i-1),s(r[w+1],t-1,n-1,i-1))))}};
const MAP_SEED = 'galactic_os_final_frontier';
const perlin = new Perlin(MAP_SEED), biomeNoise = new Perlin(MAP_SEED + '_biomes');
const TILE_TYPES = { 0:{n:'V',c:'#05060a'}, 1:{n:'P',c:'#10121f'}, 2:{n:'F',c:'#10121f',wc:'#005f6b'}, 3:{n:'C',c:'#150f1f',wc:'#6b00b3'}, 10:{n:'CF',c:'#1f283e'}, 11:{n:'CW',c:'#00f0ff',wc:'#00f0ff'}, 12:{n:'OW',c:'#a8b3d3',wc:'#a8b3d3'}, 13:{n:'OF',c:'#4a4a52'}, 14:{n:'E',c:'#000000'} };
const cityData = [[11,11,11,11,11,11,11,14,14,11,11,11,11,11,11,11],[11,10,10,10,10,10,10,10,10,10,10,10,10,10,10,11],[11,10,11,11,11,10,11,11,11,11,10,11,11,11,10,11],[11,10,11,10,10,10,10,10,10,10,10,10,10,11,10,11],[11,10,11,10,11,11,11,11,11,11,11,10,11,11,10,11],[14,10,10,10,11,10,10,10,10,10,10,10,11,10,10,14],[14,10,10,10,11,10,11,10,10,11,10,11,11,10,10,14],[11,10,11,10,11,10,10,10,10,10,10,10,11,10,10,11],[11,10,11,10,10,10,11,11,11,11,10,10,11,10,10,11],[11,10,11,11,11,10,10,10,10,10,10,11,11,11,10,11],[11,10,10,10,10,10,10,10,10,10,10,10,10,10,10,11],[11,11,11,11,11,11,11,14,14,11,11,11,11,11,11,11]];
const CITY_SPAWN_POINT = { x: 8 * TILE_SIZE, y: 8 * TILE_SIZE };
const BOSS_LOCATIONS = { DREADNOUGHT: {x: 150*TILE_SIZE, y: 150*TILE_SIZE}, SERPENT: {x: -150*TILE_SIZE, y: -150*TILE_SIZE}, ORACLE: {x: 0, y: 300*TILE_SIZE}, VOID_HUNTER: {x: 300*TILE_SIZE, y: 0} };
const TIER_COLORS = { 1: '#9ea3a1', 2: '#ffffff', 3: '#32a852', 4: '#3273a8', 5: '#a832a4', 6: '#e3d400' };
function createShopWeapon(tier, type) { return { id: `wep_${type}_${tier}`, slot: 'Weapon', tier, type, name: `${type} Emitter` }; }
function generateEquipment(tier) {
    tier = Math.max(1, Math.min(6, tier));
    const slots = ['Module', 'Plating', 'Utility'];
    const slot = slots[Math.floor(Math.random() * slots.length)];
    const item = { id: `item_${Date.now()}_${Math.random()}`, slot, tier, stats: {} };
    switch(slot) {
        case 'Module': item.name = `M${tier}`; item.stats = { damage: 5 + (tier-1)*5, fireRate: 0.5 + (tier-1)*0.5 }; break;
        case 'Plating': item.name = `P${tier}`; item.stats = { maxHealth: 10 + (tier-1) * 10, defense: 1 + (tier-1) * 2 }; break;
        case 'Utility': item.name = `U${tier}`; if (Math.random() > 0.5) { item.stats = { speed: 0.1 + (tier-1) * 0.15, energyRegen: 2 + (tier-1) * 3 }; } else { item.stats = { maxEnergy: 20 + (tier-1) * 15 }; } break;
    }
    return item;
}
const shopInventories = { 'Exchange': [ { item: generateEquipment(1), cost: 20 }, { item: generateEquipment(1), cost: 20 }, { item: generateEquipment(2), cost: 100 } ] };
const localWorld = {};
function generateChunk(chunkX, chunkY) { const key = `${chunkX},${chunkY}`; if (localWorld[key]) return; const chunk = { tiles: Array(CHUNK_SIZE * CHUNK_SIZE).fill(1) }; for(const bossName in BOSS_LOCATIONS) { const loc = BOSS_LOCATIONS[bossName]; const bossChunkX = Math.floor(loc.x / TILE_SIZE / CHUNK_SIZE); const bossChunkY = Math.floor(loc.y / TILE_SIZE / CHUNK_SIZE); if(chunkX === bossChunkX && chunkY === bossChunkY){ for (let y = 0; y < CHUNK_SIZE; y++) for (let x = 0; x < CHUNK_SIZE; x++) { const worldX = (chunkX * CHUNK_SIZE + x) * TILE_SIZE; const worldY = (chunkY * CHUNK_SIZE + y) * TILE_SIZE; const dist = Math.hypot(worldX - loc.x, worldY - loc.y); if (dist < 10 * TILE_SIZE) chunk.tiles[y * CHUNK_SIZE + x] = 13; if (dist > 9 * TILE_SIZE && dist < 10 * TILE_SIZE) chunk.tiles[y * CHUNK_SIZE + x] = 12; } localWorld[key] = chunk; broadcastMessage({type: 'worldChunkUpdate', key: key, chunk: chunk}); return;} } if (chunkX === 0 && chunkY === 0) { for (let y = 0; y < CHUNK_SIZE; y++) for (let x = 0; x < CHUNK_SIZE; x++) { chunk.tiles[y * CHUNK_SIZE + x] = cityData[y]?.[x] ?? 10; } } else { for (let y = 0; y < CHUNK_SIZE; y++) for (let x = 0; x < CHUNK_SIZE; x++) { const wX = chunkX * CHUNK_SIZE + x, wY = chunkY * CHUNK_SIZE + y; const bV = (biomeNoise.get(wX / 200, wY / 200) + 1) / 2; let t = 1; if (bV < 0.4) t = 2; else if (bV > 0.85) t = 3; if ((t === 2 || t === 3) && (perlin.get(wX / 25, wY / 25) + 1) / 2 > 0.55) t -= 1; chunk.tiles[y * CHUNK_SIZE + x] = t; } } localWorld[key] = chunk; broadcastMessage({type: 'worldChunkUpdate', key: key, chunk: chunk}); }
function getTile(worldX, worldY) { const cX = Math.floor(worldX / TILE_SIZE); const cY = Math.floor(worldY / TILE_SIZE); const chX = Math.floor(cX / CHUNK_SIZE); const chY = Math.floor(cY / CHUNK_SIZE); const key = `${chX},${chY}`; if (!localWorld[key]) generateChunk(chX, chY); const chunk = localWorld[key]; const tX = (cX % CHUNK_SIZE + CHUNK_SIZE) % CHUNK_SIZE; const tY = (cY % CHUNK_SIZE + CHUNK_SIZE) % CHUNK_SIZE; return chunk.tiles[tY * CHUNK_SIZE + tX]; }
function isSolid(tileType) { return TILE_TYPES[tileType]?.wc !== undefined; }
function isCity(worldX, worldY) { return Math.floor(worldX / TILE_SIZE / CHUNK_SIZE) === 0 && Math.floor(worldY / TILE_SIZE / CHUNK_SIZE) === 0; }
function getThreatLevel(x, y) { if(isCity(x,y)) return 0; const distFromSpawn = Math.hypot(x, y) / TILE_SIZE; if (distFromSpawn < 100) return 1; if (distFromSpawn < 200) return 2; if (distFromSpawn < 300) return 3; return 4; }
function getItemBaseValue(item) { if (!item) return 0; return (item.tier * item.tier) * 20; }

// --- PLAYER & SUBCLASSES (SERVER-SIDE) ---
class Player {
    constructor(id, username, color, className) {
        this.id = id;
        this.username = username; // This is the account name, used for the bank
        this.color = color;
        this.className = className;
        this.x = CITY_SPAWN_POINT.x;
        this.y = CITY_SPAWN_POINT.y;
        this.radius = 15;
        this.angle = 0;
        this.dataBits = 0;
        this.equipment = { Weapon: null, Module: null, Plating: null, Utility: null };
        this.inventory = Array(12).fill(null);
        
        // --- NEW: Level and XP System ---
        this.level = 1;
        this.xp = 0;
        this.xpToNextLevel = this.calculateXpToNextLevel();

        this.stats = {};
        this.recalculateStats();

        this.health = this.stats.maxHealth;
        this.energy = this.stats.maxEnergy;
        this.gunCooldown = 0;
        this.teleportCooldown = 0;
        this.teleportMaxCooldown = 600; // 10 minutes
        this.abilityCooldown = 0;
        this.isSlowed = false;
        this.isDead = false;
        this.isBoosting = false;
        this.canBoost = true;
        this.timeSinceLastHit = 0;
        this.REGEN_DELAY = 5; // seconds
        this.inputs = { w: false, a: false, s: false, d: false, h: false, shift: false, q: false, e: false, mouse: { down: false } };
    }
    
    calculateXpToNextLevel() {
        // A simple exponential curve for leveling
        return Math.floor(100 * Math.pow(1.15, this.level - 1));
    }

    addXp(amount) {
        if (this.isDead) return;
        this.xp += amount;
        while (this.xp >= this.xpToNextLevel) {
            this.xp -= this.xpToNextLevel;
            this.level++;
            this.xpToNextLevel = this.calculateXpToNextLevel();
            // Level up effect can be added here
            this.recalculateStats(); // Recalculate stats on level up
            // Fully heal on level up
            this.health = this.stats.maxHealth;
            this.energy = this.stats.maxEnergy;
        }
    }

    recalculateStats() {
        const base = { maxHealth: 100, maxEnergy: 300, defense: 0, speed: 4.0, fireRate: 2, damage: 8, energyRegen: 25, healthRegen: 5, ...this.classStats };
        // Add level-based stat scaling
        base.maxHealth += (this.level - 1) * 5;
        base.damage += (this.level - 1) * 1;

        for(const slot in this.equipment) {
            const item = this.equipment[slot];
            if(item && item.stats) {
                for(const stat in item.stats) {
                    base[stat] = (base[stat] || 0) + item.stats[stat];
                }
            }
        }
        this.stats = base;
        this.health = Math.min(this.health, this.stats.maxHealth);
        this.energy = Math.min(this.energy, this.stats.maxEnergy);
    }

    update(dt) {
        this.timeSinceLastHit += dt;
        if (this.timeSinceLastHit > this.REGEN_DELAY && this.health < this.stats.maxHealth) {
            this.health += this.stats.healthRegen * dt;
            this.health = Math.min(this.health, this.stats.maxHealth);
        }

        let currentSpeed = this.isSlowed ? this.stats.speed * 0.5 : this.stats.speed;
        this.isSlowed = false;
        
        this.isBoosting = this.inputs.shift && this.energy > 0 && this.canBoost;
        if (this.isBoosting) {
            currentSpeed *= 1.8;
            this.energy -= 35 * dt;
            if (this.energy <= 0) {
                this.canBoost = false;
            }
        } else {
            if (this.energy < this.stats.maxEnergy) {
                this.energy += this.stats.energyRegen * dt;
            }
            if (!this.canBoost && this.energy >= this.stats.maxEnergy * 0.25) {
                this.canBoost = true;
            }
        }
        this.energy = Math.max(0, Math.min(this.stats.maxEnergy, this.energy));

        const forward = (this.inputs.w ? 1 : 0) - (this.inputs.s ? 1 : 0); const strafe = (this.inputs.d ? 1 : 0) - (this.inputs.a ? 1 : 0); const moveX = Math.cos(this.angle) * forward - Math.sin(this.angle) * strafe; const moveY = Math.sin(this.angle) * forward + Math.cos(this.angle) * strafe; const mag = Math.hypot(moveX, moveY); if (mag > 0) { const timeAdjustedSpeed = currentSpeed * (dt * 60); const finalMoveX = mag > 1 ? (moveX / mag) * timeAdjustedSpeed : moveX * timeAdjustedSpeed; const finalMoveY = mag > 1 ? (moveY / mag) * timeAdjustedSpeed : moveY * timeAdjustedSpeed; const nX = this.x + finalMoveX; const nY = this.y + finalMoveY; if (!isSolid(getTile(nX, this.y))) this.x = nX; if (!isSolid(getTile(this.x, nY))) this.y = nY; } this.gunCooldown -= dt; if (this.inputs.mouse.down && this.gunCooldown <= 0) this.fireWeapon(); this.teleportCooldown = Math.max(0, this.teleportCooldown - dt); if (this.inputs.h && this.teleportCooldown <= 0) { this.teleportCooldown = this.teleportMaxCooldown; this.x = CITY_SPAWN_POINT.x; this.y = CITY_SPAWN_POINT.y; } this.abilityCooldown = Math.max(0, this.abilityCooldown - dt); if (this.inputs.q) { this.useAbility(); } this.updateAbility(dt); if (this.inputs.e) { this.attemptInteraction(); this.inputs.e = false; } }
    fireWeapon() { const weapon = this.equipment.Weapon || { type: 'Default' }; this.gunCooldown = 1 / this.stats.fireRate; const p = { ownerId: this.id, angle: this.angle, color: this.color, damage: this.stats.damage }; switch(weapon.type) { case 'Beam': if(this.energy > 5){ this.energy -= 5; entities.push(new Laser(this.x, this.y, p, 800)); } break; case 'Scatter': for(let i=0; i < 5; i++) { p.angle = this.angle + (Math.random() - 0.5) * 0.4; entities.push(new Projectile(this.x, this.y, p)); } break; case 'Launcher': entities.push(new Grenade(this.x, this.y, p, 60)); break; default: entities.push(new Projectile(this.x, this.y, p)); break; } }
    takeDamage(amount, damager = null) { if(this.isDead) return; this.timeSinceLastHit = 0; const damageTaken = Math.max(1, amount - this.stats.defense); this.health = Math.max(0, this.health - damageTaken); entities.push(new FloatingText(this.x, this.y - this.radius, `-${Math.floor(damageTaken)}`)); if (this.health <= 0) this.die(); }
    die() {
        this.isDead = true;
        const droppedItems = [...Object.values(this.equipment), ...this.inventory].filter(item => item !== null);
        const droppedBits = Math.floor(this.dataBits * 0.8);
        if(droppedItems.length > 0 || droppedBits > 0) {
            entities.push(new PlayerLootBag(this.x, this.y, droppedItems, droppedBits, this.color));
        }
        const playerSocket = getSocketByPlayerId(this.id);
        if (playerSocket) playerSocket.send(JSON.stringify({ type: 'playerDied' }));
    }
    respawn() {
        this.isDead = false;
        this.equipment = { Weapon: null, Module: null, Plating: null, Utility: null };
        this.inventory = Array(12).fill(null);
        this.dataBits = 0;
        this.level = 1; // Permadeath
        this.xp = 0;
        this.xpToNextLevel = this.calculateXpToNextLevel();
        this.recalculateStats();
        this.health = this.stats.maxHealth;
        this.energy = this.stats.maxEnergy;
    }
    addToInventory(item) { if (!item) return false; const index = this.inventory.findIndex(slot => slot === null); if (index !== -1) { this.inventory[index] = { ...item }; this.recalculateStats(); return true; } return false; }
    attemptInteraction() {
        const lootRadius = 80;
        const closestLootBag = entities.find(e => e.type === 'PlayerLootBag' && e.pickupDelay <= 0 && Math.hypot(e.x - this.x, e.y - this.y) < lootRadius);
        if (closestLootBag) {
            if (closestLootBag.bits > 0) { this.dataBits += closestLootBag.bits; closestLootBag.bits = 0; }
            closestLootBag.items.forEach((item, index) => { if (item && this.addToInventory(item)) { closestLootBag.items[index] = null; } });
            return;
        }

        for(const entity of entities) { if(entity instanceof NPC && Math.hypot(this.x - entity.x, this.y - entity.y) < 50) { const playerSocket = getSocketByPlayerId(this.id); if (playerSocket) {
            if (entity.name === "Bank") {
                if (!banks[this.username]) banks[this.username] = Array(12).fill(null);
                playerSocket.send(JSON.stringify({type: 'openBank', bank: banks[this.username]}));
            } else {
                 playerSocket.send(JSON.stringify({type: 'openShop', npcName: entity.name, inventory: shopInventories[entity.name], marketListings: marketListings }));
            }
        } return; } }

        const pickupRadius = 60;
        const closestItem = entities.filter(e => (e.type === 'EquipmentDrop') && e.pickupDelay <= 0 && Math.hypot(e.x - this.x, e.y - this.y) < pickupRadius).sort((a,b) => Math.hypot(a.x - this.x, a.y - this.y) - Math.hypot(b.x - this.x, b.y - this.y))[0];
        if(closestItem) { if(this.addToInventory(closestItem.item)) closestItem.isDead = true; }
    }
    useAbility() {} updateAbility(dt) {}
    getData() { return { id: this.id, x: this.x, y: this.y, angle: this.angle, color: this.color, username: this.username, health: this.health, stats: this.stats, energy: this.energy, abilityCooldown: this.abilityCooldown, teleportCooldown: this.teleportCooldown, dataBits: this.dataBits, inventory: this.inventory, equipment: this.equipment, isInvisible: this.isInvisible, shieldActive: this.shieldActive, isDead: this.isDead, isBoosting: this.isBoosting, className: this.className, level: this.level, xp: this.xp, xpToNextLevel: this.xpToNextLevel }; }
}

class Operator extends Player { constructor(id, u, c) { super(id, u, c, 'Operator'); this.classStats = { speed: 4.5, maxHealth: 80 }; this.isInvisible = false; this.invisDuration = 0; this.recalculateStats(); } useAbility() { if (this.abilityCooldown <= 0) { this.abilityCooldown = 12; this.isInvisible = true; this.invisDuration = 3; } } updateAbility(dt) { if (this.isInvisible) { this.invisDuration -= dt; if (this.invisDuration <= 0) this.isInvisible = false; } } }
class Guardian extends Player { constructor(id, u, c) { super(id, u, c, 'Guardian'); this.classStats = { speed: 3.5, maxHealth: 150 }; this.shieldActive = false; this.shieldDuration = 0; this.shieldHealth = 0; this.recalculateStats(); } useAbility() { if (this.abilityCooldown <= 0) { this.abilityCooldown = 20; this.shieldActive = true; this.shieldDuration = 5; this.shieldHealth = 100; } } updateAbility(dt) { if (this.shieldActive) { this.shieldDuration -= dt; if (this.shieldDuration <= 0) this.shieldActive = false; } } takeDamage(amount, damager = null) { this.timeSinceLastHit = 0; if (this.shieldActive) { const damageAbsorbed = Math.min(this.shieldHealth, amount); this.shieldHealth -= damageAbsorbed; const damageLeft = amount - damageAbsorbed; if (this.shieldHealth <= 0) this.shieldActive = false; if (damageLeft > 0) super.takeDamage(damageLeft, damager); } else { super.takeDamage(amount, damager); } } }
class Spectre extends Player {
    constructor(id, u, c) { super(id, u, c, 'Spectre'); this.recalculateStats(); }
    useAbility() {
        if (this.abilityCooldown <= 0) {
            this.abilityCooldown = 6;
            const blinkDist = 150;
            const startX = this.x;
            const startY = this.y;
            let targetX = this.x + Math.cos(this.angle) * blinkDist;
            let targetY = this.y + Math.sin(this.angle) * blinkDist;
            if(!isSolid(getTile(targetX, targetY))) {
                this.x = targetX;
                this.y = targetY;
                broadcastMessage({type: 'sfx', effect: 'blink', x: startX, y: startY, color: this.color});
                broadcastMessage({type: 'sfx', effect: 'blink', x: this.x, y: this.y, color: this.color});
            }
        }
    }
}

// --- ENTITY & ENEMY CLASSES (SERVER-SIDE) ---
class Entity { constructor(x, y, type) { this.id = `${type}_${Date.now()}_${Math.random()}`; this.x = x; this.y = y; this.type = type; } update(dt) {} getData() { const data = {}; for(const key in this) { if (typeof this[key] !== 'function' && key !== 'owner' && key !== 'head' && key !== 'segments') data[key] = this[key]; } return data; } }

class Enemy extends Entity {
    constructor(x, y, threatLevel, type = 'Enemy') {
        super(x, y, type);
        this.threatLevel = threatLevel; this.radius = 12; this.speed = 2.0; this.health = 30; this.maxHealth = 30; this.color = '#ff3355'; this.aggroRadius = 350; this.deAggroRadius = this.aggroRadius * 1.5;
        this.wanderTarget = null; this.wanderTimer = 0;
        this.xpValue = 10 * threatLevel;
        this.applyThreatLevel();
    }
    applyThreatLevel() { this.health = this.maxHealth = this.health * (1 + (this.threatLevel-1)*0.5); this.damageMultiplier = 1 + (this.threatLevel-1)*0.3; }
    update(dt) {
        let targetPlayer = null;
        let closestDist = Infinity;
        for(const pid in players){
            const player = players[pid];
            if (player.isDead || player.isInvisible) continue;
            const dist = Math.hypot(player.x - this.x, player.y - this.y);
            if(dist < closestDist){
                closestDist = dist;
                targetPlayer = player;
            }
        }
        
        if (targetPlayer && closestDist < this.aggroRadius && !isCity(targetPlayer.x, targetPlayer.y)) {
            const dX = targetPlayer.x - this.x, dY = targetPlayer.y - this.y;
            if(closestDist > this.radius + targetPlayer.radius){
                const timeAdjustedSpeed = this.speed * (dt * 60);
                const nX = this.x + (dX / closestDist) * timeAdjustedSpeed;
                const nY = this.y + (dY / closestDist) * timeAdjustedSpeed;
                if (isCity(nX, nY)) return; 
                if (!isSolid(getTile(nX, this.y))) this.x = nX;
                if (!isSolid(getTile(this.x, nY))) this.y = nY;
            } else {
                targetPlayer.takeDamage(10 * this.damageMultiplier * dt, this);
            }
        } else {
            this.wanderTimer -= dt;
            if (!this.wanderTarget || this.wanderTimer <= 0) {
                this.wanderTimer = Math.random() * 3 + 2;
                const wanderAngle = Math.random() * Math.PI * 2;
                const wanderDist = Math.random() * 150 + 50;
                this.wanderTarget = { x: this.x + Math.cos(wanderAngle) * wanderDist, y: this.y + Math.sin(wanderAngle) * wanderDist };
            }
            const dXt = this.wanderTarget.x - this.x, dYt = this.wanderTarget.y - this.y;
            const dPt = Math.hypot(dXt, dYt);
            if (dPt > 1) {
                const timeAdjustedSpeed = (this.speed / 2) * (dt * 60);
                const nX = this.x + (dXt / dPt) * timeAdjustedSpeed;
                const nY = this.y + (dYt / dPt) * timeAdjustedSpeed;
                if (!isSolid(getTile(nX, nY)) && !isCity(nX, nY)) { this.x = nX; this.y = nY; }
                else { this.wanderTarget = null; }
            } else { this.wanderTarget = null; }
        }
    }
    takeDamage(amount, damager) {
        this.health -= amount;
        if (this.health <= 0 && !this.isDead) {
            this.isDead = true;
            if (damager && players[damager.ownerId]) {
                players[damager.ownerId].addXp(this.xpValue);
            }
            for (let i = 0; i < 2; i++) entities.push(new LootDrop(this.x, this.y, this.threatLevel));
            if (Math.random() < 0.1) entities.push(new EquipmentDrop(this.x, this.y, generateEquipment(this.threatLevel + Math.floor(Math.random()*2))));
        }
    }
}
class Stinger extends Enemy { constructor(x, y, tL) { super(x, y, tL, 'Stinger'); this.radius = 10; this.speed = 3.5; this.health = this.maxHealth = 20; this.color = '#f07cff'; this.shootCooldown = 2; this.xpValue = 15 * tL; this.applyThreatLevel(); } update(dt) { super.update(dt); this.shootCooldown -= dt; if (this.shootCooldown <= 0) { this.shootCooldown = 2; for(const pid in players){ const player = players[pid]; if(!player.isDead && Math.hypot(player.x - this.x, player.y - this.y) < this.aggroRadius){ const p = { ownerId: this.id, angle: Math.atan2(player.y - this.y, player.x - this.x), color: this.color, damage: 5*this.damageMultiplier }; entities.push(new Projectile(this.x, this.y, p, 0.8)); break; } } } } }

// NEW MOB
class VoidSwarmer extends Enemy {
    constructor(x, y, tL) {
        super(x, y, tL, 'VoidSwarmer');
        this.radius = 8; this.speed = 4.5; this.health = this.maxHealth = 15; this.color = '#7d3c98';
        this.xpValue = 8 * tL;
        this.applyThreatLevel();
    }
}

class Warden extends Enemy {
    constructor(x, y, tL) {
        super(x, y, tL, 'Warden');
        this.radius = 18; this.speed = 1.5; this.health = this.maxHealth = 150; this.color = '#e3d400';
        this.abilityCooldown = 5; this.shield = 50; this.maxShield = 50;
        this.xpValue = 50 * tL; this.applyThreatLevel();
    }
    update(dt) {
        super.update(dt);
        this.abilityCooldown -= dt;
        if(this.abilityCooldown <= 0) {
            this.abilityCooldown = 5;
            for(const pid in players) {
                const player = players[pid];
                const dist = Math.hypot(player.x-this.x, player.y-this.y);
                if(!player.isDead && dist < 250) {
                    player.isSlowed = true;
                    const pullStrength = 800 * dt;
                    player.x -= (player.x - this.x) / dist * pullStrength;
                    player.y -= (player.y - this.y) / dist * pullStrength;
                }
            }
        }
    }
    takeDamage(amount, damager = null) {
        if (this.shield > 0) {
            this.shield -= amount;
            if (this.shield < 0) {
                const overflowDamage = -this.shield;
                this.shield = 0;
                super.takeDamage(overflowDamage, damager);
            }
        } else {
            super.takeDamage(amount, damager);
        }
    }
}

// --- BOSSES (SERVER-SIDE) ---
class WorldBoss extends Enemy {
    constructor(x, y, name, color, hp, type) {
        super(x, y, 5, type);
        this.isBoss = true;
        this.bossName = name;
        this.color = color;
        this.health = this.maxHealth = hp;
        this.radius = 80;
        this.aggroRadius = 2000;
        this.attackPhase = 'idle';
        this.attackTimer = 0;
        this.xpValue = 5000;
    }
    takeDamage(amount, damager = null) {
        this.health -= amount;
        if (this.health <= 0 && !this.isDead) {
            this.isDead = true;
            if(damager && players[damager.ownerId]) {
                broadcastMessage({ type: 'chat', sender: 'SYSTEM', message: `${players[damager.ownerId].username} has defeated the ${this.bossName}!`, color: '#ff00ff' });
                players[damager.ownerId].addXp(this.xpValue);
            }
            bossRespawnTimers[this.bossName] = 300;
            for (let i = 0; i < 10; i++) entities.push(new EquipmentDrop(this.x, this.y, generateEquipment(5)));
        }
    }
}

class Dreadnought extends WorldBoss {
    constructor(x, y) { super(x, y, "DREADNOUGHT", '#ff6a00', 5000, "Dreadnought"); }
    update(dt) {
        let targetPlayer = null;
        for(const pid in players) { const p = players[pid]; if(!p.isDead && Math.hypot(p.x - this.x, p.y - this.y) < this.aggroRadius) { targetPlayer = p; break; }}
        if (!targetPlayer) return;
        const dX = targetPlayer.x - this.x, dY = targetPlayer.y - this.y; const dP = Math.hypot(dX, dY);
        if(dP > 400 && !isCity(this.x, this.y)) { this.x += (dX / dP) * this.speed * (dt * 60); this.y += (dY / dP) * this.speed * (dt * 60); }
        this.attackTimer -= dt;
        if(this.attackTimer <= 0) {
            const p = { ownerId: this.id, angle: Math.atan2(dY, dX), color: this.color, damage: 10 };
            switch(this.attackPhase) {
                case 'idle': case 'barrage':
                    this.attackTimer = 3;
                    for(let i=0;i<10;i++) { setTimeout(() => { if(this.isDead) return; try { const currentTarget = players[Object.keys(players).find(id => players[id] === targetPlayer)]; if(!currentTarget) return; const targetAngle = Math.atan2(currentTarget.y-this.y, currentTarget.x-this.x); p.angle = targetAngle + (Math.random() - 0.5) * 0.3; entities.push(new Projectile(this.x, this.y, p, 1.5, 10)); } catch(e){} }, i * 100); }
                    this.attackPhase = 'mortar'; break;
                case 'mortar':
                    this.attackTimer = 5;
                    entities.push(new MortarProjectile(this.x, this.y, targetPlayer.x, targetPlayer.y, this.id));
                    this.attackPhase = 'barrage'; break;
            }
        }
    }
}

class SerpentHead extends WorldBoss {
    constructor(x, y) {
        super(x, y, "SERPENT", '#33ff99', 3000, "SerpentHead");
        this.radius = 30;
        this.segments = [];
        let leader = this;
        for(let i=1; i<=8; i++) {
            const seg = new SerpentBody(x - i*40, y, this);
            this.segments.push(seg);
            entities.push(seg);
            leader = seg;
        }
    }
    update(dt) {
        let targetPlayer=null; for(const pid in players){const p=players[pid]; if(!p.isDead && Math.hypot(p.x-this.x,p.y-this.y) < this.aggroRadius){targetPlayer=p; break;}} if(!targetPlayer) return;
        super.update(dt);
        this.attackTimer -= dt;
        if(this.attackTimer <= 0) {
            this.attackTimer = 0.5;
            const proj = { ownerId: this.id, angle: Math.atan2(targetPlayer.y-this.y, targetPlayer.x-this.x), color: this.color, damage: 15 };
            entities.push(new Projectile(this.x, this.y, proj, 1.2, 8));
        }
        let leader = this;
        this.segments.forEach(seg => {
            if (!seg.isDead) {
                seg.follow(leader, dt);
                leader = seg;
            }
        });
    }
    takeDamage(amount, damager = null) {
        const bodyAlive = this.segments.some(s => !s.isDead);
        const damageMultiplier = bodyAlive ? 0.1 : 1.0;
        super.takeDamage(amount * damageMultiplier, damager);
    }
    getData() {
        const data = super.getData();
        data.segments = this.segments.map(seg => seg.getData());
        return data;
    }
}

class SerpentBody extends Enemy {
    constructor(x, y, head) {
        super(x, y, 5, 'SerpentBody');
        this.head = head;
        this.radius = 25;
        this.health = this.maxHealth = 1000;
        this.color = '#29cc7a';
        this.shootCooldown = Math.random() * 3 + 2;
        this.xpValue = 250;
    }
    follow(leader, dt) {
        const dX = leader.x - this.x, dY = leader.y - this.y;
        const dist = Math.hypot(dX, dY);
        const targetDist = this.radius + leader.radius - 15;
        if(dist > targetDist) {
            const timeAdjustedSpeed = 10 * (dt * 60);
            this.x += (dX / dist) * timeAdjustedSpeed;
            this.y += (dY / dist) * timeAdjustedSpeed;
        }
    }
    update(dt) {
        this.shootCooldown -= dt;
        if(this.shootCooldown <= 0) {
            this.shootCooldown = Math.random() * 3 + 2;
            let targetPlayer=null; for(const pid in players){const p=players[pid]; if(!p.isDead && Math.hypot(p.x-this.x,p.y-this.y) < this.aggroRadius){targetPlayer=p; break;}}
            if (targetPlayer) {
                 const p = { ownerId: this.id, angle: Math.atan2(targetPlayer.y - this.y, targetPlayer.x - this.x), color: this.color, damage: 10 };
                 entities.push(new Projectile(this.x, this.y, p));
            }
        }
    }
}

class TheOracle extends WorldBoss {
    constructor(x,y) { super(x,y, "THE ORACLE", '#a832a4', 8000, "TheOracle"); }
    update(dt) {
        let targetPlayer = null; for(const pid in players) { const p = players[pid]; if(!p.isDead && Math.hypot(p.x-this.x, p.y-this.y) < this.aggroRadius) { targetPlayer = p; break; }}
        if (!targetPlayer) { this.attackPhase = 'idle'; return; }

        this.attackTimer -= dt;
        if(this.attackTimer <= 0) {
            const p = { ownerId: this.id, color: this.color, damage: 20};
            switch(this.attackPhase) {
                case 'idle': case 'barrage':
                    for(let i=0; i<12; i++) { p.angle = (i/12) * Math.PI*2 + Date.now()/1000; entities.push(new Projectile(this.x, this.y, p)); }
                    this.attackTimer = 3.5;
                    this.attackPhase = 'summon';
                    break;
                case 'summon':
                    for(let i=0; i<5; i++) {
                        const angle = Math.random()*Math.PI*2;
                        entities.push(new Stinger(this.x + Math.cos(angle)*150, this.y + Math.sin(angle)*150, 4));
                    }
                    this.attackTimer = 5;
                    this.attackPhase = 'barrage';
                    break;
            }
        }
    }
}

class VoidHunter extends WorldBoss {
    constructor(x, y) { super(x, y, "VOID HUNTER", '#1f283e', 4000, "aclysmHunter"); this.radius = 25; this.isInvisible = true; this.attackTimer = 3; }
    update(dt) {
        let targetPlayer=null; for(const pid in players){const p=players[pid]; if(!p.isDead && Math.hypot(p.x-this.x,p.y-this.y) < this.aggroRadius){targetPlayer=p; break;}}
        if(!targetPlayer){this.isInvisible = true; return;}
        
        super.update(dt);
        this.attackTimer -= dt;
        if(this.attackTimer <= 0) {
            this.attackTimer = 5;
            this.isInvisible = false;
            setTimeout(() => {
                if(this.isDead) return;
                try {
                    const currentTarget = players[Object.keys(players).find(id => players[id] === targetPlayer)];
                    if(!currentTarget) return;
                    for(let i=0; i<10; i++) {
                        const proj = { ownerId: this.id, angle: Math.atan2(currentTarget.y-this.y, currentTarget.x-this.x) + (Math.random()-0.5)*0.8, color: '#ff3355', damage: 25};
                        entities.push(new Projectile(this.x, this.y, proj, 0.5));
                    }
                    setTimeout(() => {
                        if(this.isDead) return;
                        this.isInvisible = true;
                        const angle = Math.random()*Math.PI*2;
                        this.x = currentTarget.x + Math.cos(angle)*400;
                        this.y = currentTarget.y + Math.sin(angle)*400;
                    }, 1000);
                } catch(e) {}
            }, 1000);
        }
    }
}

// --- OTHER ENTITIES (SERVER-SIDE) ---
class Projectile extends Entity { constructor(x,y,p,l=1.5,r=4){ super(x,y,'Projectile'); this.ownerId = p.ownerId; this.angle = p.angle; this.radius=r; this.speed=15; this.life=l; this.color=p.color; this.damage=p.damage;} update(dt){ this.x+=Math.cos(this.angle)*this.speed*(dt*60); this.y+=Math.sin(this.angle)*this.speed*(dt*60); this.life-=dt; if(this.life<=0||isSolid(getTile(this.x,this.y))) this.isDead=true; } }
class MortarProjectile extends Entity { constructor(sX,sY,tX,tY,ownerId){ super(sX,sY,'MortarProjectile'); this.tX=tX; this.tY=tY; this.ownerId=ownerId; this.life=2; this.radius=15 } update(dt){ this.life-=dt; if(this.life<=0){ this.isDead=true; entities.push(new Shockwave(this.tX,this.tY,150,40,this.ownerId)); } } }
class Laser extends Entity { constructor(x,y,p,l){ super(x,y,'Laser'); this.ownerId=p.ownerId; this.angle=p.angle; this.color=p.color; this.damage=p.damage; this.length=l; this.life=0.1;} update(dt){ this.life-=dt; if(this.life<=0) this.isDead = true; } }
class Grenade extends Projectile { constructor(x,y,p,rad) { super(x,y,p,0.8,8); this.type='Grenade'; this.speed=10; this.explosionRadius = rad; } update(dt) { super.update(dt); if(this.life <= 0) { this.isDead = true; entities.push(new Shockwave(this.x, this.y, this.explosionRadius, this.damage, this.ownerId)); } } }
class Shockwave extends Entity { constructor(x,y,mR,d,ownerId){ super(x,y,'Shockwave'); this.ownerId=ownerId; this.radius=0; this.maxRadius=mR; this.damage=d; this.life=0.5; this.hitTargets=[]; } update(dt){ this.radius += this.maxRadius * 3 * dt; this.life -= dt; if(this.life <= 0) this.isDead = true; } }
class NPC extends Entity { constructor(x, y, name, color = '#8a2be2') { super(x, y, 'NPC'); this.name = name; this.radius = 10; this.color = color; } }
class LootDrop extends Entity { constructor(x,y,v){ super(x + Math.random()*20-10, y + Math.random()*20-10, 'LootDrop'); this.value=v*5; this.radius=5; this.color='#ffff00'; this.life=60; } update(dt){ this.life-=dt; if (this.life <= 0) this.isDead=true; } }
class EquipmentDrop extends Entity { constructor(x, y, item) { super(x + Math.random()*20-10, y+Math.random()*20-10, 'EquipmentDrop'); this.item = item; this.radius = 8; this.color = TIER_COLORS[item.tier] || '#fff'; this.life = 60; this.pickupDelay = 0.5; } update(dt) { this.life -= dt; if (this.pickupDelay > 0) this.pickupDelay -= dt; if (this.life <= 0) this.isDead = true; } }
class PlayerLootBag extends Entity { constructor(x, y, items, bits, color) { super(x, y, 'PlayerLootBag'); this.item = { color: color }; this.items = items; this.bits = bits; this.life = 180; this.pickupDelay = 3; } update(dt) { this.life -= dt; if (this.pickupDelay > 0) this.pickupDelay -= dt; if (this.life <= 0 || (this.bits <= 0 && this.items.every(i => i === null))) this.isDead = true; } }
class FloatingText extends Entity { constructor(x, y, text, color = '#ff8888') { super(x, y, 'floatingText'); this.text = text; this.color = color; this.life = 1; } update(dt) { this.y -= 20 * dt; this.life -= dt; if (this.life <= 0) this.isDead = true; } }

// --- INITIALIZE WORLD ---
function initializeWorld() {
    // FIX: Renamed Armory to Bank
    entities.push(new NPC(6.5 * TILE_SIZE, 3.5 * TILE_SIZE, 'Exchange'));
    entities.push(new NPC(8.5 * TILE_SIZE, 3.5 * TILE_SIZE, 'Bank', '#e3d400')); // Give bank a different color
    generateChunk(0, 0);
    const bossClasses = { 'DREADNOUGHT': Dreadnought, 'SERPENT': SerpentHead, 'ORACLE': TheOracle, 'VOID_HUNTER': VoidHunter };
    for(const bossName in BOSS_LOCATIONS) {
        const loc = BOSS_LOCATIONS[bossName];
        const BossClass = bossClasses[bossName];
        if (BossClass) entities.push(new BossClass(loc.x, loc.y));
    }
    console.log('[SERVER] World initialized and bosses have been spawned.');
}
initializeWorld();


// --- MAIN GAME LOOP ---
function gameLoop() {
    const now = Date.now();
    const dt = (now - lastTime) / 1000.0;
    lastTime = now;

    for (const id in players) { const p = players[id]; const pChunkX = Math.floor(p.x / TILE_SIZE / CHUNK_SIZE); const pChunkY = Math.floor(p.y / TILE_SIZE / CHUNK_SIZE); for(let y = pChunkY - 1; y <= pChunkY + 1; y++) { for(let x = pChunkX - 1; x <= pChunkX + 1; x++) { if (!localWorld[`${x},${y}`]) generateChunk(x, y); } } }

    for (const id in players) if(!players[id].isDead) players[id].update(dt);
    
    for (let i = entities.length - 1; i >= 0; i--) {
        const entity = entities[i];
        if (entity.update) entity.update(dt);
        if (entity.isDead) { entities.splice(i, 1); continue; }
    }

    // Handle Collisions
    for (let i = entities.length - 1; i >= 0; i--) {
        const entity = entities[i];
        if (!entity || entity.isDead) continue;

        if (entity.type === 'Projectile' || entity.type === 'Grenade') {
            const ownerIsPlayer = entity.ownerId.startsWith('player_');
            for(const pid in players) {
                const p = players[pid];
                if (ownerIsPlayer && pid === entity.ownerId) continue;
                if (!p.isDead && Math.hypot(entity.x - p.x, entity.y - p.y) < entity.radius + p.radius) {
                    if(isCity(p.x, p.y) && ownerIsPlayer) continue;
                    p.takeDamage(entity.damage, entity);
                    entity.isDead = true;
                    break;
                }
            }
            if (entity.isDead) continue;

            if (ownerIsPlayer) {
                for(let j = entities.length - 1; j >= 0; j--) {
                    const other = entities[j];
                    if(other instanceof Enemy && Math.hypot(entity.x - other.x, entity.y - other.y) < entity.radius + other.radius){
                        other.takeDamage(entity.damage, {ownerId: entity.ownerId});
                        if (entity.type === 'Grenade') {
                             entities.push(new Shockwave(entity.x, entity.y, entity.explosionRadius, entity.damage, entity.ownerId));
                        }
                        entity.isDead = true;
                        break;
                    }
                }
                 if (entity.isDead) continue;
            }
        }
        else if (entity.type === 'Laser') {
             const ownerIsPlayer = entity.ownerId.startsWith('player_');
             if(ownerIsPlayer) {
                for(const other of entities) {
                    if (other instanceof Enemy) {
                        const dx = other.x - entity.x; const dy = other.y - entity.y; const dist = Math.hypot(dx, dy);
                        if (dist < other.radius) continue; 
                        if (dist < entity.length) {
                            const angleToTarget = Math.atan2(dy, dx);
                            let angleDiff = Math.abs(entity.angle - angleToTarget);
                            if (angleDiff > Math.PI) angleDiff = 2 * Math.PI - angleDiff;
                            if (angleDiff < Math.atan2(other.radius, dist)) {
                                other.takeDamage(entity.damage * dt * 20, {ownerId: entity.ownerId}); // Lasers do damage over time, needs multiplier
                            }
                        }
                    }
                }
             }
        }
        else if(entity.type === 'Shockwave'){
             for(const pid in players) {
                const p = players[pid];
                if (!p.isDead && !entity.hitTargets.includes(pid) && Math.hypot(entity.x - p.x, entity.y - p.y) < entity.radius) {
                    if(isCity(p.x, p.y) && entity.ownerId.startsWith('player_')) continue;
                    p.takeDamage(entity.damage, entity);
                    entity.hitTargets.push(pid);
                }
            }
             for(const other of entities) {
                if (other instanceof Enemy && !entity.hitTargets.includes(other.id) && Math.hypot(entity.x - other.x, entity.y - other.y) < entity.radius) {
                    other.takeDamage(entity.damage, entity);
                    entity.hitTargets.push(other.id);
                }
             }
        }
    }

    for (const entity of entities) { if (entity.type === 'LootDrop') { for (const pid in players) { const player = players[pid]; if (!player.isDead && Math.hypot(entity.x - player.x, entity.y - player.y) < player.radius + 30) { player.dataBits += entity.value; entity.isDead = true; break; } } } }

    for(const bossName in bossRespawnTimers) { if(bossRespawnTimers[bossName] > 0) { bossRespawnTimers[bossName] -= dt; if(bossRespawnTimers[bossName] <= 0) { const loc = BOSS_LOCATIONS[bossName]; const bossClasses = { 'DREADNOUGHT': Dreadnought, 'SERPENT': SerpentHead, 'ORACLE': TheOracle, 'VOID_HUNTER': VoidHunter }; const BossClass = bossClasses[bossName]; if(BossClass) entities.push(new BossClass(loc.x, loc.y)); broadcastMessage({type: 'chat', sender: 'SYSTEM', message: `The ${bossName} has respawned!`, color: '#ff6a00'}); delete bossRespawnTimers[bossName]; } } }

    enemySpawnTimer -= dt;
    if (enemySpawnTimer <= 0) {
        enemySpawnTimer = ENEMY_SPAWN_INTERVAL;
        if (entities.filter(e => e instanceof Enemy).length < MAX_ENEMIES) {
            for(const pid in players){
                const player = players[pid];
                if(isCity(player.x, player.y) || Math.random() < 0.5) continue;
                
                const distFromCenter = Math.hypot(player.x, player.y) / TILE_SIZE;
                const angle = Math.random() * Math.PI * 2;
                const spawnX = player.x + Math.cos(angle) * 1000;
                const spawnY = player.y + Math.sin(angle) * 1000;
                
                if(!isCity(spawnX, spawnY) && !isSolid(getTile(spawnX, spawnY))){
                     const threat = getThreatLevel(spawnX, spawnY);
                     let enemyType;
                     // FIX: Spawn Void Swarmers in outer regions
                     if (distFromCenter > 400 && Math.random() < 0.6) {
                         enemyType = VoidSwarmer;
                     } else if (threat >= 3 && Math.random() < 0.3) {
                         enemyType = Warden;
                     } else if (threat >= 2 && Math.random() < 0.4) {
                         enemyType = Stinger;
                     } else {
                         enemyType = Enemy;
                     }
                     entities.push(new enemyType(spawnX,spawnY, threat));
                }
            }
        }
    }

    const playersData = {};
    for (const id in players) playersData[id] = players[id].getData();
    
    // Custom logic to handle Serpent's circular reference before sending
    const entitiesData = entities.map(e => {
        if (e.type === 'SerpentHead') {
            const headData = e.getData();
            headData.segments = e.segments.map(seg => seg.getData());
            return headData;
        }
        return e.getData();
    });

    const stateToSend = JSON.stringify({ type: 'update', players: playersData, entities: entitiesData });
    wss.clients.forEach(client => { if (client.readyState === WebSocket.OPEN) client.send(stateToSend); });
}
setInterval(gameLoop, 1000 / TICK_RATE);

// --- WEBSOCKET LOGIC ---
function broadcastMessage(message) { const data = JSON.stringify(message); wss.clients.forEach(client => { if (client.readyState === WebSocket.OPEN) client.send(data); }); }
function getSocketByPlayerId(id) { for (const client of wss.clients) { if (client.playerId === id) return client; } return null; }

wss.on('connection', (ws) => {
    const playerId = `player_${Date.now()}_${Math.random().toString(36).substr(2, 5)}`;
    ws.playerId = playerId;
    console.log(`[SERVER] Player ${playerId} connected.`);
    ws.send(JSON.stringify({ type: 'init', playerId: playerId, world: localWorld }));
    ws.send(JSON.stringify({type: 'chat', sender: 'SYSTEM', message: 'Connection established. Welcome to Galactic OS.', color: '#ffff00'}));
    ws.send(JSON.stringify({type: 'chat', sender: 'SYSTEM', message: `DREADNOUGHT detected at [X:150, Y:150].`, color: '#ff6a00'}));
    ws.send(JSON.stringify({type: 'chat', sender: 'SYSTEM', message: `SERPENT detected at [X:-150, Y:-150].`, color: '#33ff99'}));
    ws.send(JSON.stringify({type: 'chat', sender: 'SYSTEM', message: `ORACLE detected at [X:0, Y:300].`, color: '#a832a4'}));
    ws.send(JSON.stringify({type: 'chat', sender: 'SYSTEM', message: `VOID HUNTER detected at [X:300, Y:0].`, color: '#777'}));

    ws.on('message', (message) => {
        try {
            const data = JSON.parse(message);
            const player = players[ws.playerId];

            if (data.type === 'playerInit') { const PlayerClass = { 'Operator': Operator, 'Guardian': Guardian, 'Spectre': Spectre }[data.className]; if (PlayerClass) { players[ws.playerId] = new PlayerClass(ws.playerId, data.username, data.color); } }
            if (data.type === 'playerRespawn') { if (player && player.isDead) player.respawn(); }
            
            if (data.type === 'pickupLoot' && player && !player.isDead) {
                const lootBag = entities.find(e => e.id === data.entityId);
                if (lootBag && Math.hypot(player.x - lootBag.x, player.y - lootBag.y) < 100) {
                    if (lootBag.type === 'PlayerLootBag') {
                        if(data.itemIndex === 'bits' && lootBag.bits > 0) { player.dataBits += lootBag.bits; lootBag.bits = 0; }
                        else { const item = lootBag.items[data.itemIndex]; if (item && player.addToInventory(item)) { lootBag.items[data.itemIndex] = null; } }
                    } else if (lootBag.type === 'EquipmentDrop') { if(player.addToInventory(lootBag.item)) { lootBag.isDead = true; } }
                }
            }

            // Bank and Market logic needs the player to be logged in, but not necessarily alive
            if (player && data.type === 'bankAction') {
                if (!banks[player.username]) banks[player.username] = Array(12).fill(null);
                const bank = banks[player.username];
                if (data.action === 'deposit') {
                    const item = player.inventory[data.itemIndex];
                    const bankIndex = bank.findIndex(slot => slot === null);
                    if (item && bankIndex !== -1) {
                        bank[bankIndex] = item;
                        player.inventory[data.itemIndex] = null;
                    }
                } else if (data.action === 'withdraw') {
                    const item = bank[data.itemIndex];
                    if (item && player.addToInventory(item)) {
                        bank[data.itemIndex] = null;
                    }
                }
                saveData('banks.json', banks);
                ws.send(JSON.stringify({type: 'openBank', bank: bank})); // Refresh client's view
            }

            if (player && data.type === 'marketAction') {
                if (data.action === 'list') {
                    const item = player.inventory[data.itemIndex];
                    const price = parseInt(data.price, 10);
                    if (item && price > 0) {
                        const listingId = `market_${Date.now()}_${player.username}`;
                        marketListings[listingId] = { id: listingId, seller: player.username, item: item, price: price };
                        player.inventory[data.itemIndex] = null;
                    }
                } else if (data.action === 'buy') {
                    const listing = marketListings[data.listingId];
                    if (listing && player.dataBits >= listing.price && player.addToInventory(listing.item)) {
                        player.dataBits -= listing.price;
                        // Give money to seller (if they're online, otherwise it would require a database)
                        const seller = Object.values(players).find(p => p.username === listing.seller);
                        if (seller) seller.dataBits += listing.price;
                        delete marketListings[data.listingId];
                    }
                }
                saveData('market.json', marketListings);
                broadcastMessage({type: 'marketUpdate', marketListings: marketListings});
            }


            if (!player || player.isDead) return;
            if (data.type === 'input') { player.inputs = data.inputs; player.angle = data.angle; }
            if (data.type === 'chat') { broadcastMessage({ type: 'chat', sender: player.username, message: data.message, color: player.color }); }
            if (data.type === 'equipItem') { const item = player.inventory[data.itemIndex]; if (item) { const currentEquipped = player.equipment[item.slot]; player.equipment[item.slot] = item; player.inventory[data.itemIndex] = currentEquipped; player.recalculateStats(); } }
            if (data.type === 'unequipItem') { const item = player.equipment[data.slot]; if (item && player.addToInventory(item)) { player.equipment[data.slot] = null; player.recalculateStats(); } }
            if (data.type === 'dropItem') { let itemToDrop = null; if (data.source === 'inventory') { itemToDrop = player.inventory[data.index]; player.inventory[data.index] = null; } else { itemToDrop = player.equipment[data.index]; player.equipment[data.index] = null; } if (itemToDrop) entities.push(new EquipmentDrop(player.x, player.y, itemToDrop)); player.recalculateStats(); }
            if (data.type === 'buyNpcItem') { const shop = shopInventories[data.shopName]; const shopItem = shop ? shop[data.itemIndex] : null; if(shopItem && player.dataBits >= shopItem.cost) { if(player.addToInventory(shopItem.item)) { player.dataBits -= shopItem.cost; } } }
            if (data.type === 'sellItem') { const item = player.inventory[data.itemIndex]; if(item) { player.dataBits += Math.floor(getItemBaseValue(item) / 3); player.inventory[data.itemIndex] = null; } }
        
        } catch (error) { console.error(`[SERVER] Error processing message from ${ws.playerId}:`, error); }
    });

    ws.on('close', () => {
        const player = players[ws.playerId];
        if (player) {
            console.log(`[SERVER] Player ${player.username} (${ws.playerId}) disconnected.`);
            delete players[ws.playerId];
        }
    });
});