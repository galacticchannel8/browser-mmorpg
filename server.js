// Copyright (c) 2025 GalacticChannel8.com
// All Rights Reserved.
const express = require('express');
const path = require('path');
const http = require('http');

const app = express();
const server = http.createServer(app); // Create an HTTP server

// Serve the index.html file when someone visits the root URL
app.get('/', (req, res) => {
    res.sendFile(path.join(__dirname, 'index.html'));
});


const WebSocket = require('ws');
const fs = require('fs'); // We need the file system to save player data

// --- SETUP ---
// Use the port the hosting service provides, or 8080 for local testing
const PORT = process.env.PORT || 8080;
const TICK_RATE = 30; // 30 updates per second

// Attach WebSocket server to our HTTP server
const wss = new WebSocket.Server({ server });

console.log(`[SERVER] Galactic OS server is operational on port ${PORT}`);

// --- GAME STATE ---
const players = {};
let entities = [];
const TILE_SIZE = 40;
const CHUNK_SIZE = 16;
const MAX_ENEMIES = 225;
const ENEMY_SPAWN_INTERVAL = 1;
const DESPAWN_RADIUS = 2500;
const DESPAWN_TIME = 60;
let enemySpawnTimer = ENEMY_SPAWN_INTERVAL;
let lastTime = Date.now();
const bossRespawnTimers = {};
const activeTrades = {};

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
    return {};
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
const TILE_TYPES = { 0:{n:'V',c:'#05060a'}, 1:{n:'P',c:'#10121f'}, 2:{n:'F',c:'#10121f',wc:'#005f6b'}, 3:{n:'C',c:'#150f1f',wc:'#6b00b3'}, 10:{n:'CF',c:'#1f283e'}, 11:{n:'CW',c:'#00f0ff',wc:'#00f0ff'}, 12:{n:'OW',c:'#a8b3d3',wc:'#a8b3d3'}, 13:{n:'OF',c:'#4a4a52'}, 14:{n:'E',c:'#000000'}, 15:{n:'D', c:'#00f0ff'} };

const cityData = [
    [11,11,11,11,11,11,11,15,15,11,11,11,11,11,11,11],
    [11,10,10,10,10,10,10,10,10,10,10,10,10,10,10,11],
    [11,10,10,10,10,10,10,10,10,10,10,10,10,10,10,11],
    [11,10,10,10,10,10,10,10,10,10,10,10,10,10,10,11],
    [11,10,10,10,10,10,10,10,10,10,10,10,10,10,10,11],
    [15,10,10,10,10,10,10,10,10,10,10,10,10,10,10,15],
    [15,10,10,10,10,10,10,10,10,10,10,10,10,10,10,15],
    [11,10,10,10,10,10,10,10,10,10,10,10,10,10,10,11],
    [11,10,10,10,10,10,10,10,10,10,10,10,10,10,10,11],
    [11,10,10,10,10,10,10,10,10,10,10,10,10,10,10,11],
    [11,10,10,10,10,10,10,10,10,10,10,10,10,10,10,11],
    [11,11,11,11,11,11,11,15,15,11,11,11,11,11,11,11],
];

const CITY_SPAWN_POINT = { x: 8 * TILE_SIZE, y: 8 * TILE_SIZE };
// UPDATED: Adjusted Oracle position to be better centered
const BOSS_LOCATIONS = { DREADNOUGHT: {x: 150*TILE_SIZE, y: 150*TILE_SIZE}, SERPENT: {x: -150*TILE_SIZE, y: -150*TILE_SIZE}, ORACLE: {x: 0.5 * TILE_SIZE, y: 300*TILE_SIZE}, VOID_HUNTER: {x: 300*TILE_SIZE, y: 0} };
const TIER_COLORS = { 1: '#9ea3a1', 2: '#ffffff', 3: '#32a852', 4: '#3273a8', 5: '#a832a4', 6: '#e3d400' };

function createShopWeapon(tier, type) {
    const baseNames = { 'Scatter': 'Scattergun', 'Beam': 'Beam Emitter', 'Launcher': 'Ordnance Launcher' };
    return {
        id: `wep_${type.toLowerCase()}_${tier}`,
        slot: 'Weapon',
        tier,
        type,
        name: `T${tier} ${baseNames[type]}`,
        stats: {} 
    };
}
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

function createShopItem(tier, slot) {
    const item = { id: `${slot}_shop_${tier}`, slot, tier, stats: {} };
    switch(slot) {
        case 'Weapon':
            item.name = `W1 Emitter`;
            item.type = 'Default';
            item.stats = { damage: 2 };
            break;
        case 'Module':
            item.name = `M1`;
            item.stats = { damage: 5, fireRate: 0.5 };
            break;
        case 'Plating':
            item.name = `P1`;
            item.stats = { maxHealth: 10, defense: 1 };
            break;
        case 'Utility':
            item.name = `U1`;
            item.stats = { speed: 0.1, energyRegen: 2 };
            break;
    }
    return item;
}

const shopInventories = {
    'Exchange': [
        { item: createShopItem(1, 'Weapon'), cost: 75 },
        { item: createShopItem(1, 'Plating'), cost: 50 },
        { item: createShopItem(1, 'Module'), cost: 50 },
        { item: createShopItem(1, 'Utility'), cost: 50 },
        { item: createShopWeapon(1, 'Scatter'), cost: 200 },
        { item: createShopWeapon(1, 'Beam'), cost: 225 },
        { item: createShopWeapon(1, 'Launcher'), cost: 250 },
        { item: generateEquipment(2), cost: 350 }
    ]
};

const localWorld = {};
function generateChunk(chunkX, chunkY) { const key = `${chunkX},${chunkY}`; if (localWorld[key]) return; const chunk = { tiles: Array(CHUNK_SIZE * CHUNK_SIZE).fill(1) }; for(const bossName in BOSS_LOCATIONS) { const loc = BOSS_LOCATIONS[bossName]; const bossChunkX = Math.floor(loc.x / TILE_SIZE / CHUNK_SIZE); const bossChunkY = Math.floor(loc.y / TILE_SIZE / CHUNK_SIZE); if(chunkX === bossChunkX && chunkY === bossChunkY){ for (let y = 0; y < CHUNK_SIZE; y++) for (let x = 0; x < CHUNK_SIZE; x++) { const worldX = (chunkX * CHUNK_SIZE + x) * TILE_SIZE; const worldY = (chunkY * CHUNK_SIZE + y) * TILE_SIZE; const dist = Math.hypot(worldX - loc.x, worldY - loc.y); if (dist < 10 * TILE_SIZE) chunk.tiles[y * CHUNK_SIZE + x] = 13; 
    // UPDATED: Arena wall generation logic thickened to prevent gaps
    if (dist >= 9 * TILE_SIZE && dist < 10.5 * TILE_SIZE) chunk.tiles[y * CHUNK_SIZE + x] = 12; 
} localWorld[key] = chunk; broadcastMessage({type: 'worldChunkUpdate', key: key, chunk: chunk}); return;} } if (chunkX === 0 && chunkY === 0) { for (let y = 0; y < CHUNK_SIZE; y++) for (let x = 0; x < CHUNK_SIZE; x++) { chunk.tiles[y * CHUNK_SIZE + x] = cityData[y]?.[x] ?? 10; } } else {
        for (let y = 0; y < CHUNK_SIZE; y++) {
            for (let x = 0; x < CHUNK_SIZE; x++) {
                const wX = chunkX * CHUNK_SIZE + x, wY = chunkY * CHUNK_SIZE + y;
                const bV = (biomeNoise.get(wX / 200, wY / 200) + 1) / 2;
                const structureNoise = (perlin.get(wX / 30, wY / 30) + 1) / 2;

                let t = 1; 
                let wallType = 0;

                if (bV < 0.4) wallType = 2; 
                else if (bV > 0.85) wallType = 3; 
                
                if (wallType !== 0) {
                    if (structureNoise > 0.45 && structureNoise < 0.55) {
                        t = wallType;
                    } else {
                        t = 1;
                    }
                }
                chunk.tiles[y * CHUNK_SIZE + x] = t;
            }
        }
    } localWorld[key] = chunk; broadcastMessage({type: 'worldChunkUpdate', key: key, chunk: chunk}); }
function getTile(worldX, worldY) { const cX = Math.floor(worldX / TILE_SIZE); const cY = Math.floor(worldY / TILE_SIZE); const chX = Math.floor(cX / CHUNK_SIZE); const chY = Math.floor(cY / CHUNK_SIZE); const key = `${chX},${chY}`; if (!localWorld[key]) generateChunk(chX, chY); const chunk = localWorld[key]; const tX = (cX % CHUNK_SIZE + CHUNK_SIZE) % CHUNK_SIZE; const tY = (cY % CHUNK_SIZE + CHUNK_SIZE) % CHUNK_SIZE; return chunk.tiles[tY * CHUNK_SIZE + tX]; }
function isSolid(tileType) { return TILE_TYPES[tileType]?.wc !== undefined; }
function isCity(worldX, worldY) { return Math.floor(worldX / TILE_SIZE / CHUNK_SIZE) === 0 && Math.floor(worldY / TILE_SIZE / CHUNK_SIZE) === 0; }
function getThreatLevel(x, y) { if(isCity(x,y)) return 0; const distFromSpawn = Math.hypot(x, y) / TILE_SIZE; if (distFromSpawn < 100) return 1; if (distFromSpawn < 200) return 2; if (distFromSpawn < 300) return 3; if (distFromSpawn < 500) return 4; return 5; }
function getItemBaseValue(item) { if (!item) return 0; return (item.tier * item.tier) * 20; }

// --- PLAYER & SUBCLASSES (SERVER-SIDE) ---
class Player {
    constructor(id, username, color, className) {
        this.id = id;
        this.username = username;
        this.color = color;
        this.className = className;
        this.x = CITY_SPAWN_POINT.x;
        this.y = CITY_SPAWN_POINT.y;
        this.radius = 15;
        this.angle = 0;
        this.dataBits = 0;
        this.equipment = { Weapon: null, Module: null, Plating: null, Utility: null };
        this.inventory = Array(12).fill(null);
        this.level = 1;
        this.xp = 0;
        this.xpToNextLevel = this.calculateXpToNextLevel();
        this.stats = {};
        this.recalculateStats();
        this.health = this.stats.maxHealth;
        this.energy = this.stats.maxEnergy;
        this.gunCooldown = 0;
        this.meleeCooldown = 0;
        this.abilityCooldown = 0;
        this.isSlowed = false;
        this.isDead = false;
        this.isBoosting = false;
        this.canBoost = true;
        this.timeSinceLastHit = 0;
        this.REGEN_DELAY = 15;
        
        this.isInvisible = false;
        this.shieldActive = false;

        this.isTeleporting = false;
        this.teleportTimer = 0;
        this.TELEPORT_CHARGE_TIME = 5;
        this.teleportCooldown = 0;
        this.teleportMaxCooldown = 600; 

        this.trade = {
            partnerId: null,
            offerItems: [],
            offerBits: 0,
            acceptedStage1: false,
            acceptedStage2: false
        };
        this.inputs = { w: false, a: false, s: false, d: false, h: false, shift: false, q: false, e: false, space: false, mouse: { down: false } };
    }
    
    calculateXpToNextLevel() {
        return Math.floor(100 * Math.pow(1.15, this.level - 1));
    }

    addXp(amount) {
        if (this.isDead) return;
        this.xp += amount;
        while (this.xp >= this.xpToNextLevel) {
            this.xp -= this.xpToNextLevel;
            this.level++;
            this.xpToNextLevel = this.calculateXpToNextLevel();
            this.recalculateStats();
            this.health = this.stats.maxHealth;
            this.energy = this.stats.maxEnergy;
        }
    }

    recalculateStats() {
        const base = { maxHealth: 100, maxEnergy: 300, defense: 0, speed: 4.0, fireRate: 2, damage: 8, energyRegen: 25, healthRegen: 1, ...this.classStats };
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

        if (this.trade.partnerId) {
            this.isBoosting = false;
            return;
        }

        if (this.isTeleporting) {
            this.teleportTimer -= dt;
            if (this.teleportTimer <= 0) {
                this.isTeleporting = false;
                this.x = CITY_SPAWN_POINT.x;
                this.y = CITY_SPAWN_POINT.y;
                this.teleportCooldown = this.teleportMaxCooldown;
                broadcastMessage({type: 'sfx', effect: 'teleportEnd', x: this.x, y: this.y, color: this.color});
            }
             if (this.inputs.w || this.inputs.a || this.inputs.s || this.inputs.d || this.inputs.space || this.inputs.mouse.down) {
                this.isTeleporting = false;
            } else {
                broadcastMessage({type: 'sfx', effect: 'teleportCharge', x: this.x, y: this.y, color: this.color});
            }
            return; 
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

        const forward = (this.inputs.w ? 1 : 0) - (this.inputs.s ? 1 : 0); const strafe = (this.inputs.d ? 1 : 0) - (this.inputs.a ? 1 : 0); const moveX = Math.cos(this.angle) * forward - Math.sin(this.angle) * strafe; const moveY = Math.sin(this.angle) * forward + Math.cos(this.angle) * strafe; const mag = Math.hypot(moveX, moveY); if (mag > 0) { const timeAdjustedSpeed = currentSpeed * (dt * 60); const finalMoveX = mag > 1 ? (moveX / mag) * timeAdjustedSpeed : moveX * timeAdjustedSpeed; const finalMoveY = mag > 1 ? (moveY / mag) * timeAdjustedSpeed : moveY * timeAdjustedSpeed; const nX = this.x + finalMoveX; const nY = this.y + finalMoveY; if (!isSolid(getTile(nX, this.y))) this.x = nX; if (!isSolid(getTile(this.x, nY))) this.y = nY; }
        
        this.gunCooldown -= dt;
        this.meleeCooldown -= dt;
        this.teleportCooldown = Math.max(0, this.teleportCooldown - dt);
        this.abilityCooldown = Math.max(0, this.abilityCooldown - dt);

        if (this.inputs.mouse.down && this.gunCooldown <= 0) this.fireWeapon();
        if (this.inputs.space && this.meleeCooldown <= 0) this.fireMelee();
        if (this.inputs.h && this.teleportCooldown <= 0 && !this.isTeleporting) {
            this.isTeleporting = true;
            this.teleportTimer = this.TELEPORT_CHARGE_TIME;
        }
        if (this.inputs.q) { this.useAbility(); }
        this.updateAbility(dt);
        if (this.inputs.e) { this.attemptInteraction(); this.inputs.e = false; }
    }

    fireWeapon() {
        if (this.trade.partnerId || this.isTeleporting) return;
        const weapon = this.equipment.Weapon || { type: 'Default' };
        this.gunCooldown = 1 / this.stats.fireRate;
        // UPDATED: Added a source object for better death messages
        const projectileData = {
            source: { id: this.id, name: this.username },
            angle: this.angle,
            color: this.color,
            damage: this.stats.damage
        };
        switch(weapon.type) {
            case 'Beam': if(this.energy > 5){ this.energy -= 5; entities.push(new Laser(this.x, this.y, projectileData, 800)); } break;
            case 'Scatter': for(let i=0; i < 5; i++) { projectileData.angle = this.angle + (Math.random() - 0.5) * 0.4; entities.push(new Projectile(this.x, this.y, projectileData)); } break;
            case 'Launcher': entities.push(new Grenade(this.x, this.y, projectileData, 60)); break;
            default: entities.push(new Projectile(this.x, this.y, projectileData)); break;
        }
    }

    fireMelee() {
        if (this.trade.partnerId || this.isTeleporting) return;
        this.meleeCooldown = 0.8;
        const meleeDamage = this.stats.damage * 1.5;
        // UPDATED: Added a source object for better death messages
        const source = { id: this.id, name: this.username };
        entities.push(new MeleeSlash(this.x, this.y, this.angle, source, meleeDamage, this.color));
    }

    takeDamage(amount, damager = null) {
        if(this.isDead) return;
        this.timeSinceLastHit = 0;
        if(this.isTeleporting) this.isTeleporting = false;
        if (this.trade.partnerId) {
            cancelTrade(this.id, "Trade cancelled due to combat.");
        }

        const damageTaken = Math.max(1, amount - this.stats.defense);
        this.health = Math.max(0, this.health - damageTaken);
        entities.push(new FloatingText(this.x, this.y - this.radius, `-${Math.floor(damageTaken)}`));
        if (this.health <= 0) this.die(damager);
    }

    die(killer = null) {
        if (this.isDead) return; 

        if (this.trade.partnerId) {
            cancelTrade(this.id, `${this.username} has disconnected.`);
        }
        this.isDead = true;

        // UPDATED: Logic to get a specific killer name for the tombstone
        let causeOfDeath = 'The Void';
        if (killer && killer.source) {
            causeOfDeath = killer.source.name;
        }

        let lootBagId = null;
        const droppedItems = [...Object.values(this.equipment), ...this.inventory].filter(item => item !== null);
        const droppedBits = Math.floor(this.dataBits * 0.8);
        if(droppedItems.length > 0 || droppedBits > 0) {
            const lootBag = new PlayerLootBag(this.x, this.y, droppedItems, droppedBits, this.color);
            entities.push(lootBag);
            lootBagId = lootBag.id;
        }
        
        entities.push(new Tombstone(this.x, this.y, this.username, causeOfDeath, this.color, lootBagId));
        
        const playerSocket = getSocketByPlayerId(this.id);
        if (playerSocket) playerSocket.send(JSON.stringify({ type: 'playerDied' }));
    }

    respawn() {
        this.isDead = false;
        this.equipment = { Weapon: null, Module: null, Plating: null, Utility: null };
        this.inventory = Array(12).fill(null);
        this.dataBits = 0;
        this.level = 1;
        this.xp = 0;
        this.xpToNextLevel = this.calculateXpToNextLevel();
        this.recalculateStats();
        this.health = this.stats.maxHealth;
        this.energy = this.stats.maxEnergy;
    }

    addToInventory(item) {
        if (!item) return false;
        const index = this.inventory.findIndex(slot => slot === null);
        if (index !== -1) {
            this.inventory[index] = { ...item };
            this.recalculateStats();
            return true;
        }
        return false;
    }

    attemptInteraction() {
        if (this.isTeleporting) return;
        const interactRadius = 80;

        for(const entity of entities) {
            if(Math.hypot(this.x - entity.x, this.y - entity.y) < interactRadius) {
                if (entity instanceof MedBay) {
                    if (this.health < this.stats.maxHealth) {
                        this.health = this.stats.maxHealth;
                        entities.push(new FloatingText(this.x, this.y + this.radius, `+HP`, '#33ff99'));
                    }
                    return;
                }
                if (entity instanceof AdminPanel) {
                    if (this.username === "GalacticChannel8") {
                        const playerSocket = getSocketByPlayerId(this.id);
                        if (playerSocket) playerSocket.send(JSON.stringify({type: 'chat', sender: 'SYSTEM', message: 'Admin Panel Authenticated.', color: '#ff3355'}));
                    }
                    return;
                }
                if (entity instanceof Portal) {
                     const playerSocket = getSocketByPlayerId(this.id);
                     if (playerSocket) playerSocket.send(JSON.stringify({type: 'chat', sender: 'SYSTEM', message: 'Teleportation System [OFFLINE].', color: '#f07cff'}));
                    return;
                }
                if (entity instanceof NPC) {
                    const playerSocket = getSocketByPlayerId(this.id);
                    if (playerSocket) {
                        if (entity.name === "Bank") {
                            if (!banks[this.username]) banks[this.username] = [];
                            playerSocket.send(JSON.stringify({type: 'openBank', bank: banks[this.username]}));
                        } else {
                            playerSocket.send(JSON.stringify({type: 'openShop', npcName: entity.name, inventory: shopInventories[entity.name], marketListings: marketListings }));
                        }
                    }
                    return;
                }
                if (entity.type === 'PlayerLootBag' && entity.pickupDelay <= 0) {
                    if (entity.bits > 0) { this.dataBits += entity.bits; entity.bits = 0; }
                    entity.items.forEach((item, index) => { if (item && this.addToInventory(item)) { entity.items[index] = null; } });
                    return;
                }
            }
        }

        const closestItem = entities.filter(e => (e.type === 'EquipmentDrop') && e.pickupDelay <= 0 && Math.hypot(e.x - this.x, e.y - this.y) < interactRadius)
            .sort((a,b) => Math.hypot(a.x - this.x, a.y - this.y) - Math.hypot(b.x - this.x, b.y - this.y))[0];
        if(closestItem) {
            if(this.addToInventory(closestItem.item)) closestItem.isDead = true;
        }
    }

    useAbility() {}
    updateAbility(dt) {}

    getData() {
        return {
            id: this.id, x: this.x, y: this.y, angle: this.angle, color: this.color, username: this.username,
            health: this.health, stats: this.stats, energy: this.energy, abilityCooldown: this.abilityCooldown,
            teleportCooldown: this.teleportCooldown, dataBits: this.dataBits, inventory: this.inventory,
            equipment: this.equipment, isInvisible: this.isInvisible, shieldActive: this.shieldActive,
            isDead: this.isDead, isBoosting: this.isBoosting, className: this.className, level: this.level,
            xp: this.xp, xpToNextLevel: this.xpToNextLevel,
            isTeleporting: this.isTeleporting, teleportTimer: this.teleportTimer, TELEPORT_CHARGE_TIME: this.TELEPORT_CHARGE_TIME
        };
    }
}

class Operator extends Player { constructor(id, u, c) { super(id, u, c, 'Operator'); this.classStats = { speed: 4.5, maxHealth: 80 }; this.isInvisible = false; this.invisDuration = 0; this.recalculateStats(); } useAbility() { if (this.abilityCooldown <= 0 && !this.trade.partnerId && !this.isTeleporting) { this.abilityCooldown = 12; this.isInvisible = true; this.invisDuration = 3; } } updateAbility(dt) { if (this.isInvisible) { this.invisDuration -= dt; if (this.invisDuration <= 0) this.isInvisible = false; } } }
class Guardian extends Player { constructor(id, u, c) { super(id, u, c, 'Guardian'); this.classStats = { speed: 3.5, maxHealth: 150 }; this.shieldActive = false; this.shieldDuration = 0; this.shieldHealth = 0; this.recalculateStats(); } useAbility() { if (this.abilityCooldown <= 0 && !this.trade.partnerId && !this.isTeleporting) { this.abilityCooldown = 20; this.shieldActive = true; this.shieldDuration = 5; this.shieldHealth = 100; } } updateAbility(dt) { if (this.shieldActive) { this.shieldDuration -= dt; if (this.shieldDuration <= 0) this.shieldActive = false; } } takeDamage(amount, damager = null) { this.timeSinceLastHit = 0; if(this.isTeleporting) this.isTeleporting = false; if (this.shieldActive) { const damageAbsorbed = Math.min(this.shieldHealth, amount); this.shieldHealth -= damageAbsorbed; const damageLeft = amount - damageAbsorbed; if (this.shieldHealth <= 0) this.shieldActive = false; if (damageLeft > 0) super.takeDamage(damageLeft, damager); } else { super.takeDamage(amount, damager); } } }
class Spectre extends Player {
    constructor(id, u, c) { super(id, u, c, 'Spectre'); this.recalculateStats(); }
    useAbility() {
        if (this.abilityCooldown <= 0 && !this.trade.partnerId && !this.isTeleporting) {
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

// ... CONTINUATION OF SCRIPT ...

// --- ENTITY & ENEMY CLASSES (SERVER-SIDE) ---
class Entity { constructor(x, y, type) { this.id = `${type}_${Date.now()}_${Math.random()}`; this.x = x; this.y = y; this.type = type; } update(dt) {} getData() { const data = {}; for(const key in this) { if (typeof this[key] !== 'function' && key !== 'owner' && key !== 'head' && key !== 'segments') data[key] = this[key]; } return data; } }

class Enemy extends Entity {
    constructor(x, y, threatLevel, type = 'Enemy') {
        super(x, y, type);
        this.threatLevel = threatLevel; this.radius = 12; this.speed = 2.5;
        this.health = 50; this.maxHealth = 50;
        this.color = '#ff3355'; this.aggroRadius = 350; this.deAggroRadius = this.aggroRadius * 1.5;
        this.wanderTarget = null; this.wanderTimer = 0;
        this.xpValue = 15 * threatLevel;
        this.timeOutsidePlayerRange = 0;
        this.isBossComponent = false;
        this.applyThreatLevel();
    }
    applyThreatLevel() { this.health = this.maxHealth = this.health * (1 + (this.threatLevel-1)*0.6); this.damageMultiplier = 1 + (this.threatLevel-1)*0.4; }
    update(dt) {
        let targetPlayer = null;
        let closestDist = Infinity;
        for(const pid in players){
            const player = players[pid];
            if (player.isDead || player.isInvisible || player.trade.partnerId || player.isTeleporting) continue;
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
                targetPlayer.takeDamage(40 * this.damageMultiplier * dt, { source: { name: this.type }});
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
        entities.push(new FloatingText(this.x, this.y - this.radius, `-${Math.floor(amount)}`, '#ffffff'));
        if (this.health <= 0 && !this.isDead) {
            this.isDead = true;
            if (damager && damager.source && players[damager.source.id]) {
                players[damager.source.id].addXp(this.xpValue);
            }
            for (let i = 0; i < 2; i++) entities.push(new LootDrop(this.x, this.y, this.threatLevel));
            const dropChance = 0.01 + (this.threatLevel * 0.025);
            if (Math.random() < dropChance) {
                const tierBonus = (Math.random() < 0.05) ? 2 : Math.floor(Math.random() * 2);
                const itemTier = this.threatLevel + tierBonus;
                entities.push(new EquipmentDrop(this.x, this.y, generateEquipment(itemTier)));
            }
        }
    }
}
class Stinger extends Enemy { constructor(x, y, tL) { super(x, y, tL, 'Stinger'); this.radius = 10; this.speed = 4; this.health = this.maxHealth = 40; this.color = '#f07cff'; this.shootCooldown = 1.6; this.xpValue = 20 * tL; this.applyThreatLevel(); } update(dt) { super.update(dt); this.shootCooldown -= dt; if (this.shootCooldown <= 0) { this.shootCooldown = 1.6; for(const pid in players){ const player = players[pid]; if(!player.isDead && !player.isTeleporting && Math.hypot(player.x - this.x, player.y - this.y) < this.aggroRadius){ 
    const p = { source: { id: this.id, name: this.type }, angle: Math.atan2(player.y - this.y, player.x - this.x), color: this.color, damage: 30*this.damageMultiplier }; 
    entities.push(new Projectile(this.x, this.y, p, 0.8)); break; } } } } }
class VoidSwarmer extends Enemy {
    constructor(x, y, tL) {
        super(x, y, tL, 'VoidSwarmer');
        this.radius = 8; this.speed = 5; this.health = this.maxHealth = 25; this.color = '#7d3c98';
        this.xpValue = 12 * tL;
        this.applyThreatLevel();
    }
}
class Warden extends Enemy {
    constructor(x, y, tL) {
        super(x, y, tL, 'Warden');
        this.radius = 18; this.speed = 1.8; this.health = this.maxHealth = 250; this.color = '#e3d400';
        this.abilityCooldown = 5; this.shield = 100; this.maxShield = 100;
        this.xpValue = 60 * tL; this.applyThreatLevel();
    }
    update(dt) {
        super.update(dt);
        this.abilityCooldown -= dt;
        if(this.abilityCooldown <= 0) {
            this.abilityCooldown = 5;
            for(const pid in players) {
                const player = players[pid];
                const dist = Math.hypot(player.x-this.x, player.y-this.y);
                if(!player.isDead && !player.isTeleporting && dist < 250) {
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
            entities.push(new FloatingText(this.x, this.y - this.radius, `-${Math.floor(amount)}`, '#e3d400'));
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
class GravityWell extends Enemy {
    constructor(x, y, tL) {
        super(x, y, tL, 'GravityWell');
        this.radius = 20;
        this.speed = 0;
        this.health = this.maxHealth = 999999;
        this.color = '#1a1a1a';
        this.xpValue = 0;
        this.pullRadius = 300;
        this.pullStrength = 25;
    }
    update(dt) {
        for (const pid in players) {
            const player = players[pid];
            const dist = Math.hypot(player.x - this.x, player.y - this.y);

            if (dist < this.radius && !player.isDead) {
                player.die(this);
                continue;
            }
            
            if (!player.isDead && !player.isTeleporting && dist < this.pullRadius) {
                const pullForce = (1 - (dist / this.pullRadius)) * this.pullStrength;
                const angle = Math.atan2(this.y - player.y, this.x - player.x);
                let moveX = Math.cos(angle) * pullForce * (player.isBoosting ? 0.5 : 1);
                let moveY = Math.sin(angle) * pullForce * (player.isBoosting ? 0.5 : 1);

                const nX = player.x + moveX;
                const nY = player.y + moveY;
                if (!isSolid(getTile(nX, player.y))) player.x = nX;
                if (!isSolid(getTile(player.x, nY))) player.y = nY;
            }
        }

        for (const entity of entities) {
            if (entity === this || entity.isDead) continue;
            const dist = Math.hypot(entity.x - this.x, entity.y - this.y);
            if (dist < this.radius) {
                if (entity instanceof Enemy && !entity.isBoss) {
                    entity.isDead = true;
                } else if (entity.type === 'Projectile' || entity.type === 'Grenade' || entity.type === 'LootDrop' || entity.type === 'EquipmentDrop') {
                    entity.isDead = true;
                }
            }
        }
    }
    takeDamage(amount, damager = null) {
        return;
    }
}

// UPDATED: All WorldBosses now have leashing capabilities
class WorldBoss extends Enemy {
    constructor(x, y, name, color, hp, type) {
        super(x, y, 5, type);
        this.isBoss = true;
        this.bossName = name;
        this.color = color;
        this.health = this.maxHealth = hp;
        this.radius = 80;
        this.aggroRadius = 1500; // Standard aggro radius
        this.attackPhase = 'idle';
        this.attackTimer = 0;
        this.xpValue = 5000;
        this.spawnX = x;
        this.spawnY = y;
        this.leashRadius = 2500; // How far they can be pulled
    }
    takeDamage(amount, damager = null) {
        this.health -= amount;
        entities.push(new FloatingText(this.x, this.y - this.radius, `-${Math.floor(amount)}`, '#ffffff'));
        if (this.health <= 0 && !this.isDead) {
            this.isDead = true;
            if(damager && damager.source && players[damager.source.id]) {
                broadcastMessage({ type: 'chat', sender: 'SYSTEM', message: `${players[damager.source.id].username} has defeated the ${this.bossName}!`, color: '#ff00ff' });
                players[damager.source.id].addXp(this.xpValue);
            }
            bossRespawnTimers[this.bossName] = 300;
            for (let i = 0; i < 2; i++) entities.push(new EquipmentDrop(this.x, this.y, generateEquipment(5)));
            if (Math.random() < 0.5) {
                for (let i = 0; i < 3; i++) {
                    const tier = 4 + Math.floor(Math.random() * 2);
                    entities.push(new EquipmentDrop(this.x, this.y, generateEquipment(tier)));
                }
            }
        }
    }
}
class Dreadnought extends WorldBoss {
    constructor(x, y) { super(x, y, "DREADNOUGHT", '#ff6a00', 15000, "Dreadnought"); }
    update(dt) {
        const distFromSpawn = Math.hypot(this.x - this.spawnX, this.y - this.spawnY);
        if (distFromSpawn > this.leashRadius) {
            const angleToSpawn = Math.atan2(this.spawnY - this.y, this.spawnX - this.x);
            this.x += Math.cos(angleToSpawn) * this.speed * (dt * 60);
            this.y += Math.sin(angleToSpawn) * this.speed * (dt * 60);
            return;
        }

        let targetPlayer = null;
        for(const pid in players) { const p = players[pid]; if(!p.isDead && !p.isTeleporting && Math.hypot(p.x - this.x, p.y - this.y) < this.aggroRadius) { targetPlayer = p; break; }}
        if (!targetPlayer) return;
        const dX = targetPlayer.x - this.x, dY = targetPlayer.y - this.y; const dP = Math.hypot(dX, dY);
        if(dP > 400 && !isCity(this.x, this.y)) { this.x += (dX / dP) * this.speed * (dt * 60); this.y += (dY / dP) * this.speed * (dt * 60); }
        this.attackTimer -= dt;
        if(this.attackTimer <= 0) {
            const p = { source: { id: this.id, name: this.bossName }, angle: Math.atan2(dY, dX), color: this.color, damage: 80 };
            switch(this.attackPhase) {
                case 'idle': case 'barrage':
                    this.attackTimer = 3;
                    for(let i=0;i<10;i++) { setTimeout(() => { if(this.isDead) return; try { const currentTarget = players[Object.keys(players).find(id => players[id] === targetPlayer)]; if(!currentTarget) return; const targetAngle = Math.atan2(currentTarget.y-this.y, currentTarget.x-this.x); p.angle = targetAngle + (Math.random() - 0.5) * 0.3; entities.push(new Projectile(this.x, this.y, p, 1.5, 10)); } catch(e){} }, i * 100); }
                    this.attackPhase = 'mortar'; break;
                case 'mortar':
                    this.attackTimer = 5;
                    entities.push(new MortarProjectile(this.x, this.y, targetPlayer.x, targetPlayer.y, { id: this.id, name: this.bossName }));
                    this.attackPhase = 'barrage'; break;
            }
        }
    }
}
// UPDATED: Serpent leashing and reduced aggro range
class SerpentHead extends WorldBoss {
    constructor(x, y) {
        super(x, y, "SERPENT", '#33ff99', 12000, "SerpentHead");
        this.radius = 30;
        this.aggroRadius = 1200; // Reduced from default
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
        const distFromSpawn = Math.hypot(this.x - this.spawnX, this.y - this.spawnY);
        let targetPlayer=null; for(const pid in players){const p=players[pid]; if(!p.isDead && !p.isTeleporting && Math.hypot(p.x-this.x,p.y-this.y) < this.aggroRadius){targetPlayer=p; break;}}
        
        if (distFromSpawn > this.leashRadius || !targetPlayer) {
            if (distFromSpawn > 50) { // Return to spawn if far away
                const angleToSpawn = Math.atan2(this.spawnY - this.y, this.spawnX - this.x);
                this.x += Math.cos(angleToSpawn) * this.speed * (dt * 60);
                this.y += Math.sin(angleToSpawn) * this.speed * (dt * 60);
            }
        } else if (targetPlayer) {
            const dX = targetPlayer.x - this.x;
            const dY = targetPlayer.y - this.y;
            const distToPlayer = Math.hypot(dX, dY);
            if (distToPlayer > 300 && !isCity(this.x, this.y)) {
                const timeAdjustedSpeed = this.speed * (dt * 60);
                this.x += (dX / distToPlayer) * timeAdjustedSpeed;
                this.y += (dY / distToPlayer) * timeAdjustedSpeed;
            }

            this.attackTimer -= dt;
            if(this.attackTimer <= 0) {
                this.attackTimer = 0.3;
                const proj = { source: { id: this.id, name: this.bossName }, angle: Math.atan2(targetPlayer.y-this.y, targetPlayer.x-this.x), color: this.color, damage: 60 };
                entities.push(new Projectile(this.x, this.y, proj, 1.2, 8));
            }
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
}
class SerpentBody extends Enemy {
    constructor(x, y, head) {
        super(x, y, 5, 'SerpentBody');
        this.isBossComponent = true; 
        this.head = head;
        this.radius = 25;
        this.health = this.maxHealth = 2000;
        this.color = '#29cc7a';
        this.shootCooldown = Math.random() * 3 + 2;
        this.xpValue = 250;
    }
    follow(leader, dt) {
        const dX = leader.x - this.x, dY = leader.y - this.y;
        const dist = Math.hypot(dX, dY);
        const targetDist = this.radius + leader.radius - 15;
        if(dist > targetDist) {
            const timeAdjustedSpeed = 12 * (dt * 60);
            this.x += (dX / dist) * timeAdjustedSpeed;
            this.y += (dY / dist) * timeAdjustedSpeed;
        }
    }
    update(dt) {
        this.shootCooldown -= dt;
        if(this.shootCooldown <= 0) {
            this.shootCooldown = Math.random() * 3 + 2;
            let targetPlayer=null; for(const pid in players){const p=players[pid]; if(!p.isDead && !p.isTeleporting && Math.hypot(p.x-this.x,p.y-this.y) < this.aggroRadius){targetPlayer=p; break;}}
            if (targetPlayer) {
                 const p = { source: {id: this.id, name: this.type}, angle: Math.atan2(targetPlayer.y - this.y, targetPlayer.x - this.x), color: this.color, damage: 40 };
                 entities.push(new Projectile(this.x, this.y, p));
            }
        }
    }
}
// UPDATED: Oracle is now stationary
class TheOracle extends WorldBoss {
    constructor(x,y) { super(x,y, "THE ORACLE", '#a832a4', 10000, "TheOracle"); }
    update(dt) {
        // This boss does not move.
        this.attackTimer -= dt;
        if(this.attackTimer <= 0) {
            const p = { source: { id: this.id, name: this.bossName }, color: this.color, damage: 50};
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
// UPDATED: Void Hunter has new predatory AI
class VoidHunter extends WorldBoss {
    constructor(x, y) { 
        super(x, y, "VOID HUNTER", '#1f283e', 20000, "aclysmHunter"); 
        this.radius = 25; 
        this.isInvisible = true; 
        this.attackTimer = 3;
        this.lockedTargetId = null; // New property for predatory AI
        this.leashRadius = Infinity; // This boss does not leash
    }
    update(dt) {
        // Predatory AI logic
        let targetPlayer = this.lockedTargetId ? players[this.lockedTargetId] : null;

        // Reset if target is dead or disconnected
        if (targetPlayer && (targetPlayer.isDead || !targetPlayer)) {
            this.lockedTargetId = null;
            this.isInvisible = true;
            this.x = this.spawnX;
            this.y = this.spawnY;
            return;
        }

        // Find a new target if it doesn't have one
        if (!targetPlayer) {
            for(const pid in players){
                const p = players[pid]; 
                if(!p.isDead && !p.isTeleporting && Math.hypot(p.x - this.x, p.y - this.y) < this.aggroRadius) {
                    this.lockedTargetId = pid;
                    targetPlayer = p;
                    break;
                }
            }
        }

        if (!targetPlayer) { // Still no target, do nothing
            this.isInvisible = true;
            return;
        }

        // --- Standard attack logic, but only against the locked target ---
        const dX = targetPlayer.x - this.x, dY = targetPlayer.y - this.y;
        this.x += (dX / Math.hypot(dX, dY)) * this.speed * (dt * 60);
        this.y += (dY / Math.hypot(dX, dY)) * this.speed * (dt * 60);

        this.attackTimer -= dt;
        if(this.attackTimer <= 0) {
            this.attackTimer = 5;
            this.isInvisible = false;
            setTimeout(() => {
                if(this.isDead) return;
                const currentTarget = players[this.lockedTargetId];
                if (!currentTarget) return; // Target might have disconnected during the wait
                for(let i=0; i<10; i++) {
                    const proj = { source: {id: this.id, name: this.bossName }, angle: Math.atan2(currentTarget.y-this.y, currentTarget.x-this.x) + (Math.random()-0.5)*0.8, color: '#ff3355', damage: 120};
                    entities.push(new Projectile(this.x, this.y, proj, 0.5));
                }
                setTimeout(() => {
                    if(this.isDead) return;
                    this.isInvisible = true;
                    const angle = Math.random()*Math.PI*2;
                    this.x = currentTarget.x + Math.cos(angle)*400;
                    this.y = currentTarget.y + Math.sin(angle)*400;
                }, 1000);
            }, 1000);
        }
    }
}

class MeleeSlash extends Entity {
    constructor(x, y, angle, source, damage, color) { // UPDATED: Takes a source object now
        super(x, y, 'MeleeSlash');
        this.source = source;
        this.angle = angle;
        this.damage = damage;
        this.color = color;
        this.life = 0.2;
        this.hitTargets = [];
        this.radius = 60;
        this.arc = Math.PI / 2;
    }
    update(dt) {
        this.life -= dt;
        if (this.life <= 0) {
            this.isDead = true;
        }
    }
}

class Projectile extends Entity { constructor(x,y,p,l=1.5,r=4){ super(x,y,'Projectile'); this.source = p.source; this.angle = p.angle; this.radius=r; this.speed=15; this.life=l; this.color=p.color; this.damage=p.damage;} update(dt){ this.x+=Math.cos(this.angle)*this.speed*(dt*60); this.y+=Math.sin(this.angle)*this.speed*(dt*60); this.life-=dt; if(this.life<=0||isSolid(getTile(this.x,this.y))) this.isDead=true; } }
class MortarProjectile extends Entity { constructor(sX,sY,tX,tY,source){ super(sX,sY,'MortarProjectile'); this.tX=tX; this.tY=tY; this.source=source; this.life=2; this.radius=15 } update(dt){ this.life-=dt; if(this.life<=0){ this.isDead=true; entities.push(new Shockwave(this.tX,this.tY,150,40,this.source)); } } }
class Laser extends Entity { constructor(x,y,p,l){ super(x,y,'Laser'); this.source=p.source; this.angle=p.angle; this.color=p.color; this.damage=p.damage; this.length=l; this.life=0.1;} update(dt){ this.life-=dt; if(this.life<=0) this.isDead = true; } }
class Grenade extends Projectile { constructor(x,y,p,rad) { super(x,y,p,0.8,8); this.type='Grenade'; this.speed=10; this.explosionRadius = rad; } update(dt) { super.update(dt); if(this.life <= 0) { this.isDead = true; entities.push(new Shockwave(this.x, this.y, this.explosionRadius, this.damage, this.source)); } } }
class Shockwave extends Entity { constructor(x,y,mR,d,source){ super(x,y,'Shockwave'); this.source=source; this.radius=0; this.maxRadius=mR; this.damage=d; this.life=0.5; this.hitTargets=[]; } update(dt){ this.radius += this.maxRadius * 3 * dt; this.life -= dt; if(this.life <= 0) this.isDead = true; } }
class NPC extends Entity { constructor(x, y, name, color = '#8a2be2') { super(x, y, 'NPC'); this.name = name; this.radius = 12; this.color = color; } }
class MedBay extends Entity { constructor(x, y) { super(x, y, 'MedBay'); this.name = 'Med-Bay'; this.radius = 12; this.color = '#ffffff'; } }
class AdminPanel extends Entity { constructor(x, y) { super(x, y, 'AdminPanel'); this.name = 'Admin'; this.radius = 12; this.color = '#1a1a1a'; } }
class Portal extends Entity { constructor(x, y) { super(x, y, 'Portal'); this.name = 'Portal'; this.radius = 25; } }
class LootDrop extends Entity { constructor(x,y,v){ super(x + Math.random()*20-10, y + Math.random()*20-10, 'LootDrop'); this.value=v*5; this.radius=5; this.color='#ffff00'; this.life=60; } update(dt){ this.life-=dt; if (this.life <= 0) this.isDead=true; } }
class EquipmentDrop extends Entity { constructor(x, y, item) { super(x + Math.random()*20-10, y+Math.random()*20-10, 'EquipmentDrop'); this.item = item; this.radius = 8; this.color = TIER_COLORS[item.tier] || '#fff'; this.life = 60; this.pickupDelay = 0.5; } update(dt) { this.life -= dt; if (this.pickupDelay > 0) this.pickupDelay -= dt; if (this.life <= 0) this.isDead = true; } }
class PlayerLootBag extends Entity { constructor(x, y, items, bits, color) { super(x, y, 'PlayerLootBag'); this.item = { color: color }; this.items = items; this.bits = bits; this.life = 180; this.pickupDelay = 3; } update(dt) { this.life -= dt; if (this.pickupDelay > 0) this.pickupDelay -= dt; if (this.life <= 0 || (this.bits <= 0 && this.items.every(i => i === null))) this.isDead = true; } }
class FloatingText extends Entity { constructor(x, y, text, color = '#ff8888') { super(x, y, 'floatingText'); this.text = text; this.color = color; this.life = 1; } update(dt) { this.y -= 20 * dt; this.life -= dt; if (this.life <= 0) this.isDead = true; } }
class Tombstone extends Entity {
    constructor(x, y, playerName, causeOfDeath, playerColor, lootBagId = null) {
        super(x, y, 'Tombstone');
        this.playerName = playerName;
        this.causeOfDeath = causeOfDeath;
        this.playerColor = playerColor;
        this.lootBagId = lootBagId;
        this.life = 180;
    }
    update(dt) {
        this.life -= dt;
        if (this.life <= 0) {
            this.isDead = true;
        }
    }
}


// --- INITIALIZE WORLD ---
function initializeWorld() {
    entities = []; 
    entities.push(new NPC(2.5 * TILE_SIZE, 2.5 * TILE_SIZE, 'Exchange', '#8a2be2'));
    entities.push(new NPC(13.5 * TILE_SIZE, 2.5 * TILE_SIZE, 'Bank', '#e3d400'));
    entities.push(new MedBay(2.5 * TILE_SIZE, 10.5 * TILE_SIZE));
    entities.push(new AdminPanel(13.5 * TILE_SIZE, 10.5 * TILE_SIZE));
    entities.push(new Portal(CITY_SPAWN_POINT.x, CITY_SPAWN_POINT.y - (TILE_SIZE * 2)));

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

    const playerIds = Object.keys(players);
    if (playerIds.length > 0) {
        for (let i = entities.length - 1; i >= 0; i--) {
            const entity = entities[i];
            if ((entity instanceof Enemy && !entity.isBoss && !entity.isBossComponent)) { 
                let isNearPlayer = false;
                for (const pid of playerIds) {
                    const player = players[pid];
                    if (player.isDead) continue;
                    if (Math.hypot(entity.x - player.x, entity.y - player.y) < DESPAWN_RADIUS) {
                        isNearPlayer = true;
                        break;
                    }
                }

                if (isNearPlayer) {
                    entity.timeOutsidePlayerRange = 0;
                } else {
                    entity.timeOutsidePlayerRange += dt;
                    if (entity.timeOutsidePlayerRange > DESPAWN_TIME) {
                        entity.isDead = true;
                    }
                }
            }
        }
    }

    // Handle Collisions
    for (let i = entities.length - 1; i >= 0; i--) {
        const entity = entities[i];
        if (!entity || entity.isDead) continue;

        if (entity.type === 'Projectile' || entity.type === 'Grenade') {
            const ownerIsPlayer = players[entity.source.id] !== undefined;
            for(const pid in players) {
                const p = players[pid];
                if (ownerIsPlayer && pid === entity.source.id) continue;
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
                        other.takeDamage(entity.damage, entity);
                        if (entity.type === 'Grenade') {
                             entities.push(new Shockwave(entity.x, entity.y, entity.explosionRadius, entity.damage, entity.source));
                        }
                        entity.isDead = true;
                        break;
                    }
                }
                 if (entity.isDead) continue;
            }
        }
        else if (entity.type === 'MeleeSlash') {
            const owner = players[entity.source.id];
            if (!owner) continue;
             for(const other of entities) {
                if (other instanceof Enemy && !entity.hitTargets.includes(other.id)) {
                    const dist = Math.hypot(other.x - owner.x, other.y - owner.y);
                    if (dist < other.radius + entity.radius) {
                        const angleToTarget = Math.atan2(other.y - owner.y, other.x - owner.x);
                        let angleDiff = Math.abs(entity.angle - angleToTarget);
                        if (angleDiff > Math.PI) angleDiff = 2 * Math.PI - angleDiff;
                        if (angleDiff < entity.arc / 2) {
                            other.takeDamage(entity.damage, entity);
                            entity.hitTargets.push(other.id);
                            if (other instanceof Enemy && !other.isBoss) {
                                const knockbackStrength = 15;
                                const knockbackAngle = entity.angle;
                                const knockbackX = other.x + Math.cos(knockbackAngle) * knockbackStrength;
                                const knockbackY = other.y + Math.sin(knockbackAngle) * knockbackStrength;
                                if (!isSolid(getTile(knockbackX, other.y))) other.x = knockbackX;
                                if (!isSolid(getTile(other.x, knockbackY))) other.y = knockbackY;
                            }
                        }
                    }
                }
             }
        }
        else if (entity.type === 'Laser') {
             const ownerIsPlayer = players[entity.source.id] !== undefined;
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
                                other.takeDamage(entity.damage * dt * 20, entity);
                            }
                        }
                    }
                }
             }
        }
        else if(entity.type === 'Shockwave'){
             const ownerIsPlayer = players[entity.source.id] !== undefined;
             for(const pid in players) {
                const p = players[pid];
                if (!p.isDead && !entity.hitTargets.includes(pid) && Math.hypot(entity.x - p.x, entity.y - p.y) < entity.radius) {
                    if(isCity(p.x, p.y) && ownerIsPlayer) continue;
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

    for (const entity of entities) { 
        if (entity.type === 'LootDrop') { 
            for (const pid in players) { 
                const player = players[pid]; 
                if (!player.isDead && Math.hypot(entity.x - player.x, entity.y - player.y) < player.radius + 30) { 
                    player.dataBits += entity.value; 
                    entity.isDead = true; 
                    break; 
                } 
            } 
        } 
    }

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
                     if (distFromCenter > 500 && Math.random() < 0.2) {
                        enemyType = GravityWell;
                     } else if (distFromCenter > 400 && Math.random() < 0.6) {
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
    
    const entitiesData = entities.map(e => e.getData());

    const stateToSend = JSON.stringify({ type: 'update', players: playersData, entities: entitiesData });
    wss.clients.forEach(client => { if (client.readyState === WebSocket.OPEN) client.send(stateToSend); });
}
setInterval(gameLoop, 1000 / TICK_RATE);

function countFreeInventorySlots(player) {
    return player.inventory.filter(slot => slot === null).length;
}

// --- TRADE LOGIC (UPDATED) ---
function startTrade(player1Id, player2Id) {
    const p1 = players[player1Id];
    const p2 = players[player2Id];
    if (!p1 || !p2 || p1.trade.partnerId || p2.trade.partnerId) return;

    p1.trade.partnerId = player2Id;
    p2.trade.partnerId = player1Id;
    
    const p1Socket = getSocketByPlayerId(player1Id);
    const p2Socket = getSocketByPlayerId(player2Id);
    if(p1Socket) p1Socket.send(JSON.stringify({ type: 'tradeStarted', partner: p2.getData() }));
    if(p2Socket) p2Socket.send(JSON.stringify({ type: 'tradeStarted', partner: p1.getData() }));
}

function cancelTrade(cancellerId, reason) {
    const player = players[cancellerId];
    if (!player || !player.trade.partnerId) return;

    const partnerId = player.trade.partnerId;
    const partner = players[partnerId];
    
    const resetTradeState = (p) => {
        if (!p) return;
        p.trade = { partnerId: null, offerItems: [], offerBits: 0, acceptedStage1: false, acceptedStage2: false };
        const socket = getSocketByPlayerId(p.id);
        if(socket) socket.send(JSON.stringify({ type: 'tradeCancelled', reason: reason }));
    };

    resetTradeState(player);
    resetTradeState(partner);
}

function finalizeTrade(p1Id, p2Id) {
    const p1 = players[p1Id];
    const p2 = players[p2Id];

    if (!p1 || !p2 || p1.dataBits < p1.trade.offerBits || p2.dataBits < p2.trade.offerBits) {
        cancelTrade(p1Id, "An error occurred during trade.");
        return;
    }

    const p1FreeSlots = countFreeInventorySlots(p1);
    const p2FreeSlots = countFreeInventorySlots(p2);

    if (p1FreeSlots < p2.trade.offerItems.length || p2FreeSlots < p1.trade.offerItems.length) {
        cancelTrade(p1Id, "Not enough inventory space to complete the trade.");
        return;
    }
    
    p1.dataBits = p1.dataBits - p1.trade.offerBits + p2.trade.offerBits;
    p2.dataBits = p2.dataBits - p2.trade.offerBits + p1.trade.offerBits;

    const p1ItemsToGive = [...p1.trade.offerItems];
    const p2ItemsToGive = [...p2.trade.offerItems];

    p1ItemsToGive.forEach(itemToGive => {
        const index = p1.inventory.findIndex(invItem => invItem && invItem.id === itemToGive.id);
        if (index !== -1) p1.inventory[index] = null;
    });
    p2ItemsToGive.forEach(itemToGive => {
        const index = p2.inventory.findIndex(invItem => invItem && invItem.id === itemToGive.id);
        if (index !== -1) p2.inventory[index] = null;
    });

    p1ItemsToGive.forEach(item => p2.addToInventory(item));
    p2ItemsToGive.forEach(item => p1.addToInventory(item));

    [p1, p2].forEach(p => {
        p.trade = { partnerId: null, offerItems: [], offerBits: 0, acceptedStage1: false, acceptedStage2: false };
        const socket = getSocketByPlayerId(p.id);
        if (socket) socket.send(JSON.stringify({ type: 'tradeCompleted' }));
    });
}


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
            // UPDATED: New bank logic for "Deposit-All" and "Deposit-X"
            if (player && data.type === 'bankAction') {
                const playerBank = banks[player.username] || [];
                if (data.action === 'deposit') {
                    const itemToDeposit = player.inventory[data.itemIndex];
                    if (itemToDeposit) {
                        let amountToDeposit = 0;
                        if (data.amount === 'all') {
                            amountToDeposit = player.inventory.filter(i => i && i.id === itemToDeposit.id).length;
                        } else {
                            amountToDeposit = Math.min(
                                player.inventory.filter(i => i && i.id === itemToDeposit.id).length,
                                data.amount || 1
                            );
                        }
                        
                        if (amountToDeposit > 0) {
                            const existingStack = playerBank.find(stack => stack.item.id === itemToDeposit.id);
                            if (existingStack) {
                                existingStack.quantity += amountToDeposit;
                            } else {
                                playerBank.push({ item: { ...itemToDeposit }, quantity: amountToDeposit });
                            }
                            
                            // Remove items from inventory
                            let removedCount = 0;
                            for (let i = player.inventory.length - 1; i >= 0; i--) {
                                if (removedCount >= amountToDeposit) break;
                                if (player.inventory[i] && player.inventory[i].id === itemToDeposit.id) {
                                    player.inventory[i] = null;
                                    removedCount++;
                                }
                            }
                        }
                    }
                } else if (data.action === 'withdraw') {
                    const bankStack = playerBank[data.itemIndex];
                    if (bankStack) {
                        const amountToWithdraw = data.amount === 'all' ? bankStack.quantity : Math.min(bankStack.quantity, data.amount || 1);
                        if (amountToWithdraw > 0) {
                            if (countFreeInventorySlots(player) >= amountToWithdraw) {
                                for(let i = 0; i < amountToWithdraw; i++) {
                                    player.addToInventory(bankStack.item);
                                }
                                bankStack.quantity -= amountToWithdraw;
                                if (bankStack.quantity <= 0) {
                                    playerBank.splice(data.itemIndex, 1);
                                }
                            }
                        }
                    }
                }
                banks[player.username] = playerBank;
                saveData('banks.json', banks);
                ws.send(JSON.stringify({ type: 'openBank', bank: playerBank }));
            }

            if (player && data.type === 'marketAction') { /* ... existing market code ... */ }
            
            if (player && data.type === 'tradeRequest') {
                const targetPlayer = players[data.targetId];
                if (targetPlayer && !targetPlayer.trade.partnerId) {
                    const targetSocket = getSocketByPlayerId(data.targetId);
                    if (targetSocket) {
                        targetSocket.send(JSON.stringify({ type: 'tradeRequest', from: player.getData() }));
                    }
                }
            }
            if (player && data.type === 'tradeResponse') {
                const requester = players[data.requesterId];
                if (requester && data.accepted) {
                    startTrade(player.id, requester.id);
                }
            }
            if (player && player.trade.partnerId && data.type === 'tradeUpdate') {
                const partner = players[player.trade.partnerId];
                if (!partner) return;
                player.trade.offerItems = data.offerItems;
                player.trade.offerBits = Math.max(0, parseInt(data.offerBits, 10)) || 0;
                player.trade.acceptedStage1 = false;
                partner.trade.acceptedStage1 = false;
                
                const partnerSocket = getSocketByPlayerId(partner.id);
                if (partnerSocket) {
                    partnerSocket.send(JSON.stringify({ type: 'tradeUpdate', offer: { offer: player.trade.offerItems, offerBits: player.trade.offerBits } }));
                    partnerSocket.send(JSON.stringify({ type: 'tradeStatusChange', myAccepted: partner.trade.acceptedStage1, partnerAccepted: player.trade.acceptedStage1 }));
                }
                ws.send(JSON.stringify({ type: 'tradeStatusChange', myAccepted: player.trade.acceptedStage1, partnerAccepted: partner.trade.acceptedStage1 }));
            }
            if (player && player.trade.partnerId && data.type === 'tradeAcceptStage1') {
                const partner = players[player.trade.partnerId];
                if (!partner) return;
                player.trade.acceptedStage1 = true;

                if (partner.trade.acceptedStage1) {
                    const myOfferSummary = { items: player.trade.offerItems, bits: player.trade.offerBits };
                    const partnerOfferSummary = { items: partner.trade.offerItems, bits: partner.trade.offerBits };
                    ws.send(JSON.stringify({ type: 'tradeShowConfirmation', myOffer: myOfferSummary, partnerOffer: partnerOfferSummary }));
                    const partnerSocket = getSocketByPlayerId(partner.id);
                    if(partnerSocket) partnerSocket.send(JSON.stringify({ type: 'tradeShowConfirmation', myOffer: partnerOfferSummary, partnerOffer: myOfferSummary }));
                } else {
                    const partnerSocket = getSocketByPlayerId(partner.id);
                    if(partnerSocket) partnerSocket.send(JSON.stringify({ type: 'tradeStatusChange', myAccepted: partner.trade.acceptedStage1, partnerAccepted: player.trade.acceptedStage1 }));
                    ws.send(JSON.stringify({ type: 'tradeStatusChange', myAccepted: player.trade.acceptedStage1, partnerAccepted: partner.trade.acceptedStage1 }));
                }
            }
            if (player && player.trade.partnerId && data.type === 'tradeAcceptStage2') {
                const partner = players[player.trade.partnerId];
                if (!partner) return;
                player.trade.acceptedStage2 = true;
                if (partner.trade.acceptedStage2) {
                    finalizeTrade(player.id, partner.id);
                }
            }
            if (player && player.trade.partnerId && data.type === 'tradeCancel') {
                cancelTrade(player.id, `${player.username} cancelled the trade.`);
            }

            if (!player || player.isDead) return;
            if (data.type === 'input') { player.inputs = data.inputs; player.angle = data.angle; }
            if (data.type === 'chat') { broadcastMessage({ type: 'chat', sender: player.username, message: data.message, color: player.color }); }
            if (data.type === 'equipItem') { const item = player.inventory[data.itemIndex]; if (item) { const currentEquipped = player.equipment[item.slot]; player.equipment[item.slot] = item; player.inventory[data.itemIndex] = currentEquipped; player.recalculateStats(); } }
            if (data.type === 'unequipItem') { const item = player.equipment[data.slot]; if (item && player.addToInventory(item)) { player.equipment[data.slot] = null; player.recalculateStats(); } }
            if (data.type === 'dropItem') { let itemToDrop = null; if (data.source === 'inventory') { itemToDrop = player.inventory[data.index]; player.inventory[data.index] = null; } else { itemToDrop = player.equipment[data.index]; player.equipment[data.index] = null; } if (itemToDrop) entities.push(new EquipmentDrop(player.x, player.y, itemToDrop)); player.recalculateStats(); }
            if (data.type === 'buyNpcItem') { const shop = shopInventories[data.shopName]; const shopItem = shop ? shop[data.itemIndex] : null; if(shopItem && player.dataBits >= shopItem.cost) { if(player.addToInventory(shopItem.item)) { player.dataBits -= shopItem.cost; } } }
            if (data.type === 'sellItem') { const item = player.inventory[data.itemIndex]; if(item) { player.dataBits += Math.floor(getItemBaseValue(item) / 3); player.inventory[data.index] = null; } }
        
        } catch (error) { console.error(`[SERVER] Error processing message from ${ws.playerId}:`, error); }
    });

    ws.on('close', () => {
        const player = players[ws.playerId];
        if (player) {
            if (player.trade.partnerId) {
                cancelTrade(player.id, `${player.username} has disconnected.`);
            }
            console.log(`[SERVER] Player ${player.username} (${ws.playerId}) disconnected.`);
            delete players[ws.playerId];
        }
    });
});

server.listen(PORT, () => {
    console.log(`Server started and listening on port ${PORT}`);
});