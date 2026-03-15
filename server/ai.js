'use strict';
/**
 * ai.js — AI player logic for Age of Realms
 *
 * Three difficulty levels:
 *   easy     — slow economy, few units, rarely attacks
 *   moderate — balanced economy + military, attacks every ~5 min
 *   hard     — aggressive economy AND military, attacks early and often
 *
 * Called from gameTick() in index.js once per server tick per AI team.
 * Receives a context object {uid, UDEFS, BCOSTS, BHPS, BSIZES, MAP, HALF, URES, VRES}
 * so it has no hard imports from the server file.
 */

const WATER_LEVEL = -1.3;

function _dist2D(ax,az,bx,bz){ return Math.sqrt((ax-bx)**2+(az-bz)**2); }

function _getH(wx,wz,h,URES,VRES,MAP,HALF){
  const cx=Math.max(-HALF,Math.min(HALF-0.001,wx));
  const cz=Math.max(-HALF,Math.min(HALF-0.001,wz));
  const gx=(cx+HALF)/MAP*URES, gz=(cz+HALF)/MAP*VRES;
  const c0=Math.floor(gx),c1=Math.min(c0+1,URES);
  const r0=Math.floor(gz),r1=Math.min(r0+1,VRES);
  const fx=gx-c0,fz=gz-r0;
  return h[r0*(URES+1)+c0]*(1-fx)*(1-fz)+h[r0*(URES+1)+c1]*fx*(1-fz)
        +h[r1*(URES+1)+c0]*(1-fx)*fz+h[r1*(URES+1)+c1]*fx*fz;
}

function _isW(wx,wz,h,URES,VRES,MAP,HALF){
  return _getH(wx,wz,h,URES,VRES,MAP,HALF)<WATER_LEVEL;
}

// ─── Technology cost table (mirrors TECHS in index.js) ───────────────────────
const TECH_COSTS = {
  'Iron Tools':   {food:100,gold:50},
  'Town Watch':   {food:75},
  'Loom':         {gold:50},
  'Masonry':      {stone:100},
  'Feudal Age':   {food:500},
  'Fletching':    {food:100,wood:50},
  'Scale Armor':  {food:100,gold:50},
  'Horse Collar': {food:75,wood:75},
  'Castle Age':   {food:800,gold:200},
  'Chemistry':    {food:300,gold:200},
  'Plate Armor':  {gold:300},
};
const TECH_AGE = {
  'Iron Tools':0,'Town Watch':0,'Loom':0,'Masonry':0,'Feudal Age':0,
  'Fletching':1,'Scale Armor':1,'Horse Collar':1,'Castle Age':1,
  'Chemistry':2,'Plate Armor':2,
};

// ─── Per-difficulty configuration ────────────────────────────────────────────
const DIFF_CFG = {
  easy: {
    maxVillagers:    4,
    maxArmy:         3,
    attackInterval:  600,   // 10 min before first serious attack
    attackThreshold: 4,     // needs 4 soldiers to attack
    buildInterval:   45,    // seconds between build attempts
    trainInterval:   20,
    researchEnabled: false,
    ageUpEnabled:    false,
    buildQueue:      ['House','Farm','House','Farm','House'],
    trainTypes:      ['Swordsman'],
    gatherRadius:    30,
    unitPreference:  'random',
  },
  moderate: {
    maxVillagers:    8,
    maxArmy:         12,
    attackInterval:  300,   // 5 min
    attackThreshold: 6,
    buildInterval:   22,
    trainInterval:   10,
    researchEnabled: true,
    ageUpEnabled:    true,
    buildQueue:      ['House','Farm','Lumbercamp','Farm','House','MiningCamp',
                      'House','Barracks','House','Tower','House','Farm'],
    trainTypes:      ['Swordsman','Archer','Scout'],
    gatherRadius:    40,
    unitPreference:  'random',
    researchList:    ['Iron Tools','Loom','Feudal Age','Horse Collar','Scale Armor'],
  },
  hard: {
    maxVillagers:    90,
    maxArmy:         70,
    attackInterval:  180,   // 3 min — attacks early and often
    attackWaveSizes: [5,15,20,30,55], // cycles through these wave sizes
    attackThreshold: 5,     // minimum to trigger (first wave)
    buildInterval:   12,
    trainInterval:   6,
    researchEnabled: true,
    ageUpEnabled:    true,
    buildQueue:      ['House','Farm','Lumbercamp','Farm','House','MiningCamp','Farm',
                      'House','Barracks','House','Tower','House','Barracks',
                      'House','Farm','House','Castle'],
    trainTypes:      ['Swordsman','Archer','Knight','Scout'],
    gatherRadius:    100,
    unitPreference:  'strongest',  // picks best affordable unit
    researchList:    ['Iron Tools','Loom','Masonry','Feudal Age','Fletching',
                      'Scale Armor','Horse Collar','Castle Age','Chemistry','Plate Armor'],
  },
};

// ─────────────────────────────────────────────────────────────────────────────
//  Main entry point
// ─────────────────────────────────────────────────────────────────────────────
function tickAI(lobby, dt, teamNum, difficulty, ctx) {
  const {uid, UDEFS, BCOSTS, BHPS, BSIZES, MAP, HALF, URES, VRES} = ctx;
  const cfg = DIFF_CFG[difficulty] || DIFF_CFG.moderate;
  const {gs} = lobby;
  const {units, buildings, teams, resNodes, heights} = gs;
  const td = teams[teamNum];
  const enemyTeam = teamNum === 1 ? 2 : 1;

  // ── Initialise per-team AI state on first tick ──────────────────────────
  if(!lobby.aiState) lobby.aiState = {};
  if(!lobby.aiState[teamNum]) {
    lobby.aiState[teamNum] = {
      buildTimer:      cfg.buildInterval * 0.3 * Math.random(), // stagger start
      attackTimer:     0,
      trainTimer:      0,
      researchTimer:   cfg.buildInterval * 2,
      buildIdx:        0,
      army:            [],
      isAttacking:     false,
    };
  }
  const ai = lobby.aiState[teamNum];

  // ── Convenience helpers ─────────────────────────────────────────────────
  function iW(x,z){ return _isW(x,z,heights,URES,VRES,MAP,HALF); }
  function afford(cost){
    return (!cost.food||td.food>=cost.food)
        && (!cost.wood||td.wood>=cost.wood)
        && (!cost.gold||td.gold>=cost.gold)
        && (!cost.stone||td.stone>=cost.stone);
  }
  function spend(cost){
    if(cost.food) td.food-=cost.food;
    if(cost.wood) td.wood-=cost.wood;
    if(cost.gold) td.gold-=cost.gold;
    if(cost.stone) td.stone-=cost.stone;
  }
  function mkBld(type,x,z){
    const key=type.replace(' ','');
    return {
      id:uid(), type, x, z, team:teamNum,
      ownerId:'ai_team_'+teamNum,
      hp:BHPS[key]||400, maxHp:BHPS[key]||400,
      size:BSIZES[key]||1.5,
      productionQueue:[], productionTimer:0,
      dead:false, atkTimer:0,
      underConstruction:false, buildProgress:0, buildTime:0,
    };
  }

  // ── Get own Town Center (AI base anchor) ────────────────────────────────
  const aiTC = Object.values(buildings).find(
    b => b.team===teamNum && b.type==='Town Center' && !b.dead
  );
  if(!aiTC) return; // base destroyed — AI is done

  const bx=aiTC.x, bz=aiTC.z;

  // ══════════════════════════════════════════════════════════════════════════
  //  1. ECONOMY — Villager gathering
  // ══════════════════════════════════════════════════════════════════════════
  const myVills = Object.values(units).filter(
    u => !u.dead && u.team===teamNum && u.type==='Villager'
  );

  for(const v of myVills){
    // Leave builders alone; only redirect idle villagers
    if(v.state==='moving_to_build'||v.state==='building') continue;
    if(v.state!=='idle') continue;

    // Find the closest non-depleted resource node within gather radius
    let best=null, bd=cfg.gatherRadius;
    const nodeList=ctx.resMap?[...ctx.resMap.values()]:resNodes;
    for(const rn of nodeList){
      if(rn.depleted||rn.amount<=0) continue;
      const d=_dist2D(v.x,v.z,rn.x,rn.z);
      if(d<bd){ bd=d; best=rn; }
    }
    if(best){
      v.gatherTarget=best.id;
      v.state='moving_to_gather';
      v.tx=best.x+(Math.random()-0.5)*1.5;
      v.tz=best.z+(Math.random()-0.5)*1.5;
    }
  }

  // ══════════════════════════════════════════════════════════════════════════
  //  2. ECONOMY — Train more villagers
  // ══════════════════════════════════════════════════════════════════════════
  const villCount = myVills.length;
  if(villCount < cfg.maxVillagers && td.population < td.maxPop-1){
    const vcost = UDEFS.Villager.cost;
    if(afford(vcost) && !aiTC.productionQueue.length){
      spend(vcost);
      aiTC.productionQueue.push('Villager');
    }
  }

  // ══════════════════════════════════════════════════════════════════════════
  //  3. ECONOMY — Construct buildings
  // ══════════════════════════════════════════════════════════════════════════
  ai.buildTimer += dt;
  if(ai.buildTimer >= cfg.buildInterval && ai.buildIdx < cfg.buildQueue.length){
    const bType = cfg.buildQueue[ai.buildIdx];
    const cost  = BCOSTS[bType] || {};

    // Age-gated buildings
    if(bType==='Castle' && td.age<2){ /* skip until Castle Age */ }
    else if(bType==='Barracks' && td.age<0){ /* always allowed */ }
    else if(afford(cost)){
      const sz = BSIZES[bType.replace(' ','')] || 1.5;
      let placed = false;

      for(let attempt=0; attempt<25&&!placed; attempt++){
        const a = Math.random()*Math.PI*2;
        const r = 6 + Math.random()*16;
        const px = bx+Math.cos(a)*r, pz = bz+Math.sin(a)*r;
        if(Math.abs(px)>=HALF-4||Math.abs(pz)>=HALF-4||iW(px,pz)) continue;

        // Don't overlap existing buildings
        const blocked = Object.values(buildings).some(
          b => !b.dead && _dist2D(px,pz,b.x,b.z) < sz+(b.size||1.5)+0.8
        );
        if(blocked) continue;

        spend(cost);
        const b = mkBld(bType, px, pz);
        buildings[b.id] = b;
        if(bType==='House') td.maxPop += 5;
        gs.events.push({msg:`Enemy built ${bType}!`, type:'warn'});
        ai.buildIdx++;
        ai.buildTimer = 0;
        placed = true;
      }
      // If placement failed, retry sooner rather than waiting a full interval
      if(!placed) ai.buildTimer = cfg.buildInterval * 0.6;
    }
  }

  // ══════════════════════════════════════════════════════════════════════════
  //  4. MILITARY — Train soldiers
  // ══════════════════════════════════════════════════════════════════════════
  ai.trainTimer += dt;
  if(ai.trainTimer >= cfg.trainInterval){
    ai.trainTimer = 0;

    // Prune dead from army list
    ai.army = ai.army.filter(id => units[id] && !units[id].dead);

    if(ai.army.length < cfg.maxArmy){
      const bars = Object.values(buildings).filter(
        b => b.team===teamNum && b.type==='Barracks' && !b.dead && !b.underConstruction
      );
      for(const bar of bars){
        if(bar.productionQueue.length > 0) continue;

        // Pick the best affordable unit type
        const candidates = cfg.trainTypes.filter(t => {
          const d = UDEFS[t];
          if(!d) return false;
          // Knight and Catapult require Feudal Age (age>=1) or Castle Age (age>=2)
          if(t==='Knight'&&td.age<1) return false;
          if(t==='Catapult'&&td.age<2) return false;
          return afford(d.cost) && td.population+(d.pop||1) <= td.maxPop;
        });
        if(!candidates.length) continue;

        let pick;
        if(cfg.unitPreference === 'strongest'){
          // Hard: prefer Knight > Archer > Swordsman > Scout
          const priority = ['Knight','Catapult','Archer','Swordsman','Scout'];
          pick = priority.find(t => candidates.includes(t)) || candidates[0];
        } else {
          pick = candidates[Math.floor(Math.random()*candidates.length)];
        }

        const d = UDEFS[pick];
        spend(d.cost);
        bar.productionQueue.push(pick);
        // Population increment handled by gameTick production loop when unit spawns
        break; // one training order per interval
      }
    }
  }

  // Absorb any freshly trained non-villager units into the army list
  for(const u of Object.values(units)){
    if(!u.dead && u.team===teamNum && u.type!=='Villager' && !ai.army.includes(u.id)){
      ai.army.push(u.id);
    }
  }

  // ══════════════════════════════════════════════════════════════════════════
  //  5. RESEARCH (moderate & hard only)
  // ══════════════════════════════════════════════════════════════════════════
  if(cfg.researchEnabled){
    ai.researchTimer += dt;
    if(ai.researchTimer >= cfg.buildInterval * 2.5){
      ai.researchTimer = 0;
      for(const techId of cfg.researchList){
        if(td.researched.includes(techId)) continue;
        if(td.age < (TECH_AGE[techId]||0)) continue;
        const cost = TECH_COSTS[techId]||{};
        if(!afford(cost)) continue;

        spend(cost);
        td.researched.push(techId);

        // Age advancement
        if(techId==='Feudal Age'){
          td.age=1;
          gs.events.push({msg:'Enemy advances to Feudal Age!', type:'warn'});
        }
        if(techId==='Castle Age'){
          td.age=2;
          gs.events.push({msg:'Enemy advances to Castle Age!', type:'warn'});
        }

        // Apply tech effects to existing units/buildings
        if(techId==='Loom')
          for(const u of Object.values(units))
            if(u.team===teamNum&&u.type==='Villager'){u.maxHp+=40;u.hp=Math.min(u.hp+40,u.maxHp);}
        if(techId==='Masonry')
          for(const b of Object.values(buildings))
            if(b.team===teamNum) b.maxHp=Math.floor(b.maxHp*1.2);
        if(techId==='Scale Armor')
          for(const u of Object.values(units))
            if(u.team===teamNum) u.def+=2;
        if(techId==='Plate Armor')
          for(const u of Object.values(units))
            if(u.team===teamNum) u.def+=4;

        gs.events.push({msg:`Enemy researched ${techId}!`, type:'warn'});
        break; // one research per interval
      }
    }
  }

  // ══════════════════════════════════════════════════════════════════════════
  //  6. COMBAT — Attack or patrol
  // ══════════════════════════════════════════════════════════════════════════
  ai.attackTimer += dt;
  const readyArmy = ai.army.filter(id => units[id] && !units[id].dead);

  // Find primary attack target — enemy TC first, else any enemy building
  const enemyTC = Object.values(buildings).find(
    b => b.team===enemyTeam && b.type==='Town Center' && !b.dead
  );
  const anyEnemyBld = !enemyTC && Object.values(buildings).find(
    b => b.team===enemyTeam && !b.dead
  );
  const target = enemyTC || anyEnemyBld;
  const tx = target ? target.x : 0;
  const tz = target ? target.z : 0;

  // For hard AI, determine the current wave size target from the cycling list
  let currentThreshold = cfg.attackThreshold;
  if(cfg.attackWaveSizes){
    if(!ai.waveIndex) ai.waveIndex=0;
    currentThreshold = cfg.attackWaveSizes[ai.waveIndex % cfg.attackWaveSizes.length];
  }

  const shouldAttack =
    readyArmy.length >= currentThreshold &&
    ai.attackTimer >= cfg.attackInterval &&
    gs.gameTime >= cfg.attackInterval * 0.4;

  if(shouldAttack){
    ai.isAttacking = true;
    ai.attackTimer = 0;
    // Advance to next wave size for next attack
    if(cfg.attackWaveSizes) ai.waveIndex = ((ai.waveIndex||0)+1) % cfg.attackWaveSizes.length;
    // Only send up to currentThreshold units in this wave — hold the rest back
    const wave = readyArmy.slice(0, currentThreshold);
    gs.events.push({
      msg:`⚔ Enemy assault! ${wave.length} warriors marching!`,
      type:'bad'
    });
    for(const id of wave){
      const u = units[id]; if(!u) continue;
      let ax = tx+(Math.random()-0.5)*10, az = tz+(Math.random()-0.5)*10;
      if(iW(ax,az)){ ax=tx; az=tz; }
      u.tx=ax; u.tz=az; u.state='moving_to_attack';
    }
  }

  // Patrol near own base when not attacking
  if(!ai.isAttacking){
    for(const id of readyArmy){
      const u = units[id];
      if(!u || u.state!=='idle') continue;
      let rx = bx+(Math.random()-0.5)*14, rz = bz+(Math.random()-0.5)*14;
      if(iW(rx,rz)){ rx=bx; rz=bz; }
      u.tx=rx; u.tz=rz; u.state='moving';
    }
  }

  // Reset attacking flag once the army is wiped out
  if(readyArmy.length>0 && readyArmy.every(id => !units[id]||units[id].dead)){
    ai.isAttacking = false;
  }
}

module.exports = {tickAI};
