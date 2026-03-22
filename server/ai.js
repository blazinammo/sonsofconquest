'use strict';
/**
 * ai.js — AI player logic for Age of Realms
 * easy / moderate / hard difficulties
 *
 * Improvements in this version:
 *  - Villager lock-in: villagers stay on a resource for a minimum duration
 *    before being eligible for reassignment, preventing thrashing
 *  - Lumbercamp passive income: included in build queues early
 *  - Market trading: AI sells surplus resources for gold when needed
 *  - Farm staffing: pulls low-priority gatherers to staff empty farms
 *  - Unit roles in waves: archers hang 6u back, catapults 12u back
 *  - Unit retreat: units below 20% HP fall back to Town Center
 *  - Flanking: waves approach from a randomly varied angle each time
 *  - Wave column spread: lateral offsets so units don't pile on one point
 *  - Blacksmith queue: up to 3 units pre-positioned; arming fires the
 *    instant the 60s server cooldown clears
 *  - Blacksmith skip: won't re-send already fully-armored units
 *  - Continuous scouting: scout keeps roaming after finding enemy base,
 *    orbiting the enemy perimeter to reveal towers and expansions
 *  - Tower awareness: if enemy has 3+ towers, shift production to Catapults
 *  - Post-wipe timer: attackTimer pauses until army is partly rebuilt
 *  - Early rush harassment: 2-3 unit raid at ~50s to disrupt economy
 *  - Age-up gated on army size for rush AI
 *  - Pathfinding step size reduced to 2 cells for cleaner water routing
 *  - Moderate AI: occasional resource-node harassment
 *  - Adaptive turtle mode: tower spam when TC drops below 50% HP
 */

const WATER_LEVEL = -1.3;
function _dist2D(ax,az,bx,bz){ return Math.sqrt((ax-bx)**2+(az-bz)**2); }
function _getH(wx,wz,h,URES,VRES,MAP,HALF){
  const cx=Math.max(-HALF,Math.min(HALF-0.001,wx)), cz=Math.max(-HALF,Math.min(HALF-0.001,wz));
  const gx=(cx+HALF)/MAP*URES, gz=(cz+HALF)/MAP*VRES;
  const c0=Math.floor(gx),c1=Math.min(c0+1,URES), r0=Math.floor(gz),r1=Math.min(r0+1,VRES);
  const fx=gx-c0,fz=gz-r0;
  return h[r0*(URES+1)+c0]*(1-fx)*(1-fz)+h[r0*(URES+1)+c1]*fx*(1-fz)
        +h[r1*(URES+1)+c0]*(1-fx)*fz+h[r1*(URES+1)+c1]*fx*fz;
}
function _isW(wx,wz,h,URES,VRES,MAP,HALF){
  return _getH(wx,wz,h,URES,VRES,MAP,HALF)<WATER_LEVEL;
}

// ─────────────────────────────────────────────────────────────────────────────
//  PATHFINDING — A* on the terrain height grid
//
//  Finds the shortest land path (in world-space distance) from (sx,sz) to
//  (tx,tz), routing around water.  Returns an array of {x,z} waypoints.
//
//  Grid resolution: STEP=3 cells ≈ 5 world units on a 150-map, 10 on 300.
//  A* uses true Euclidean distance as both heuristic and edge cost, so it
//  finds the geometrically shortest path, not just fewest hops.
//
//  After the raw path is found, a line-of-sight string-pull removes
//  unnecessary intermediate waypoints so units walk straight wherever safe.
// ─────────────────────────────────────────────────────────────────────────────
function _findWaterPath(sx,sz,tx,tz,h,URES,VRES,MAP,HALF){
  function toCell(wx,wz){
    return [Math.max(0,Math.min(URES,Math.round((wx+HALF)/MAP*URES))),
            Math.max(0,Math.min(VRES,Math.round((wz+HALF)/MAP*VRES)))];
  }
  function toWorld(c,r){ return [-HALF+c/URES*MAP, -HALF+r/VRES*MAP]; }
  // Use the SAME water threshold as moveU/isWSafe (-1.1) so A* only routes
  // through cells the movement code will actually allow. The lenient _isW
  // threshold (-1.3) caused scouts to be sent through shallow cells that
  // moveU then refused to enter, stalling the unit on the shore.
  const SAFE_WATER=-1.1;
  function cellWet(c,r){
    const[wx,wz]=toWorld(c,r);
    const cxc=Math.max(-HALF,Math.min(HALF-0.001,wx)),czc=Math.max(-HALF,Math.min(HALF-0.001,wz));
    const gx=(cxc+HALF)/MAP*URES,gz=(czc+HALF)/MAP*VRES;
    const c0=Math.floor(gx),c1=Math.min(c0+1,URES),r0=Math.floor(gz),r1=Math.min(r0+1,VRES);
    const fx=gx-c0,fz=gz-r0;
    const ht=h[r0*(URES+1)+c0]*(1-fx)*(1-fz)+h[r0*(URES+1)+c1]*fx*(1-fz)
            +h[r1*(URES+1)+c0]*(1-fx)*fz+h[r1*(URES+1)+c1]*fx*fz;
    return ht<SAFE_WATER;
  }
  // Line-of-sight check between two world points at grid resolution
  function losClean(ax,az,bx,bz){
    const[ac,ar]=toCell(ax,az);
    const[bc,br]=toCell(bx,bz);
    const steps=Math.max(Math.abs(bc-ac),Math.abs(br-ar),1);
    for(let i=0;i<=steps;i++){
      const ic=Math.round(ac+(bc-ac)*i/steps);
      const ir=Math.round(ar+(br-ar)*i/steps);
      if(cellWet(ic,ir)) return false;
    }
    return true;
  }

  // If a clean straight line exists, return direct
  if(losClean(sx,sz,tx,tz)) return [{x:tx,z:tz}];

  const[sc,sr]=toCell(sx,sz);
  const[ec,er]=toCell(tx,tz);

  // A* — step size 2 cells (was 3) for finer routing through narrow passages.
  // STEP=3 ≈ 10 world units on a 300-map; a strait narrower than that was
  // jumped over entirely. STEP=2 ≈ 6.7 world units catches narrower land bridges.
  const STEP=2;
  const cellW=MAP/URES*STEP; // world units per step
  const key=(c,r)=>c*10000+r;

  const gScore=new Map();
  const fScore=new Map();
  const parent=new Map();
  const open=[];  // min-heap would be ideal; array with sorted insert for simplicity
  const closed=new Set();

  const sk=key(sc,sr);
  gScore.set(sk,0);
  const h0=Math.sqrt((ec-sc)**2+(er-sr)**2)*cellW;
  fScore.set(sk,h0);
  open.push([h0,sc,sr]);
  parent.set(sk,null);

  let found=null;
  const MAX_ITER=12000; // raised from 6000 — STEP=2 explores ~2× more nodes than STEP=3
  let iter=0;

  while(open.length&&!found&&iter<MAX_ITER){
    iter++;
    // Pop lowest fScore
    open.sort((a,b)=>a[0]-b[0]);
    const[,c,r]=open.shift();
    const ck=key(c,r);
    if(closed.has(ck)) continue;
    closed.add(ck);

    if(Math.abs(c-ec)<=STEP*2&&Math.abs(r-er)<=STEP*2){found=[c,r];break;}

    const dirs=[
      [STEP,0,cellW],[- STEP,0,cellW],[0,STEP,cellW],[0,-STEP,cellW],
      [STEP,STEP,cellW*1.414],[-STEP,STEP,cellW*1.414],[STEP,-STEP,cellW*1.414],[-STEP,-STEP,cellW*1.414]
    ];
    for(const[dc,dr,cost] of dirs){
      const nc=c+dc,nr=r+dr;
      if(nc<0||nc>URES||nr<0||nr>VRES) continue;
      const nk=key(nc,nr);
      if(closed.has(nk)||cellWet(nc,nr)) continue;
      const ng=(gScore.get(ck)||0)+cost;
      if(ng<(gScore.get(nk)??Infinity)){
        gScore.set(nk,ng);
        const hh=Math.sqrt((ec-nc)**2+(er-nr)**2)*cellW;
        fScore.set(nk,ng+hh);
        parent.set(nk,[c,r]);
        open.push([ng+hh,nc,nr]);
      }
    }
  }

  if(!found) return [{x:tx,z:tz}]; // no path found — fallback direct

  // Reconstruct raw cell path
  const cellPath=[];
  let cur=found;
  while(cur){cellPath.unshift(cur);cur=parent.get(key(cur[0],cur[1]));}

  // Convert to world coords
  const raw=cellPath.map(([c,r])=>{const[wx,wz]=toWorld(c,r);return{x:wx,z:wz};});
  raw.push({x:tx,z:tz});

  // String-pull: greedily skip waypoints whenever line-of-sight is clear
  // This removes unnecessary zigzags and makes units walk straight stretches
  const pulled=[raw[0]];
  let i=0;
  while(i<raw.length-1){
    // Find the furthest point we can reach in a straight line from pulled tail
    let j=raw.length-1;
    while(j>i+1&&!losClean(pulled[pulled.length-1].x,pulled[pulled.length-1].z,raw[j].x,raw[j].z)) j--;
    pulled.push(raw[j]);
    i=j;
  }

  // Remove the start point (unit is already there) and return
  return pulled.slice(1);
}

// ─────────────────────────────────────────────────────────────────────────────
//  PATH ASSIGNMENT — compute and attach an A* path to a unit destination.
//  Called whenever we send a unit somewhere, so pathing is proactive.
//  Sets u.tx/u.tz to the first waypoint and stores the rest on u._waypoints.
// ─────────────────────────────────────────────────────────────────────────────
function _assignPath(u,destX,destZ,h,URES,VRES,MAP,HALF,spread=0){
  // Apply optional spread to final destination
  let ax=destX,az=destZ;
  if(spread>0){
    ax=destX+(Math.random()-0.5)*spread*2;
    az=destZ+(Math.random()-0.5)*spread*2;
  }
  const wps=_findWaterPath(u.x,u.z,ax,az,h,URES,VRES,MAP,HALF);
  u._waypoints=wps.length>1?wps.slice(0,-1):[];  // all but final dest
  u._pathDest={x:ax,z:az};
  u._pathLastPos={x:u.x,z:u.z};
  u._pathStuckTimer=0;
  // Set immediate target to first waypoint (or final dest if only one)
  const first=wps.length>0?wps[0]:{x:ax,z:az};
  u.tx=first.x; u.tz=first.z;
  return{finalX:ax,finalZ:az};
}

// Count enemy defensive structures near a point
function _towerThreat(px,pz,radius,buildings,enemyTeam){
  let n=0;
  for(const bid in buildings){
    const b=buildings[bid];
    if(!b.dead&&b.team===enemyTeam&&(b.type==='Tower'||b.type==='Castle')&&_dist2D(px,pz,b.x,b.z)<radius) n++;
  }
  return n;
}

// ─────────────────────────────────────────────────────────────────────────────
const TECH_COSTS={
  'Iron Tools':{food:100,gold:50},'Town Watch':{food:75},'Loom':{gold:50},
  'Masonry':{stone:100},'Feudal Age':{food:500},'Fletching':{food:100,wood:50},
  'Scale Armor':{food:100,gold:50},'Horse Collar':{food:75,wood:75},
  'Castle Age':{food:800,gold:200},'Chemistry':{food:300,gold:200},'Plate Armor':{gold:300},
};
const TECH_AGE={
  'Iron Tools':0,'Town Watch':0,'Loom':0,'Masonry':0,'Feudal Age':0,
  'Fletching':1,'Scale Armor':1,'Horse Collar':1,'Castle Age':1,
  'Chemistry':2,'Plate Armor':2,
};

// ─────────────────────────────────────────────────────────────────────────────
//  DIFFICULTY CONFIG
// ─────────────────────────────────────────────────────────────────────────────
const DIFF_CFG={
  easy:{
    maxVillagers:4,maxArmy:3,
    attackInterval:600,attackThreshold:4,
    buildInterval:45,trainInterval:20,
    researchEnabled:false,ageUpEnabled:false,
    buildQueue:['House','Farm','House','Farm','House'],
    trainTypes:['Swordsman'],gatherRadius:30,unitPreference:'random',
    detectionRange:8,useBlacksmith:false,useMarket:false,villagerLockIn:0,
  },
  moderate:{
    maxVillagers:8,maxArmy:12,
    attackInterval:300,attackThreshold:6,
    buildInterval:22,trainInterval:10,
    researchEnabled:true,ageUpEnabled:true,
    buildQueue:['House','Farm','Lumbercamp','Farm','House','MiningCamp',
                'House','Barracks','House','Tower','House','Farm'],
    trainTypes:['Swordsman','Archer','Scout'],gatherRadius:40,unitPreference:'random',
    researchList:['Iron Tools','Loom','Feudal Age','Horse Collar','Scale Armor'],
    detectionRange:12,useBlacksmith:false,useMarket:false,villagerLockIn:15,
  },
  hard:{
    maxVillagers:16,maxArmy:40,
    attackInterval:150,attackWaveSizes:[6,12,20,30,40],attackThreshold:6,
    buildInterval:10,trainInterval:5,
    researchEnabled:true,ageUpEnabled:true,
    buildQueue:[],  // filled at init based on strategy
    trainTypes:['Swordsman','Archer','Knight','Scout','Catapult'],
    gatherRadius:60,unitPreference:'strongest',
    researchList:['Iron Tools','Loom','Masonry','Feudal Age','Fletching',
                  'Scale Armor','Horse Collar','Castle Age','Chemistry','Plate Armor'],
    detectionRange:20,useBlacksmith:true,useMarket:true,
    smithInterval:12,villagerLockIn:20,
  },
};

const HARD_BUILD_QUEUE_RUSH=[
  'House','Farm','Lumbercamp','Barracks','House','Farm',
  'MiningCamp','Barracks','House','Tower','House','Barracks',
  'Blacksmith','House','Farm','Tower','House','Barracks',
];
const HARD_BUILD_QUEUE_BOOM=[
  'House','Farm','Farm','Lumbercamp','House','Farm','MiningCamp',
  'House','Farm','Farm','Blacksmith','Barracks','House','Farm',
  'Tower','House','Barracks','Farm','House','Barracks',
  'Tower','Castle','House','Barracks',
];

const COMBAT_TYPES=new Set(['Swordsman','Archer','Knight','Catapult','Scout']);
const MELEE_TYPES =new Set(['Swordsman','Knight']);

// ─────────────────────────────────────────────────────────────────────────────
//  MAIN AI TICK
// ─────────────────────────────────────────────────────────────────────────────
function tickAI(lobby,dt,teamNum,difficulty,ctx){
  const{uid,UDEFS,BCOSTS,BHPS,BSIZES,BBUILD_TIME,MAP,HALF,URES,VRES}=ctx;
  const cfg=DIFF_CFG[difficulty]||DIFF_CFG.moderate;
  const{gs}=lobby;
  const{units,buildings,teams,resNodes,heights}=gs;
  const td=teams[teamNum];
  const aiOwner='ai_team_'+teamNum;
  // Defeated teams — provided by server via ctx; never target them
  const defeated=ctx.defeated||new Set();

  // All team numbers that are not ours and not already defeated
  const allEnemyTeams=Object.keys(teams).map(Number).filter(t=>t!==teamNum&&!defeated.has(t));

  // Own spawn position
  const ownSpawn=ctx.spawnPositions?ctx.spawnPositions[teamNum-1]:{x:ctx.pox||0,z:ctx.poz||0};

  // ── First-time initialisation ──────────────────────────────────────────────
  if(!lobby.aiState) lobby.aiState={};
  if(!lobby.aiState[teamNum]){

    // ── Roll a unique personality for this AI instance ──────────────────────
    // Each dimension is independently randomised so no two AIs feel the same.
    const R=()=>Math.random();

    // Strategy: boom (economy first), rush (early aggression), turtle (defend+boom)
    let strategy='rush';
    if(difficulty==='hard'){
      const roll=R();
      strategy=roll<0.35?'boom':roll<0.65?'rush':'turtle';
    }

    // Aggression level: scales attack timing and wave sizes
    const aggressionScale=difficulty==='hard'?0.7+R()*0.9:1.0; // 0.7–1.6×

    // Unit flavour: which combat unit this AI over-produces (25% bias toward it)
    const unitFlavours=['Swordsman','Archer','Knight','balanced'];
    const unitFlavour=difficulty==='hard'?unitFlavours[Math.floor(R()*unitFlavours.length)]:'balanced';

    // Economy flavour: what resources this AI prioritises gathering
    const ecoFlavours=[
      ['food','gold','wood','stone'],   // standard
      ['gold','food','wood','stone'],   // gold rush
      ['food','wood','gold','stone'],   // fast builder
      ['food','gold','stone','wood'],   // stone turtle
    ];
    const ecoFlavour=difficulty==='hard'?ecoFlavours[Math.floor(R()*ecoFlavours.length)]:ecoFlavours[0];

    // Research flavour: shuffle tech order slightly
    const baseResearch=['Iron Tools','Loom','Masonry','Feudal Age','Fletching',
                        'Scale Armor','Horse Collar','Castle Age','Chemistry','Plate Armor'];
    // Swap a couple of techs in the list to create variety
    const researchList=[...baseResearch];
    if(difficulty==='hard'&&R()<0.5){
      // Randomly swap two mid-list entries
      const i=1+Math.floor(R()*4), j=i+1+Math.floor(R()*3);
      if(j<researchList.length)[researchList[i],researchList[j]]=[researchList[j],researchList[i]];
    }

    // Build queue: start from the template, then shuffle the middle section
    // (keep the first 4 items stable so the base always gets established)
    function shuffledQueue(base){
      const q=[...base];
      const LOCK=4; // first N items are fixed
      for(let i=q.length-1;i>LOCK;i--){
        const j=LOCK+Math.floor(R()*(i-LOCK+1));
        [q[i],q[j]]=[q[j],q[i]];
      }
      return q;
    }

    // Numeric variation ranges
    const maxVill = difficulty==='hard'
      ? Math.round((strategy==='boom'?28:strategy==='turtle'?30:20) + R()*8)
      : undefined;
    const maxArmy = difficulty==='hard' ? Math.round(30+R()*20) : undefined;
    // Tighter attack intervals — boom was 160s, now 80–130s; rush 60–100s; turtle 140–200s
    const atkInterval = difficulty==='hard'
      ? Math.round((strategy==='rush'?60:strategy==='turtle'?160:90)*aggressionScale)
      : undefined;
    const firstWaveSize = difficulty==='hard' ? 5+Math.floor(R()*4) : undefined;

    // Early harassment: rush sends raiders at 40–70s, boom/turtle at 80–120s
    const harassTime = strategy==='rush' ? 40+Math.floor(R()*30) : 80+Math.floor(R()*40);

    lobby.aiState[teamNum]={
      buildTimer:cfg.buildInterval*(0.1+R()*0.5),
      attackTimer:0,trainTimer:0,researchTimer:cfg.buildInterval*(1+R()),
      buildIdx:0,army:[],isAttacking:false,
      strategy,
      aggressionScale,
      unitFlavour,
      ecoFlavour,
      researchList,
      shuffledBuildQueue:null,  // set below
      maxVill,maxArmy,atkInterval,firstWaveSize,
      harassTime,
      smithTimer:0,smithQueue:[],
      marketTimer:0,
      harassSent:false,
      postWipeTimer:0,
      turtleMode:false,
      harassTimer:0,
      knownBases:{},
      currentTargetTeam:null,
      targetRerollTimer:0,
      // Resistance tracking — updated each tick during an attack
      resistanceState:'none',   // 'none' | 'active' | 'cleared'
      towerDmgAccum:0,          // cumulative tower/castle damage taken this engagement
      prevArmyHp:{},            // id->hp snapshot to detect damage taken
    };

    // Now set the per-instance config overrides — mutate a local copy, NOT the
    // shared cfg object (that would bleed across all AIs of the same difficulty)
    if(difficulty==='hard'){
      const bq=strategy==='boom'?[...HARD_BUILD_QUEUE_BOOM]
              :strategy==='turtle'?[...HARD_BUILD_QUEUE_BOOM]  // turtle uses boom queue but attacks late
              :[...HARD_BUILD_QUEUE_RUSH];
      lobby.aiState[teamNum].shuffledBuildQueue=shuffledQueue(bq);
      cfg.buildQueue=lobby.aiState[teamNum].shuffledBuildQueue;
      cfg.maxVillagers=maxVill;
      cfg.maxArmy=maxArmy;
      cfg.attackInterval=atkInterval;
      cfg.attackWaveSizes=[
        firstWaveSize,
        firstWaveSize+Math.round(6+R()*4),
        firstWaveSize+Math.round(14+R()*6),
        firstWaveSize+Math.round(22+R()*8),
      ];
      cfg.researchList=researchList;
    }
  }
  const ai=lobby.aiState[teamNum];
  const strategy=ai.strategy||'rush';

  // Restore per-instance config each tick (cfg is shared; re-apply overrides)
  if(difficulty==='hard'&&ai.shuffledBuildQueue){
    cfg.buildQueue=ai.shuffledBuildQueue;
    cfg.maxVillagers=ai.maxVill;
    cfg.maxArmy=ai.maxArmy;
    cfg.attackInterval=ai.atkInterval;
    cfg.researchList=ai.researchList;
  }

  // ── Helpers ────────────────────────────────────────────────────────────────
  function iW(x,z){ return _isW(x,z,heights,URES,VRES,MAP,HALF); }
  function afford(cost){
    return(!cost.food||td.food>=cost.food)&&(!cost.wood||td.wood>=cost.wood)
          &&(!cost.gold||td.gold>=cost.gold)&&(!cost.stone||td.stone>=cost.stone);
  }
  function spend(cost){
    if(cost.food)td.food-=cost.food; if(cost.wood)td.wood-=cost.wood;
    if(cost.gold)td.gold-=cost.gold; if(cost.stone)td.stone-=cost.stone;
  }
  function mkBld(type,x,z){
    const key=type.replace(' ','');
    const buildTime=(BBUILD_TIME&&BBUILD_TIME[key])||20;
    const b={id:uid(),type,x,z,team:teamNum,ownerId:aiOwner,
      hp:1,maxHp:BHPS[key]||400,size:BSIZES[key]||1.5,
      productionQueue:[],productionTimer:0,dead:false,atkTimer:0,
      underConstruction:true,buildProgress:0,buildTime,
      rallyX:null,rallyZ:null,rallyResourceId:null};
    return b;
  }
  // Send the nearest idle AI villager to construct a building site.
  // If no idle villager is available, the building will sit until one frees up.
  function dispatchBuilder(buildingId,bldX,bldZ){
    const vills=Object.values(units).filter(u=>
      !u.dead&&u.team===teamNum&&u.type==='Villager'&&u.ownerId===aiOwner
      &&u.state==='idle'&&!u._farmId);
    if(!vills.length) return;
    let best=vills[0],bestD=Infinity;
    for(const v of vills){
      const d=_dist2D(v.x,v.z,bldX,bldZ);
      if(d<bestD){bestD=d;best=v;}
    }
    best.state='moving_to_build';
    best.buildTarget=buildingId;
    best.tx=bldX+(Math.random()-0.5)*1.5;
    best.tz=bldZ+(Math.random()-0.5)*1.5;
  }
  function safePt(cx,cz,spread=16){
    // Pre-collect enemy tower/castle positions so patrol points avoid their fire arcs
    const dangerZones=[];
    for(const bid in buildings){
      const b=buildings[bid];
      if(!b.dead&&b.team!==teamNum&&(b.type==='Tower'||b.type==='Castle')){
        dangerZones.push({x:b.x,z:b.z,r:b.type==='Castle'?13:10});
      }
    }
    for(let i=0;i<40;i++){
      const a=Math.random()*Math.PI*2,r=4+Math.random()*spread;
      const px=Math.max(-HALF+3,Math.min(HALF-3,cx+Math.cos(a)*r));
      const pz=Math.max(-HALF+3,Math.min(HALF-3,cz+Math.sin(a)*r));
      if(iW(px,pz)) continue;
      if(dangerZones.some(dz=>_dist2D(px,pz,dz.x,dz.z)<dz.r)) continue;
      return{x:px,z:pz};
    }
    return null;
  }
  function getResNode(id){ return ctx.resMap?ctx.resMap.get(id):resNodes.find(r=>r.id===id); }

  const aiTC=Object.values(buildings).find(b=>b.team===teamNum&&b.type==='Town Center'&&!b.dead);
  if(!aiTC) return;
  const bx=aiTC.x,bz=aiTC.z;

  // ── Adaptive: turtle mode when TC is critically damaged ───────────────────
  ai.turtleMode=(aiTC.hp/aiTC.maxHp)<0.5;

  // ══════════════════════════════════════════════════════════════════════════
  //  MULTI-ENEMY TARGET SELECTION
  //  Keep a known-bases map for every enemy team.  Pick which enemy to focus
  //  attacks on — 70% nearest, 30% random — and re-evaluate when:
  //   • A wave finishes (army goes idle after attacking)
  //   • The current target's TC is destroyed
  //   • targetRerollTimer hits 0
  // ══════════════════════════════════════════════════════════════════════════

  // Refresh known bases: any visible enemy building updates that team's entry
  for(const id in units){
    const u=units[id];
    if(u.dead||u.team!==teamNum||u.ownerId!==aiOwner) continue;
    const vr=u.vision||12;
    for(const bid in buildings){
      const b=buildings[bid];
      if(b.dead||b.team===teamNum) continue;
      if(_dist2D(u.x,u.z,b.x,b.z)<vr){
        // Update or initialise entry for this enemy team
        if(!ai.knownBases[b.team]||b.type==='Town Center'){
          ai.knownBases[b.team]={x:b.x,z:b.z};
        }
      }
    }
  }

  // Prune bases whose TC is confirmed dead / team eliminated / team defeated
  for(const tn of Object.keys(ai.knownBases).map(Number)){
    const stillAlive=!defeated.has(tn)&&Object.values(buildings).some(b=>!b.dead&&b.team===tn&&b.type==='Town Center');
    if(!stillAlive) delete ai.knownBases[tn];
  }

  // Seed unknown enemy bases from spawn positions so the AI has a fallback
  // even before scouting (mirrors old behaviour for 2-player games)
  if(ctx.spawnPositions){
    for(const tn of allEnemyTeams){
      if(!ai.knownBases[tn]){
        // Only seed if that team is actually still alive (has a TC)
        const alive=Object.values(buildings).some(b=>!b.dead&&b.team===tn&&b.type==='Town Center');
        if(alive&&ctx.spawnPositions[tn-1]){
          // We don't mark this as "confirmed" yet — scouts will confirm it
          // For now, leave knownBases empty until vision reveals something.
          // (Keeps the pre-existing scouting behaviour intact.)
        }
      }
    }
  }

  // Decide which enemy team to focus on this tick
  ai.targetRerollTimer=Math.max(0,(ai.targetRerollTimer||0)-dt);

  function pickTargetTeam(){
    const known=Object.keys(ai.knownBases).map(Number).filter(tn=>allEnemyTeams.includes(tn));
    if(known.length===0) return null;
    // 30% chance: pick a random known enemy
    if(Math.random()<0.30) return known[Math.floor(Math.random()*known.length)];
    // 70%: pick the enemy whose base is closest to our TC
    let nearest=known[0],nearestDist=Infinity;
    for(const tn of known){
      const kb=ai.knownBases[tn];
      const d=_dist2D(bx,bz,kb.x,kb.z);
      if(d<nearestDist){nearestDist=d;nearest=tn;}
    }
    return nearest;
  }

  // Re-roll if: no current target, target eliminated, or timer expired
  const currentTargetAlive=ai.currentTargetTeam!==null
    &&ai.knownBases[ai.currentTargetTeam]!==undefined;
  if(!currentTargetAlive||ai.targetRerollTimer<=0){
    ai.currentTargetTeam=pickTargetTeam();
    // Reroll every 60s normally, 30s if we just lost a target
    ai.targetRerollTimer=currentTargetAlive?60:30;
  }

  // Convenience: the "primary enemy" concept for scouting/waves.
  // Only use a team if it actually has a known base — never fall back to a
  // team that isn't in knownBases, since that would leave enemyBase undefined.
  const enemyTeam=(ai.currentTargetTeam!=null&&ai.knownBases[ai.currentTargetTeam]!=null)
    ?ai.currentTargetTeam
    :null;
  const enemyBase=enemyTeam!=null?(ai.knownBases[enemyTeam]||null):null;
  // Legacy compat: knownEnemyX/Z mirrors the current target base
  if(enemyBase){ai.knownEnemyX=enemyBase.x;ai.knownEnemyZ=enemyBase.z;}
  else{ai.knownEnemyX=undefined;ai.knownEnemyZ=undefined;}

  // Fallback spawn direction for scouting (before any base is scouted)
  const enemySpawn=(()=>{
    // Use the spawn of the closest unmet enemy
    if(ctx.spawnPositions){
      let best=null,bestD=Infinity;
      for(const tn of allEnemyTeams){
        const sp=ctx.spawnPositions[tn-1];
        if(!sp) continue;
        const d=_dist2D(bx,bz,sp.x,sp.z);
        if(d<bestD){bestD=d;best=sp;}
      }
      if(best) return best;
    }
    return{x:ctx.aox||0,z:ctx.aoz||0};
  })();

  // ══════════════════════════════════════════════════════════════════════════
  //  0. RESISTANCE ASSESSMENT — track what our attacking units are facing
  //
  //  resistanceState:
  //   'none'    — no enemy military units near our attackers, no tower damage
  //   'active'  — enemy military units present OR tower damage being taken
  //   'cleared' — had active resistance, now enemy military all dead/gone;
  //               only villagers/buildings remain
  //
  //  Updated every tick based on the actual situation at the front.
  // ══════════════════════════════════════════════════════════════════════════
  const ENGAGE_RADIUS=22; // world units — how close our units must be to "be at the front"

  // Find the centroid of our attacking units to define "the front"
  const attackingUnits=ai.army
    .map(id=>units[id])
    .filter(u=>u&&!u.dead&&!u._retreating&&
      (u.state==='attacking'||u.state==='attacking_building'||u.state==='moving_to_attack'));

  let frontX=enemyBase?enemyBase.x:bx, frontZ=enemyBase?enemyBase.z:bz;
  if(attackingUnits.length>0){
    frontX=attackingUnits.reduce((s,u)=>s+u.x,0)/attackingUnits.length;
    frontZ=attackingUnits.reduce((s,u)=>s+u.z,0)/attackingUnits.length;
  }

  // Detect tower damage: compare current HP of attacking units to last tick's snapshot
  let newTowerDmg=0;
  for(const u of attackingUnits){
    const prev=ai.prevArmyHp[u.id];
    if(prev!==undefined&&u.hp<prev) newTowerDmg+=(prev-u.hp);
    ai.prevArmyHp[u.id]=u.hp;
  }
  // Decay old snapshots for dead/retreated units
  for(const id of Object.keys(ai.prevArmyHp)){
    if(!units[id]||units[id].dead) delete ai.prevArmyHp[id];
  }
  // Accumulate tower damage (decays slowly so brief pauses don't reset state)
  ai.towerDmgAccum=Math.max(0,(ai.towerDmgAccum||0)*0.97+newTowerDmg);

  // Count enemy military units near the front
  const enemyMilNearFront=Object.values(units).filter(u=>
    !u.dead&&u.team!==teamNum&&COMBAT_TYPES.has(u.type)&&
    _dist2D(u.x,u.z,frontX,frontZ)<ENGAGE_RADIUS
  ).length;

  // Count enemy towers/castles near the front
  const towersNearFront=Object.values(buildings).filter(b=>
    !b.dead&&b.team!==teamNum&&(b.type==='Tower'||b.type==='Castle')&&
    _dist2D(b.x,b.z,frontX,frontZ)<ENGAGE_RADIUS
  ).length;

  // Update resistance state
  const hasResistance=enemyMilNearFront>0||ai.towerDmgAccum>15||towersNearFront>0;
  if(ai.isAttacking||attackingUnits.length>0){
    if(hasResistance){
      ai.resistanceState='active';
    } else if(ai.resistanceState==='active'){
      // Was active, now cleared — enemy military defeated
      ai.resistanceState='cleared';
    } else if(ai.resistanceState==='none'){
      ai.resistanceState='none';
    }
  } else {
    // Reset when not attacking
    ai.resistanceState='none';
    ai.towerDmgAccum=0;
  }
  const rs=ai.resistanceState;

  // ── Priority target selector ──────────────────────────────────────────────
  // Returns the best target (unit id or building id) for a given attacker
  // based on current resistance state and what's visible near it.
  function priorityTarget(u){
    const scanR=cfg.detectionRange||16;
    const ex=frontX, ez=frontZ;

    if(rs==='none'){
      // No resistance — hit economic targets: villagers → houses → TC
      // Look for enemy villagers first
      let best=null,bestScore=-Infinity;
      for(const oid in units){
        const o=units[oid];
        if(o.dead||o.team===teamNum) continue;
        const d=_dist2D(u.x,u.z,o.x,o.z);
        if(d>scanR*1.5) continue;
        let score=0;
        if(o.type==='Villager') score=100-d*0.5;
        else score=10-d*0.5; // other units lower priority
        if(score>bestScore){bestScore=score;best={type:'unit',id:oid};}
      }
      // Buildings: houses first, then TC
      for(const bid in buildings){
        const b=buildings[bid];
        if(b.dead||b.team===teamNum) continue;
        const d=_dist2D(u.x,u.z,b.x,b.z);
        if(d>scanR*1.5) continue;
        let score=0;
        if(b.type==='Town Center')       score=60-d*0.3;
        else if(b.type==='House')        score=80-d*0.3;
        else                             score=20-d*0.3;
        if(score>bestScore){bestScore=score;best={type:'building',id:bid};}
      }
      return best;

    } else if(rs==='active'){
      // Resistance present — hit: enemy units → towers → barracks → houses → TC
      let best=null,bestScore=-Infinity;
      for(const oid in units){
        const o=units[oid];
        if(o.dead||o.team===teamNum) continue;
        const d=_dist2D(u.x,u.z,o.x,o.z);
        if(d>scanR) continue;
        let score=100-d*0.5; // all enemy units high priority
        if(score>bestScore){bestScore=score;best={type:'unit',id:oid};}
      }
      for(const bid in buildings){
        const b=buildings[bid];
        if(b.dead||b.team===teamNum) continue;
        const d=_dist2D(u.x,u.z,b.x,b.z);
        if(d>scanR*1.2) continue;
        let score=0;
        if(b.type==='Tower'||b.type==='Castle') score=90-d*0.4;
        else if(b.type==='Barracks')            score=70-d*0.4;
        else if(b.type==='House')               score=40-d*0.4;
        else if(b.type==='Town Center')         score=30-d*0.4;
        else                                    score=15-d*0.4;
        if(score>bestScore){bestScore=score;best={type:'building',id:bid};}
      }
      return best;

    } else { // 'cleared'
      // Military defeated — mop up: villagers → TC
      let best=null,bestScore=-Infinity;
      for(const oid in units){
        const o=units[oid];
        if(o.dead||o.team===teamNum) continue;
        const d=_dist2D(u.x,u.z,o.x,o.z);
        if(d>scanR*1.5) continue;
        let score=o.type==='Villager'?100-d*0.5:50-d*0.5;
        if(score>bestScore){bestScore=score;best={type:'unit',id:oid};}
      }
      for(const bid in buildings){
        const b=buildings[bid];
        if(b.dead||b.team===teamNum) continue;
        const d=_dist2D(u.x,u.z,b.x,b.z);
        if(d>scanR*1.5) continue;
        let score=b.type==='Town Center'?70-d*0.3:25-d*0.3;
        if(score>bestScore){bestScore=score;best={type:'building',id:bid};}
      }
      return best;
    }
  }

  // ══════════════════════════════════════════════════════════════════════════
  //  1. AUTO-ATTACK / DEFENSE — priority-based target selection
  // ══════════════════════════════════════════════════════════════════════════
  const detRange=cfg.detectionRange||12;
  for(const id in units){
    const u=units[id];
    if(u.dead||u.team!==teamNum||u.ownerId!==aiOwner||!COMBAT_TYPES.has(u.type)) continue;
    if(u.state==='attacking'||u.state==='attacking_building') continue;
    if(u._headingToSmith&&u.state==='moving') continue;

    // Units actively marching on an attack wave use priority targeting
    const atFront=attackingUnits.includes(u)||
      (enemyBase&&_dist2D(u.x,u.z,enemyBase.x,enemyBase.z)<ENGAGE_RADIUS*1.5);

    if(atFront){
      const pt=priorityTarget(u);
      if(pt){
        if(pt.type==='unit'&&units[pt.id]&&!units[pt.id].dead){
          u.target=pt.id;u.state='attacking';u._waypoints=null;continue;
        } else if(pt.type==='building'&&buildings[pt.id]&&!buildings[pt.id].dead){
          u.target=pt.id;u.state='attacking_building';u._waypoints=null;continue;
        }
      }
    }

    // Fallback: standard nearest-enemy detection for units not at the front
    const closeRange=u.state==='moving_to_attack'?4:detRange;
    let nearEnemy=null,nearDist=closeRange;
    for(const oid in units){
      const o=units[oid];
      if(!o.dead&&o.team!==teamNum){const d=_dist2D(u.x,u.z,o.x,o.z);if(d<nearDist){nearDist=d;nearEnemy=o;}}
    }
    if(nearEnemy){u.target=nearEnemy.id;u.state='attacking';u._waypoints=null;continue;}
    // Only scan for buildings to attack when truly idle — don't yank a patrolling
    // unit (state='moving') into an enemy tower's fire arc mid-patrol.
    // moving_to_attack units are handled by the atFront priority block above.
    if(u.state==='idle'){
      let nearBld=null,nearBldDist=detRange*0.7;
      for(const bid in buildings){
        const b=buildings[bid];
        if(!b.dead&&b.team!==teamNum&&!defeated.has(b.team)){const d=_dist2D(u.x,u.z,b.x,b.z);if(d<nearBldDist){nearBldDist=d;nearBld=b;}}
      }
      if(nearBld){u.target=nearBld.id;u.state='attacking_building';u._waypoints=null;continue;}

      // ── TC fail-safe: unit is inside an enemy base but found nothing to attack.
      // Target the enemy TC directly so units never idle in a conquered base.
      if(enemyBase&&_dist2D(u.x,u.z,enemyBase.x,enemyBase.z)<ENGAGE_RADIUS*1.5){
        const enemyTCId=Object.entries(gs.tcIds||{}).find(([tn])=>Number(tn)===enemyTeam)?.[1];
        const enemyTC=enemyTCId?buildings[enemyTCId]:null;
        if(enemyTC&&!enemyTC.dead){
          u.target=enemyTCId;u.state='attacking_building';u._waypoints=null;
        }
      }
    }
  }

  // ══════════════════════════════════════════════════════════════════════════
  //  1b. UNIT RETREAT — fall back to TC when below 20% HP
  // ══════════════════════════════════════════════════════════════════════════
  for(const id in units){
    const u=units[id];
    if(u.dead||u.team!==teamNum||u.ownerId!==aiOwner||!COMBAT_TYPES.has(u.type)) continue;
    if(u._retreating) continue;
    if((u.hp/(u.maxHp||1))<0.20&&u.state!=='idle'){
      u.target=null; u.state='moving';
      u._retreating=true;
      _assignPath(u,bx,bz,heights,URES,VRES,MAP,HALF,4);
    }
    if(u._retreating&&u.state==='idle') u._retreating=false;
  }

  // ══════════════════════════════════════════════════════════════════════════
  //  2. WAYPOINT FOLLOWING — advance units through their A* path
  //  For all moving AI units: pop waypoints as they're reached, redirect tx/tz
  //  to the next waypoint.  If a unit hasn't moved in 3s, recompute the path
  //  from current position (handles edge cases like separation pushes).
  // ══════════════════════════════════════════════════════════════════════════
  for(const id in units){
    const u=units[id];
    if(u.dead||u.team!==teamNum||u.ownerId!==aiOwner) continue;
    if(u.state!=='moving_to_attack'&&u.state!=='moving') continue;
    if(!isFinite(u.tx)||!isFinite(u.tz)) continue;

    // Advance through waypoints as each is reached
    if(u._waypoints&&u._waypoints.length>0){
      while(u._waypoints.length>0&&_dist2D(u.x,u.z,u._waypoints[0].x,u._waypoints[0].z)<2.0)
        u._waypoints.shift();
      if(u._waypoints.length>0){
        u.tx=u._waypoints[0].x; u.tz=u._waypoints[0].z;
      } else if(u._pathDest){
        u.tx=u._pathDest.x; u.tz=u._pathDest.z;
      }
    }

    // Stuck detection — recompute path if unit hasn't progressed in 1s.
    // _stuckCount gives up after 3 failed recomputes.
    if(!u._pathLastPos){u._pathLastPos={x:u.x,z:u.z};u._pathStuckTimer=0;}
    const moved=_dist2D(u.x,u.z,u._pathLastPos.x,u._pathLastPos.z);
    if(moved>0.8){u._pathLastPos={x:u.x,z:u.z};u._pathStuckTimer=0;u._stuckCount=0;}
    else u._pathStuckTimer=(u._pathStuckTimer||0)+dt;

    if(u._pathStuckTimer>=1.0&&u._pathDest){
      u._pathStuckTimer=0;u._pathLastPos={x:u.x,z:u.z};
      u._stuckCount=(u._stuckCount||0)+1;
      if(u._stuckCount>=3){
        u.state='idle';u._waypoints=null;u._pathDest=null;u._stuckCount=0;
      } else {
        // Recompute path from current position to original destination
        const wps=_findWaterPath(u.x,u.z,u._pathDest.x,u._pathDest.z,heights,URES,VRES,MAP,HALF);
        u._waypoints=wps.length>1?wps.slice(0,-1):[];
        u.tx=wps.length>0?wps[0].x:u._pathDest.x;
        u.tz=wps.length>0?wps[0].z:u._pathDest.z;
      }
    }
  }

  // ══════════════════════════════════════════════════════════════════════════
  //  3. ECONOMY — Villager gathering with lock-in to prevent thrashing
  // ══════════════════════════════════════════════════════════════════════════
  const myVills=Object.values(units).filter(u=>!u.dead&&u.team===teamNum&&u.type==='Villager'&&u.ownerId===aiOwner);
  const lockIn=cfg.villagerLockIn||0;

  // Strategy-aware resource priority — use this AI's personal eco flavour
  let resPriority;
  if(difficulty==='hard'){
    resPriority=ai.ecoFlavour||['food','gold','wood','stone'];
    // Dynamic overrides still apply on top of flavour
    if(td.gold<200&&td.food>400) resPriority=['gold','food','wood','stone'];
    if(td.stone<150&&td.age>=1)  resPriority=['stone','gold','food','wood'];
  } else {
    resPriority=['gold','food','wood','stone'];
  }

  const gatherCount={food:0,wood:0,gold:0,stone:0};
  for(const v of myVills){
    if(v.state==='moving_to_gather'||v.state==='gathering'||v.state==='returning'){
      const rn=getResNode(v.gatherTarget);
      if(rn) gatherCount[rn.type]=(gatherCount[rn.type]||0)+1;
    }
  }
  // Tick down lock-in timers
  for(const v of myVills) if(v._gatherLockTimer>0) v._gatherLockTimer=Math.max(0,v._gatherLockTimer-dt);

  for(const v of myVills){
    if(v.state==='moving_to_build'||v.state==='building') continue;
    if(v.state!=='idle') continue;
    if(v._farmId) continue;  // permanently dedicated to a farm — never reassign
    if(lockIn>0&&(v._gatherLockTimer||0)>0) continue;
    const nodeList=ctx.resMap?[...ctx.resMap.values()]:resNodes;
    let best=null,bestScore=-Infinity;
    for(const rn of nodeList){
      if(rn.depleted||rn.amount<=0||rn.isFarm) continue;
      const d=_dist2D(v.x,v.z,rn.x,rn.z);
      if(d>cfg.gatherRadius) continue;
      const typeBonus=(resPriority.indexOf(rn.type)>=0?(4-resPriority.indexOf(rn.type))*3:0);
      const staffPenalty=(gatherCount[rn.type]||0)*4;
      const distPen=difficulty==='hard'?d*0.08:d*0.1;
      const score=typeBonus-staffPenalty-distPen;
      if(score>bestScore){bestScore=score;best=rn;}
    }
    if(best){
      v.gatherTarget=best.id;v.state='moving_to_gather';
      v.tx=best.x+(Math.random()-0.5)*1.5;v.tz=best.z+(Math.random()-0.5)*1.5;
      v._gatherLockTimer=lockIn;
      gatherCount[best.type]=(gatherCount[best.type]||0)+1;
    }
  }

  // ══════════════════════════════════════════════════════════════════════════
  //  3b. FARM STAFFING
  //  Handled authoritatively in gameTick (index.js) using farm._lockedVillagerId.
  //  The AI only needs to avoid reassigning farm-locked villagers in section 3,
  //  which is done via the v._farmId guard above.
  // ══════════════════════════════════════════════════════════════════════════
  // (no AI-side logic needed here)

  // ══════════════════════════════════════════════════════════════════════════
  //  4. ECONOMY — Train villagers
  //  Count farms to ensure we always have enough free workers on top of
  //  the villagers permanently sacrificed to farms.
  // ══════════════════════════════════════════════════════════════════════════
  const myFarmCount=Object.values(buildings).filter(b=>b.team===teamNum&&b.type==='Farm'&&!b.dead&&!b.underConstruction&&b.farmNodeId).length;
  const effectiveVillagerCap=cfg.maxVillagers+myFarmCount; // one extra slot per farm
  if(myVills.length<effectiveVillagerCap&&td.population<td.maxPop-1){
    const vcost=UDEFS.Villager.cost;
    if(afford(vcost)&&!aiTC.productionQueue.length){spend(vcost);aiTC.productionQueue.push('Villager');}
  }

  // ══════════════════════════════════════════════════════════════════════════
  //  5. ECONOMY — Construct buildings
  // ══════════════════════════════════════════════════════════════════════════
  // Emergency house
  if(td.population>=td.maxPop-2&&afford(BCOSTS.House||{wood:30})){
    const alreadyBuilding=Object.values(buildings).some(b=>b.team===teamNum&&b.type==='House'&&b.underConstruction);
    if(!alreadyBuilding){
      const pt=safePt(bx,bz,14);
      if(pt){
        spend(BCOSTS.House||{wood:30});
        const b=mkBld('House',pt.x,pt.z);
        buildings[b.id]=b;
        dispatchBuilder(b.id,pt.x,pt.z);
      }
    }
  }

  // Turtle mode: spam towers near TC
  if(ai.turtleMode&&difficulty!=='easy'){
    const tcost=BCOSTS.Tower||{stone:125};
    const tCount=Object.values(buildings).filter(b=>b.team===teamNum&&b.type==='Tower'&&!b.dead).length;
    if(tCount<8&&afford(tcost)){
      for(let attempt=0;attempt<30;attempt++){
        const a=Math.random()*Math.PI*2,r=8+Math.random()*14;
        const px=bx+Math.cos(a)*r,pz=bz+Math.sin(a)*r;
        if(Math.abs(px)>=HALF-4||Math.abs(pz)>=HALF-4||iW(px,pz)) continue;
        if(Object.values(buildings).some(b=>!b.dead&&_dist2D(px,pz,b.x,b.z)<(BSIZES.Tower||1.2)+2.5)) continue;
        spend(tcost);
        const tb=mkBld('Tower',px,pz);
        buildings[tb.id]=tb;
        dispatchBuilder(tb.id,px,pz);
        gs.events.push({msg:'Enemy fortifying defenses!',type:'warn'});break;
      }
    }
  }

  ai.buildTimer+=dt;
  if(ai.buildTimer>=cfg.buildInterval&&ai.buildIdx<cfg.buildQueue.length){
    const bType=cfg.buildQueue[ai.buildIdx];
    const cost=BCOSTS[bType]||{};
    const ageGated=(bType==='Castle'&&td.age<2)||(bType==='Market'&&td.age<1)||(bType==='MiningCamp'&&td.age<3);
    if(ageGated){ai.buildIdx++;ai.buildTimer=0;}
    else if(afford(cost)){
      const sz=BSIZES[bType.replace(' ','')]||1.5;
      let placed=false;
      for(let attempt=0;attempt<30&&!placed;attempt++){
        const a=Math.random()*Math.PI*2,r=6+Math.random()*18;
        const px=bx+Math.cos(a)*r,pz=bz+Math.sin(a)*r;
        if(Math.abs(px)>=HALF-4||Math.abs(pz)>=HALF-4||iW(px,pz)) continue;
        if(Object.values(buildings).some(b=>!b.dead&&_dist2D(px,pz,b.x,b.z)<sz+(b.size||1.5)+0.8)) continue;
        // Mining Camp must be placed on a forest — require ≥3 inForest trees nearby
        if(bType==='MiningCamp'){
          const MINE_R=10;
          const forestCount=ctx.resMap?[...ctx.resMap.values()].filter(rn=>rn.isTree&&rn.inForest&&!rn.depleted&&_dist2D(px,pz,rn.x,rn.z)<MINE_R*1.5).length:0;
          if(forestCount<3) continue;
        }
        spend(cost);const b=mkBld(bType,px,pz);buildings[b.id]=b;
        dispatchBuilder(b.id,px,pz);
        gs.events.push({msg:`Enemy built ${bType}!`,type:'warn'});
        ai.buildIdx++;ai.buildTimer=0;placed=true;
      }
      if(!placed) ai.buildTimer=cfg.buildInterval*0.5;
    }
  }

  // ══════════════════════════════════════════════════════════════════════════
  //  5c. CONSTRUCTION OVERSIGHT — ensure every unfinished building always
  //  has at least one villager actively building it.
  //
  //  Every tick, scan all AI buildings that are still underConstruction.
  //  For each one, count villagers whose state is 'moving_to_build' or
  //  'building' and whose buildTarget matches.  If none are assigned,
  //  send the nearest available (idle or gathering non-farm) villager.
  //  This handles interruptions: combat, reassignment, death, etc.
  // ══════════════════════════════════════════════════════════════════════════
  for(const bid in buildings){
    const site=buildings[bid];
    if(!site.underConstruction||site.dead||site.team!==teamNum) continue;

    // Count active builders on this site
    const activeBuilders=Object.values(units).filter(u=>
      !u.dead&&u.team===teamNum&&u.type==='Villager'
      &&(u.state==='moving_to_build'||u.state==='building')
      &&u.buildTarget===bid
    ).length;

    if(activeBuilders>0) continue; // already being built

    // Find a villager to dispatch — prefer idle, then pull from non-farm gathering
    let builder=null;
    let bestDist=Infinity;
    for(const v of myVills){
      if(v._farmId) continue; // never pull a dedicated farm worker
      if(v.state==='moving_to_build'||v.state==='building') continue; // already on another site
      if(v.state==='idle'){
        const d=_dist2D(v.x,v.z,site.x,site.z);
        if(d<bestDist){bestDist=d;builder=v;}
      }
    }
    if(!builder){
      // No idle villager — pull the nearest non-farm gatherer
      for(const v of myVills){
        if(v._farmId) continue;
        if(v.state==='gathering'||v.state==='moving_to_gather'||v.state==='returning'){
          const d=_dist2D(v.x,v.z,site.x,site.z);
          if(d<bestDist){bestDist=d;builder=v;}
        }
      }
    }

    if(builder){
      builder.state='moving_to_build';
      builder.buildTarget=bid;
      builder.tx=site.x+(Math.random()-0.5)*site.size;
      builder.tz=site.z+(Math.random()-0.5)*site.size;
      // Clear any gather state so they don't snap back to gathering next tick
      builder.gatherTarget=null;
      builder._gatherLockTimer=0;
    }
  }

  // ══════════════════════════════════════════════════════════════════════════
  //  5b. MARKET TRADING — sell surplus for gold; buy food when starving
  // ══════════════════════════════════════════════════════════════════════════
  if(cfg.useMarket&&difficulty==='hard'){
    ai.marketTimer=(ai.marketTimer||0)+dt;
    if(ai.marketTimer>=30){
      ai.marketTimer=0;
      const hasMarket=Object.values(buildings).some(b=>!b.dead&&!b.underConstruction&&b.type==='Market'&&b.team===teamNum);
      if(hasMarket){
        if(td.gold<300){
          for(const{res,surplus} of [{res:'food',surplus:500},{res:'wood',surplus:400},{res:'stone',surplus:400}]){
            if((td[res]||0)>=surplus){
              td[res]-=100;td.gold=Math.min(9999,(td.gold||0)+60);
              gs.events.push({type:'trade',action:'sell',res,amt:100,gold:60,team:teamNum});
              gs.events.push({msg:`Enemy traded ${res} for gold!`,type:'warn'});break;
            }
          }
        }
        if(td.food<150&&td.gold>320){
          td.gold-=160;td.food=Math.min(9999,(td.food||0)+100);
          gs.events.push({type:'trade',action:'buy',res:'food',amt:100,gold:160,team:teamNum});
        }
      }
    }
  }

  // ══════════════════════════════════════════════════════════════════════════
  //  6. MILITARY — Train soldiers with counter-composition awareness
  //
  //  Every 15s scan all known enemy units and buildings and derive a counter
  //  priority list.  The list overrides the normal age/strategy priority with
  //  80% probability (20% trains normally to stay unpredictable).
  //
  //  Counter matrix:
  //   Archer-heavy   (>40%)  → Knight > Swordsman > Archer
  //   Swordsman-heavy(>45%)  → Knight > Archer > Swordsman
  //   Knight-heavy   (>35%)  → Swordsman > Archer > Catapult > Knight
  //   Tower/Castle 3+        → Catapult > Knight > Archer > Swordsman
  //   Turtling (10+ buildings, few units) → Catapult > Knight > Archer
  //   Diverse / mixed (3+ types present) → Catapult > Knight > Archer > Swordsman
  //   Default                → normal age/strategy priority
  //
  //  Age-gating: if the top counter pick isn't unlocked yet, fall through to
  //  the next entry in the list.
  // ══════════════════════════════════════════════════════════════════════════

  // Periodic enemy composition scan (every 15 seconds)
  ai.counterScanTimer=(ai.counterScanTimer||0)+dt;
  if(ai.counterScanTimer>=15){
    ai.counterScanTimer=0;

    const ec={Swordsman:0,Archer:0,Knight:0,Catapult:0};
    let eBldCount=0,eTowerCount=0;

    // Hard AI has full knowledge of all enemies (slight cheat, intentional)
    // Moderate/easy AI only counts units within vision range of their own units
    for(const id in units){
      const u=units[id];
      if(u.dead||u.team===teamNum) continue;
      if(difficulty==='hard'||Object.values(units).some(own=>
        !own.dead&&own.team===teamNum&&own.ownerId===aiOwner
        &&_dist2D(own.x,own.z,u.x,u.z)<(own.vision||12))){
        if(ec[u.type]!==undefined) ec[u.type]++;
      }
    }
    for(const bid in buildings){
      const b=buildings[bid];
      if(b.dead||b.team===teamNum) continue;
      eBldCount++;
      if(b.type==='Tower'||b.type==='Castle') eTowerCount++;
    }

    const total=Object.values(ec).reduce((a,b)=>a+b,0);
    const archR =total>0?ec.Archer/total:0;
    const swordR=total>0?ec.Swordsman/total:0;
    const knightR=total>0?ec.Knight/total:0;
    const typesPresent=Object.values(ec).filter(n=>n>=2).length;
    const turtling=eBldCount>=10&&total<5;
    const towerHeavy=eTowerCount>=3;
    const diverseArmy=typesPresent>=3;

    // Derive priority list (most preferred first)
    let cPriority=null;
    if(towerHeavy||turtling){
      cPriority=['Catapult','Knight','Archer','Swordsman'];
    } else if(diverseArmy||total>=12){
      cPriority=['Catapult','Knight','Archer','Swordsman'];
    } else if(archR>=0.40){
      // Archers → Knights crush them
      cPriority=['Knight','Swordsman','Archer'];
    } else if(swordR>=0.45){
      // Swordsmen → Knights outstat, Archers kite
      cPriority=['Knight','Archer','Swordsman'];
    } else if(knightR>=0.35){
      // Knights → numbers + ranged chip; catapults if available
      cPriority=['Swordsman','Archer','Catapult','Knight'];
    }

    ai.counterPriority=cPriority; // null = use standard logic
  }

  // Tower threat fallback (fires even before scan timer)
  const enemyTowerThreat=enemyBase
    ?_towerThreat(enemyBase.x,enemyBase.z,30,buildings,enemyTeam):0;
  const needsCatapults=enemyTowerThreat>=3&&td.age>=2;

  ai.trainTimer+=dt;
  if(ai.trainTimer>=cfg.trainInterval){
    ai.trainTimer=0;
    ai.army=ai.army.filter(id=>units[id]&&!units[id].dead);
    if(ai.army.length<cfg.maxArmy){
      const bars=Object.values(buildings).filter(b=>b.team===teamNum&&b.type==='Barracks'&&!b.dead&&!b.underConstruction);
      for(const bar of bars){
        if(bar.productionQueue.length>0) continue;
        const candidates=cfg.trainTypes.filter(t=>{
          const d=UDEFS[t];if(!d) return false;
          if(t==='Knight'&&td.age<1) return false;
          if(t==='Catapult'&&td.age<2) return false;
          return afford(d.cost)&&td.population+(d.pop||1)<=td.maxPop;
        });
        if(!candidates.length) continue;
        let pick;

        // 80% commit to counter priority; 20% trains normally for unpredictability
        if(difficulty==='hard'&&ai.counterPriority&&Math.random()<0.80){
          // Walk down the counter list until we find something we can actually train
          pick=ai.counterPriority.find(t=>candidates.includes(t))||null;
        }

        if(!pick){
          // Unit flavour: 25% chance to lean toward this AI's preferred unit type
          if(difficulty==='hard'&&ai.unitFlavour&&ai.unitFlavour!=='balanced'
             &&candidates.includes(ai.unitFlavour)&&Math.random()<0.25){
            pick=ai.unitFlavour;
          }
        }

        if(!pick){
          // Standard age/strategy fallback
          if(cfg.unitPreference==='strongest'){
            if(difficulty==='hard'){
              if(needsCatapults&&candidates.includes('Catapult')){
                pick='Catapult';
              } else if(strategy==='rush'){
                if(td.age>=2)      pick=['Knight','Catapult','Archer','Swordsman'].find(t=>candidates.includes(t));
                else if(td.age>=1) pick=['Archer','Knight','Swordsman'].find(t=>candidates.includes(t));
                else               pick=(Math.random()<0.5&&candidates.includes('Archer'))?'Archer':(candidates.includes('Swordsman')?'Swordsman':null);
              } else {
                if(td.age>=2)      pick=['Knight','Catapult','Archer','Swordsman'].find(t=>candidates.includes(t));
                else if(td.age>=1){const r=Math.random();pick=r<0.4&&candidates.includes('Knight')?'Knight':r<0.7&&candidates.includes('Archer')?'Archer':(candidates.includes('Swordsman')?'Swordsman':null);}
                else               pick=candidates.includes('Archer')?'Archer':(candidates.includes('Swordsman')?'Swordsman':null);
              }
              pick=pick||candidates[0];
            } else {
              pick=['Knight','Catapult','Archer','Swordsman','Scout'].find(t=>candidates.includes(t))||candidates[0];
            }
          } else {
            pick=candidates[Math.floor(Math.random()*candidates.length)];
          }
        }
        spend(UDEFS[pick].cost);bar.productionQueue.push(pick);
        if(difficulty==='hard'&&cfg.useBlacksmith){
          const bs=Object.values(buildings).find(b=>b.team===teamNum&&b.type==='Blacksmith'&&!b.dead&&!b.underConstruction);
          if(bs){bar.rallyX=bs.x;bar.rallyZ=bs.z;}
        }
        break;
      }
    }
  }

  // Absorb new combat units into army list
  for(const u of Object.values(units)){
    if(!u.dead&&u.team===teamNum&&u.ownerId===aiOwner&&COMBAT_TYPES.has(u.type)&&!ai.army.includes(u.id))
      ai.army.push(u.id);
  }

  // ══════════════════════════════════════════════════════════════════════════
  //  7. BLACKSMITH — queue up to 3 units; arm as soon as cooldown clears
  // ══════════════════════════════════════════════════════════════════════════
  if(difficulty==='hard'&&cfg.useBlacksmith){
    const SMITH_RANGE=5.5, QUEUE_MAX=3;
    const bs=Object.values(buildings).find(b=>b.team===teamNum&&b.type==='Blacksmith'&&!b.dead&&!b.underConstruction);
    if(bs){
      // Clean queue
      ai.smithQueue=(ai.smithQueue||[]).filter(id=>{const u=units[id];return u&&!u.dead&&!u.armored;});

      ai.smithTimer=(ai.smithTimer||0)+dt;
      if(ai.smithTimer>=cfg.smithInterval){
        ai.smithTimer=0;
        while(ai.smithQueue.length<QUEUE_MAX){
          const c=Object.values(units).find(u=>
            !u.dead&&u.team===teamNum&&u.ownerId===aiOwner
            &&COMBAT_TYPES.has(u.type)&&u.type!=='Scout'&&!u.armored
            &&!ai.smithQueue.includes(u.id)
            &&u.state!=='attacking'&&u.state!=='attacking_building'&&u.state!=='moving_to_attack'
          );
          if(!c) break;
          c.state='moving';c._headingToSmith=true;
          _assignPath(c,bs.x,bs.z,heights,URES,VRES,MAP,HALF,2.5);
          ai.smithQueue.push(c.id);
        }
      }

      // Arm any arrived unit the instant cooldown is 0
      for(const id of ai.smithQueue){
        const u=units[id];if(!u||u.dead||u.armored) continue;
        if(_dist2D(u.x,u.z,bs.x,bs.z)<=SMITH_RANGE&&!(bs.smithCooldown>0)){
          const baseDef=UDEFS[u.type]?.def||0;
          u.def=baseDef+1+(td.researched.includes('Scale Armor')?2:0)+(td.researched.includes('Plate Armor')?4:0);
          u.armored=true;bs.smithCooldown=60;u._headingToSmith=false;
          gs.events.push({msg:`Enemy ${u.type} armored at Blacksmith!`,type:'warn'});
        }
        // Release unit if it's been waiting near the smith for a near-full cooldown
        if(_dist2D(u.x,u.z,bs.x,bs.z)<=SMITH_RANGE&&(bs.smithCooldown||0)>45){
          u._headingToSmith=false;u.state='idle';
        }
      }
    }
  }

  // ══════════════════════════════════════════════════════════════════════════
  //  8. RESEARCH — rush gates Castle Age on minimum army size
  // ══════════════════════════════════════════════════════════════════════════
  if(cfg.researchEnabled){
    ai.researchTimer+=dt;
    // Cooldown varies slightly by strategy and has a small random jitter per AI
    const researchJitter=ai.researchJitter||(ai.researchJitter=(0.8+Math.random()*0.5));
    const cooldown=difficulty==='hard'
      ?(strategy==='boom'?cfg.buildInterval*1.2:strategy==='turtle'?cfg.buildInterval*1.0:cfg.buildInterval*1.8)*researchJitter
      :cfg.buildInterval*2.5;
    if(ai.researchTimer>=cooldown){
      ai.researchTimer=0;
      // Use this AI's personalised research order (set at init, may differ from neighbours)
      const list=ai.researchList||cfg.researchList||[];
      for(const techId of list){
        if(td.researched.includes(techId)) continue;
        if(td.age<(TECH_AGE[techId]||0)) continue;
        if(techId==='Castle Age'&&strategy==='rush'&&ai.army.filter(id=>units[id]&&!units[id].dead).length<10) continue;
        const cost=TECH_COSTS[techId]||{};
        if(!afford(cost)) continue;
        spend(cost);td.researched.push(techId);
        if(techId==='Feudal Age'){td.age=1;gs.events.push({msg:'Enemy advances to Feudal Age!',type:'warn'});}
        if(techId==='Castle Age'){td.age=2;gs.events.push({msg:'Enemy advances to Castle Age!',type:'warn'});}
        if(techId==='Loom') for(const u of Object.values(units)) if(u.team===teamNum&&u.type==='Villager'){u.maxHp+=40;u.hp=Math.min(u.hp+40,u.maxHp);}
        if(techId==='Masonry') for(const b of Object.values(buildings)) if(b.team===teamNum){const nm=Math.floor(b.maxHp*1.2);b.hp=Math.min(nm,Math.floor(b.hp*(nm/b.maxHp)));b.maxHp=nm;}
        if(techId==='Scale Armor') for(const u of Object.values(units)) if(u.team===teamNum) u.def+=2;
        if(techId==='Plate Armor') for(const u of Object.values(units)) if(u.team===teamNum) u.def+=4;
        gs.events.push({msg:`Enemy researched ${techId}!`,type:'warn'});
        break;
      }
    }
  }

  // ══════════════════════════════════════════════════════════════════════════
  //  9. SCOUTING — reveal all enemy bases; keep roaming perimeter
  // ══════════════════════════════════════════════════════════════════════════
  // knownBases is updated continuously in the target-selection block above.
  // Announce the first discovery of each enemy base.
  for(const tn of allEnemyTeams){
    if(ai.knownBases[tn]&&!ai._announcedBase?.[tn]){
      if(!ai._announcedBase) ai._announcedBase={};
      ai._announcedBase[tn]=true;
      gs.events.push({msg:`Enemy base located!`,type:'warn'});
    }
  }

  // Scout: roam toward unknown enemies; orbit current target's perimeter once found
  const myScout=Object.values(units).find(u=>!u.dead&&u.team===teamNum&&u.ownerId===aiOwner&&u.type==='Scout')
    ||Object.values(units).find(u=>!u.dead&&u.team===teamNum&&u.ownerId===aiOwner&&u.type!=='Villager'&&(u.state==='idle'||u.state==='moving'));
  if(myScout&&myScout.ownerId===aiOwner&&myScout.state!=='attacking'&&myScout.state!=='attacking_building'&&!myScout._retreating){
    if(!ai.scoutLastPos){ai.scoutLastPos={x:myScout.x,z:myScout.z};ai.scoutStuckTimer=0;}
    const moved=_dist2D(myScout.x,myScout.z,ai.scoutLastPos.x,ai.scoutLastPos.z);
    if(moved>=0.5){ai.scoutLastPos={x:myScout.x,z:myScout.z};ai.scoutStuckTimer=0;}
    else ai.scoutStuckTimer=(ai.scoutStuckTimer||0)+dt;
    const stuck=myScout.state==='moving'&&ai.scoutStuckTimer>=4;
    const needsWpt=myScout.state==='idle'||stuck
      ||(myScout.state==='moving'&&_dist2D(myScout.x,myScout.z,ai.scoutTarget?.x||myScout.x,ai.scoutTarget?.z||myScout.z)<3);
    if(needsWpt){
      if(stuck) ai.scoutStuckTimer=0;
      // Choose which enemy to scout toward: prefer ones we haven't found yet,
      // otherwise orbit the current attack target's perimeter
      const unknownEnemies=allEnemyTeams.filter(tn=>!ai.knownBases[tn]);
      let ex,ez,orbitMode=false;
      if(unknownEnemies.length>0){
        // Head toward the closest unknown enemy's spawn
        let best=null,bestD=Infinity;
        for(const tn of unknownEnemies){
          const sp=ctx.spawnPositions?ctx.spawnPositions[tn-1]:null;
          if(!sp) continue;
          const d=_dist2D(bx,bz,sp.x,sp.z);
          if(d<bestD){bestD=d;best=sp;}
        }
        ex=(best||enemySpawn).x; ez=(best||enemySpawn).z;
      } else if(enemyBase){
        ex=enemyBase.x; ez=enemyBase.z; orbitMode=Math.random()<0.6;
      } else {
        ex=enemySpawn.x; ez=enemySpawn.z;
      }
      let sx=myScout.x,sz=myScout.z,picked=false;
      for(let i=0;i<20&&!picked;i++){
        const angle=orbitMode?Math.random()*Math.PI*2:Math.atan2(ez-bz,ex-bx)+(Math.random()-0.5)*(0.8+i*0.15);
        const dist=orbitMode?20+Math.random()*20:15+Math.random()*35;
        const cx=Math.max(-HALF+4,Math.min(HALF-4,ex+Math.cos(angle)*dist));
        const cz=Math.max(-HALF+4,Math.min(HALF-4,ez+Math.sin(angle)*dist));
        if(iW(cx,cz)) continue;
        if(ai.scoutTarget&&_dist2D(cx,cz,ai.scoutTarget.x,ai.scoutTarget.z)<8) continue;
        sx=cx;sz=cz;picked=true;
      }
      if(!picked){sx=ex+(Math.random()-0.5)*10;sz=ez+(Math.random()-0.5)*10;}
      _assignPath(myScout,sx,sz,heights,URES,VRES,MAP,HALF);
      myScout.state='moving';
      ai.scoutTarget={x:sx,z:sz};ai.scoutLastPos={x:myScout.x,z:myScout.z};
    }
  }

  // ══════════════════════════════════════════════════════════════════════════
  //  9b. MODERATE HARASSMENT — occasionally raid enemy resource nodes
  // ══════════════════════════════════════════════════════════════════════════
  if(difficulty==='moderate'&&enemyBase!==null){
    ai.harassTimer=(ai.harassTimer||0)+dt;
    if(ai.harassTimer>=120){
      ai.harassTimer=0;
      const harasser=Object.values(units).find(u=>
        !u.dead&&u.team===teamNum&&u.ownerId===aiOwner
        &&(u.type==='Scout'||u.type==='Swordsman')&&u.state==='idle');
      if(harasser){
        const tgt=resNodes.find(r=>!r.depleted&&_dist2D(r.x,r.z,enemyBase.x,enemyBase.z)<25);
        if(tgt){harasser.tx=tgt.x+(Math.random()-0.5)*3;harasser.tz=tgt.z+(Math.random()-0.5)*3;harasser.state='moving_to_attack';harasser._waypoints=null;}
      }
    }
  }

  // ══════════════════════════════════════════════════════════════════════════
  //  10. BASE DEFENSE
  // ══════════════════════════════════════════════════════════════════════════
  const DEFENSE_RADIUS=difficulty==='hard'?25:20;
  let baseUnderAttack=false;
  for(const id in units){
    const u=units[id];
    if(!u.dead&&u.team!==teamNum&&_dist2D(u.x,u.z,bx,bz)<DEFENSE_RADIUS){baseUnderAttack=true;break;}
  }
  if(baseUnderAttack){
    for(const id of ai.army){
      const u=units[id];if(!u||u.dead||u.ownerId!==aiOwner||u._retreating) continue;
      if(u.state==='attacking'||u.state==='attacking_building') continue;
      let closest=null,cd=DEFENSE_RADIUS*1.5;
      for(const oid in units){
        const o=units[oid];
        if(!o.dead&&o.team!==teamNum){const d=_dist2D(bx,bz,o.x,o.z);if(d<cd){cd=d;closest=o;}}
      }
      if(closest){u.target=closest.id;u.state='attacking';u._waypoints=null;}
    }
  }

  // ══════════════════════════════════════════════════════════════════════════
  //  11. EARLY RUSH HARASSMENT — 2-3 unit raid at ~50s (hard/rush only)
  // ══════════════════════════════════════════════════════════════════════════
  if(difficulty==='hard'&&!ai.harassSent&&gs.gameTime>=(ai.harassTime||50)&&enemyBase!==null){
    ai.harassSent=true;
    const raiders=[];
    for(const id of ai.army){
      const u=units[id];
      if(u&&!u.dead&&u.ownerId===aiOwner&&(u.type==='Scout'||u.type==='Swordsman')&&!u._retreating){
        raiders.push(id);if(raiders.length>=3) break;
      }
    }
    if(raiders.length>=2){
      gs.events.push({msg:'⚔ Enemy raiding party spotted!',type:'bad'});
      const rtx=enemyBase.x,rtz=enemyBase.z;
      raiders.forEach(id=>{
        const u=units[id];if(!u) return;
        u.state='moving_to_attack';
        _assignPath(u,rtx,rtz,heights,URES,VRES,MAP,HALF,8);
        u._pathStuckTimer=0;
      });
    }
  }

  // ══════════════════════════════════════════════════════════════════════════
  //  12. ATTACK WAVES — role-based formation + flanking angle variance
  //
  //  Target is the current focus enemy's nearest live building.
  //  After each wave finishes, the target may be re-rolled so the AI
  //  can switch focus to a different enemy.
  // ══════════════════════════════════════════════════════════════════════════
  ai.attackTimer+=dt;
  if(ai.postWipeTimer>0){ai.postWipeTimer=Math.max(0,ai.postWipeTimer-dt);ai.attackTimer=0;}

  const readyArmy=ai.army.filter(id=>units[id]&&!units[id].dead&&!units[id]._retreating);

  // Build attack target from the current focus enemy's known base,
  // using resistance state to choose what to march toward
  let target=null;
  if(enemyTeam!==null&&enemyBase!==null){
    const baseX=enemyBase.x, baseZ=enemyBase.z;
    const nearBuildings=Object.values(buildings).filter(b=>
      !b.dead&&b.team===enemyTeam&&_dist2D(b.x,b.z,baseX,baseZ)<35);

    if(rs==='active'){
      // Resistance present — prioritise towers, then barracks, then anything
      const tower=nearBuildings.find(b=>b.type==='Tower'||b.type==='Castle');
      const barracks=nearBuildings.find(b=>b.type==='Barracks');
      target=tower||barracks||nearBuildings[0]||{x:baseX,z:baseZ};
    } else if(rs==='cleared'){
      // Military cleared — go for villagers first, then TC
      const enemyVill=Object.values(units).find(u=>
        !u.dead&&u.team===enemyTeam&&u.type==='Villager'&&
        _dist2D(u.x,u.z,baseX,baseZ)<40);
      const tc=nearBuildings.find(b=>b.type==='Town Center');
      target=enemyVill?{x:enemyVill.x,z:enemyVill.z}:tc||nearBuildings[0]||{x:baseX,z:baseZ};
    } else {
      // No resistance — go for villagers → houses → TC
      const enemyVill=Object.values(units).find(u=>
        !u.dead&&u.team===enemyTeam&&u.type==='Villager'&&
        _dist2D(u.x,u.z,baseX,baseZ)<40);
      const house=nearBuildings.find(b=>b.type==='House');
      const tc=nearBuildings.find(b=>b.type==='Town Center');
      target=enemyVill?{x:enemyVill.x,z:enemyVill.z}:house||tc||nearBuildings[0]||{x:baseX,z:baseZ};
    }

    // Keep knownBases fresh
    const tc2=nearBuildings.find(b=>b.type==='Town Center');
    if(tc2) ai.knownBases[enemyTeam]={x:tc2.x,z:tc2.z};
  }
  if(!target) ai.attackTimer=0;

  let currentThreshold=cfg.attackThreshold;
  if(cfg.attackWaveSizes){
    if(ai.waveIndex==null) ai.waveIndex=0;
    currentThreshold=cfg.attackWaveSizes[ai.waveIndex%cfg.attackWaveSizes.length];
  }

  // All-in: if the army has grown to 75%+ of maxArmy, commit everything now
  // regardless of wave threshold — don't sit on a huge idle army
  const maxArmy=ai.maxArmy||cfg.maxArmy||40;
  const allInThreshold=Math.round(maxArmy*0.75);
  const timerMet=ai.attackTimer>=cfg.attackInterval;
  const armyOverflow=readyArmy.length>=allInThreshold;
  // Also lower the effective threshold to actual army size so we never wait
  // for MORE troops when we already exceed the wave threshold
  const effectiveThreshold=Math.min(currentThreshold,readyArmy.length);

  const minAttackTime=difficulty==='hard'
    ?(strategy==='rush'?60:strategy==='turtle'?300:120)
    :cfg.attackInterval*0.4;
  const shouldAttack=target!=null&&gs.gameTime>=minAttackTime&&(
    // Normal: army meets threshold and timer has elapsed
    (readyArmy.length>=currentThreshold&&timerMet)
    // All-in: army is very large, attack now regardless of timer
    ||armyOverflow
  );

  if(shouldAttack){
    ai.isAttacking=true;ai.attackTimer=0;
    // Only advance the wave escalation index on timer-triggered attacks,
    // not on all-in attacks (which should reset to keep escalation meaningful)
    if(timerMet&&cfg.attackWaveSizes) ai.waveIndex=((ai.waveIndex||0)+1)%cfg.attackWaveSizes.length;
    // Send as many units as we have (up to currentThreshold, or all if all-in)
    const waveSize=armyOverflow?readyArmy.length:Math.min(readyArmy.length,currentThreshold);
    const wave=readyArmy.slice(0,waveSize);
    gs.events.push({msg:`⚔ Enemy ${armyOverflow?'all-in assault':strategy==='rush'?'raid':'assault'}! ${wave.length} warriors!`,type:'bad'});

    const tx=target.x,tz=target.z;
    // Flanking: slightly rotate march direction each wave
    const flankAngle=(Math.random()-0.5)*0.6;
    const bDX=tx-bx,bDZ=tz-bz,bLen=Math.sqrt(bDX*bDX+bDZ*bDZ)||1;
    const cosA=Math.cos(flankAngle),sinA=Math.sin(flankAngle);
    const fDX=(bDX*cosA-bDZ*sinA)/bLen,fDZ=(bDX*sinA+bDZ*cosA)/bLen;
    const perpX=-fDZ,perpZ=fDX;

    const meleeIds=wave.filter(id=>MELEE_TYPES.has(units[id]?.type));
    const archerIds=wave.filter(id=>units[id]?.type==='Archer');
    const catIds=wave.filter(id=>units[id]?.type==='Catapult');
    const otherIds=wave.filter(id=>!meleeIds.includes(id)&&!archerIds.includes(id)&&!catIds.includes(id));

    function dispatch(u,destX,destZ,holdBack){
      if(!u||u.ownerId!==aiOwner) return;
      // Hold-back: position ranged/siege units behind the front line
      let ax=destX,az=destZ;
      if(holdBack>0){ax=destX-fDX*holdBack;az=destZ-fDZ*holdBack;}
      u.state='moving_to_attack';
      _assignPath(u,ax,az,heights,URES,VRES,MAP,HALF,holdBack>0?4:5);
    }

    meleeIds.forEach((id,i)=>{
      const u=units[id];if(!u) return;
      const spread=(i-(meleeIds.length-1)/2)*2.5;
      dispatch(u,tx+perpX*spread,tz+perpZ*spread,0);
    });
    archerIds.forEach((id,i)=>{
      const u=units[id];if(!u) return;
      const spread=(i-(archerIds.length-1)/2)*3;
      dispatch(u,tx+perpX*spread,tz+perpZ*spread,6);
    });
    catIds.forEach(id=>dispatch(units[id],tx,tz,12));
    otherIds.forEach(id=>dispatch(units[id],tx,tz,0));
  }

  // Post-wipe detection
  const prevSize=ai.army.length;
  ai.army=ai.army.filter(id=>units[id]&&!units[id].dead);
  if(ai.isAttacking&&prevSize>4&&ai.army.length===0) ai.postWipeTimer=30;

  const stillMarching=ai.army.some(id=>{const u=units[id];return u&&(u.state==='moving_to_attack'||u.state==='attacking'||u.state==='attacking_building');});
  if(ai.isAttacking&&!stillMarching){
    ai.isAttacking=false;ai.attackTimer=0;
    // Force a target re-roll after each wave so the AI may switch to a different enemy
    ai.targetRerollTimer=0;
  }

  // ── Patrol near base when idle ──────────────────────────────────────────
  if(!ai.isAttacking&&!baseUnderAttack){
    for(const id of readyArmy){
      const u=units[id];
      if(!u||u.state!=='idle'||u.ownerId!==aiOwner||u._headingToSmith||u._retreating||u.type==='Scout') continue;
      const pt=safePt(bx,bz,difficulty==='hard'?20:16);
      if(pt){_assignPath(u,pt.x,pt.z,heights,URES,VRES,MAP,HALF);u.state='moving';}
    }
  }
}
module.exports={tickAI,_findWaterPath,_assignPath};
