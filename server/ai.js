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
//  WATER PATHFINDING
//  Step size 2 cells (~3.3 world units) for tighter corner-hugging.
//  BFS visits capped at 4000 to bound worst-case cost.
// ─────────────────────────────────────────────────────────────────────────────
function _findWaterPath(sx,sz,tx,tz,h,URES,VRES,MAP,HALF){
  function toCell(wx,wz){
    return [Math.max(0,Math.min(URES,Math.round((wx+HALF)/MAP*URES))),
            Math.max(0,Math.min(VRES,Math.round((wz+HALF)/MAP*VRES)))];
  }
  function toWorld(c,r){ return [-HALF+c/URES*MAP,-HALF+r/VRES*MAP]; }
  function cellWet(c,r){ const[wx,wz]=toWorld(c,r); return _isW(wx,wz,h,URES,VRES,MAP,HALF); }

  const[sc,sr]=toCell(sx,sz);
  const[ec,er]=toCell(tx,tz);

  // Quick line-of-sight — skip BFS if path is clear
  if(!cellWet(ec,er)&&!_isW(tx,tz,h,URES,VRES,MAP,HALF)){
    let blocked=false;
    const steps=Math.max(Math.abs(ec-sc),Math.abs(er-sr));
    for(let i=1;i<steps&&!blocked;i++){
      if(cellWet(Math.round(sc+(ec-sc)*i/steps),Math.round(sr+(er-sr)*i/steps))) blocked=true;
    }
    if(!blocked) return [{x:tx,z:tz}];
  }

  const STEP=2, MAX_V=4000;
  const vis=new Map(), key=(c,r)=>c*10000+r;
  const q=[[sc,sr]]; vis.set(key(sc,sr),null);
  let found=null, v=0;
  while(q.length&&!found&&v<MAX_V){
    const[c,r]=q.shift(); v++;
    if(Math.abs(c-ec)<=STEP*2&&Math.abs(r-er)<=STEP*2){found=[c,r];break;}
    for(const[dc,dr] of [[STEP,0],[-STEP,0],[0,STEP],[0,-STEP],[STEP,STEP],[-STEP,STEP],[STEP,-STEP],[-STEP,-STEP]]){
      const nc=c+dc,nr=r+dr;
      if(nc<0||nc>URES||nr<0||nr>VRES) continue;
      const k=key(nc,nr);
      if(vis.has(k)||cellWet(nc,nr)) continue;
      vis.set(k,[c,r]); q.push([nc,nr]);
    }
  }
  if(!found) return [{x:tx,z:tz}];

  const path=[]; let cur=found;
  while(cur){path.unshift(cur);cur=vis.get(key(cur[0],cur[1]));}

  const wps=[];
  for(let i=1;i<path.length;i++){const[wx,wz]=toWorld(path[i][0],path[i][1]);wps.push({x:wx,z:wz});}
  wps.push({x:tx,z:tz});

  // Prune near-collinear points
  const out=[wps[0]];
  for(let i=1;i<wps.length-1;i++){
    const p=out[out.length-1],n=wps[i+1];
    const d1x=wps[i].x-p.x,d1z=wps[i].z-p.z,d2x=n.x-wps[i].x,d2z=n.z-wps[i].z;
    if(Math.abs(d1x*d2z-d1z*d2x)>0.8) out.push(wps[i]);
  }
  if(wps.length>0) out.push(wps[wps.length-1]);
  return out;
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
  const{uid,UDEFS,BCOSTS,BHPS,BSIZES,MAP,HALF,URES,VRES}=ctx;
  const cfg=DIFF_CFG[difficulty]||DIFF_CFG.moderate;
  const{gs}=lobby;
  const{units,buildings,teams,resNodes,heights}=gs;
  const td=teams[teamNum];
  // In a 4-player game, pick the "primary enemy" as the team with the
  // nearest Town Center to ours — updated lazily every few seconds.
  const numTeams=Object.keys(teams).length;
  const aiOwner='ai_team_'+teamNum;

  // Resolve enemy team: for 2p always the other; for 3-4p use nearest TC
  function resolveEnemyTeam(){
    if(numTeams<=2) return teamNum===1?2:1;
    const myTC=Object.values(buildings).find(b=>b.team===teamNum&&b.type==='Town Center'&&!b.dead);
    if(!myTC) return teamNum===1?2:1;
    let nearest=null, nearestDist=Infinity;
    for(const tn of Object.keys(teams).map(Number)){
      if(tn===teamNum) continue;
      const tc=Object.values(buildings).find(b=>b.team===tn&&b.type==='Town Center'&&!b.dead);
      if(!tc) continue;
      const d=_dist2D(myTC.x,myTC.z,tc.x,tc.z);
      if(d<nearestDist){nearestDist=d;nearest=tn;}
    }
    return nearest||(teamNum===1?2:1);
  }
  const enemyTeam=resolveEnemyTeam();

  // Own spawn position
  const ownSpawn=ctx.spawnPositions?ctx.spawnPositions[teamNum-1]:{x:ctx.pox||0,z:ctx.poz||0};
  // Enemy spawn fallback (before we've scouted)
  const enemySpawn=ctx.spawnPositions?ctx.spawnPositions[enemyTeam-1]:{x:ctx.aox||0,z:ctx.aoz||0};

  // ── First-time initialisation ──────────────────────────────────────────────
  if(!lobby.aiState) lobby.aiState={};
  if(!lobby.aiState[teamNum]){
    let strategy='rush';
    if(difficulty==='hard') strategy=Math.random()<0.45?'boom':'rush';
    lobby.aiState[teamNum]={
      buildTimer:cfg.buildInterval*0.3*Math.random(),
      attackTimer:0,trainTimer:0,researchTimer:cfg.buildInterval*2,
      buildIdx:0,army:[],isAttacking:false,
      strategy,
      smithTimer:0,smithQueue:[],
      marketTimer:0,
      harassSent:false,
      postWipeTimer:0,
      turtleMode:false,
      harassTimer:0,
    };
    if(difficulty==='hard'){
      cfg.buildQueue=strategy==='boom'?[...HARD_BUILD_QUEUE_BOOM]:[...HARD_BUILD_QUEUE_RUSH];
      if(strategy==='boom'){
        cfg.maxVillagers=32;cfg.attackInterval=200;
        cfg.attackWaveSizes=[8,16,25,35,45];
      } else {
        cfg.maxVillagers=24;cfg.attackInterval=120;
        cfg.attackWaveSizes=[5,10,18,28,40];
      }
    }
  }
  const ai=lobby.aiState[teamNum];
  const strategy=ai.strategy||'rush';

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
    return{id:uid(),type,x,z,team:teamNum,ownerId:aiOwner,
      hp:BHPS[key]||400,maxHp:BHPS[key]||400,size:BSIZES[key]||1.5,
      productionQueue:[],productionTimer:0,dead:false,atkTimer:0,
      underConstruction:false,buildProgress:0,buildTime:0,
      rallyX:null,rallyZ:null,rallyResourceId:null};
  }
  function safePt(cx,cz,spread=16){
    for(let i=0;i<20;i++){
      const a=Math.random()*Math.PI*2,r=4+Math.random()*spread;
      const px=Math.max(-HALF+3,Math.min(HALF-3,cx+Math.cos(a)*r));
      const pz=Math.max(-HALF+3,Math.min(HALF-3,cz+Math.sin(a)*r));
      if(!iW(px,pz)) return{x:px,z:pz};
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
  //  1. AUTO-ATTACK / DEFENSE
  // ══════════════════════════════════════════════════════════════════════════
  const detRange=cfg.detectionRange||12;
  for(const id in units){
    const u=units[id];
    if(u.dead||u.team!==teamNum||u.ownerId!==aiOwner||!COMBAT_TYPES.has(u.type)) continue;
    if(u.state==='attacking'||u.state==='attacking_building') continue;
    if(u._headingToSmith&&u.state==='moving') continue; // don't break smith trips
    const closeRange=u.state==='moving_to_attack'?4:detRange;
    let nearEnemy=null,nearDist=closeRange;
    for(const oid in units){
      const o=units[oid];
      if(!o.dead&&o.team!==teamNum){const d=_dist2D(u.x,u.z,o.x,o.z);if(d<nearDist){nearDist=d;nearEnemy=o;}}
    }
    if(nearEnemy){u.target=nearEnemy.id;u.state='attacking';u._waypoints=null;continue;}
    if(u.state==='idle'||u.state==='moving'){
      let nearBld=null,nearBldDist=detRange*0.7;
      for(const bid in buildings){
        const b=buildings[bid];
        if(!b.dead&&b.team!==teamNum){const d=_dist2D(u.x,u.z,b.x,b.z);if(d<nearBldDist){nearBldDist=d;nearBld=b;}}
      }
      if(nearBld){u.target=nearBld.id;u.state='attacking_building';u._waypoints=null;}
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
      u.tx=bx+(Math.random()-0.5)*4; u.tz=bz+(Math.random()-0.5)*4;
      u._waypoints=null; u._retreating=true;
    }
    if(u._retreating&&u.state==='idle') u._retreating=false;
  }

  // ══════════════════════════════════════════════════════════════════════════
  //  2. WATER PATHFINDING — stuck detection and re-routing
  // ══════════════════════════════════════════════════════════════════════════
  for(const id in units){
    const u=units[id];
    if(u.dead||u.team!==teamNum||u.ownerId!==aiOwner) continue;
    if(u.state!=='moving_to_attack'&&u.state!=='moving') continue;
    if(!isFinite(u.tx)||!isFinite(u.tz)) continue;
    if(!u._pathLastPos){u._pathLastPos={x:u.x,z:u.z};u._pathStuckTimer=0;}
    const moved=_dist2D(u.x,u.z,u._pathLastPos.x,u._pathLastPos.z);
    if(moved>1.0){u._pathLastPos={x:u.x,z:u.z};u._pathStuckTimer=0;}
    else u._pathStuckTimer=(u._pathStuckTimer||0)+dt;
    if(u._pathStuckTimer>=2.0){
      u._pathStuckTimer=0;u._pathLastPos={x:u.x,z:u.z};
      if(iW((u.x+u.tx)/2,(u.z+u.tz)/2)||iW(u.tx,u.tz))
        u._waypoints=_findWaterPath(u.x,u.z,u.tx,u.tz,heights,URES,VRES,MAP,HALF);
    }
    if(u._waypoints&&u._waypoints.length>0){
      while(u._waypoints.length>1&&_dist2D(u.x,u.z,u._waypoints[0].x,u._waypoints[0].z)<2.5)
        u._waypoints.shift();
      const wp=u._waypoints[0];
      if(_dist2D(wp.x,wp.z,u.tx,u.tz)>3){u.tx=wp.x;u.tz=wp.z;}
      else u._waypoints=null;
    }
  }

  // ══════════════════════════════════════════════════════════════════════════
  //  3. ECONOMY — Villager gathering with lock-in to prevent thrashing
  // ══════════════════════════════════════════════════════════════════════════
  const myVills=Object.values(units).filter(u=>!u.dead&&u.team===teamNum&&u.type==='Villager'&&u.ownerId===aiOwner);
  const lockIn=cfg.villagerLockIn||0;

  // Strategy-aware resource priority
  let resPriority;
  if(difficulty==='hard'){
    resPriority=strategy==='rush'?['food','gold','wood','stone']:['food','wood','gold','stone'];
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
  //  3b. FARM STAFFING — idle first; fall back to lowest-priority gatherer
  // ══════════════════════════════════════════════════════════════════════════
  for(const bid in buildings){
    const farm=buildings[bid];
    if(farm.dead||farm.underConstruction||farm.type!=='Farm'||farm.team!==teamNum||!farm.farmNodeId) continue;
    const staffed=Object.values(units).some(u=>
      !u.dead&&u.team===teamNum&&u.type==='Villager'
      &&(u.state==='gathering'||u.state==='moving_to_gather')&&u.gatherTarget===farm.farmNodeId);
    if(staffed) continue;
    let pick=null,bestDist=Infinity;
    for(const v of myVills){
      if(v.state==='idle'){const d=_dist2D(v.x,v.z,farm.x,farm.z);if(d<bestDist){bestDist=d;pick=v;}}
    }
    if(!pick){
      for(const res of['stone','wood','gold']){
        const c=myVills.find(v=>
          (v.state==='gathering'||v.state==='moving_to_gather')&&getResNode(v.gatherTarget)?.type===res);
        if(c){pick=c;break;}
      }
    }
    if(pick){
      pick.gatherTarget=farm.farmNodeId;pick.state='moving_to_gather';
      pick.tx=farm.x+(Math.random()-0.5)*0.4;pick.tz=farm.z+(Math.random()-0.5)*0.4;
      pick._gatherLockTimer=lockIn;gatherCount['food']=(gatherCount['food']||0)+1;
    }
  }

  // ══════════════════════════════════════════════════════════════════════════
  //  4. ECONOMY — Train villagers
  // ══════════════════════════════════════════════════════════════════════════
  if(myVills.length<cfg.maxVillagers&&td.population<td.maxPop-1){
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
      if(pt){spend(BCOSTS.House||{wood:30});const b=mkBld('House',pt.x,pt.z);buildings[b.id]=b;td.maxPop+=5;}
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
        spend(tcost);buildings[mkBld('Tower',px,pz).id]=mkBld('Tower',px,pz);
        gs.events.push({msg:'Enemy fortifying defenses!',type:'warn'});break;
      }
    }
  }

  ai.buildTimer+=dt;
  if(ai.buildTimer>=cfg.buildInterval&&ai.buildIdx<cfg.buildQueue.length){
    const bType=cfg.buildQueue[ai.buildIdx];
    const cost=BCOSTS[bType]||{};
    const ageGated=(bType==='Castle'&&td.age<2)||(bType==='Market'&&td.age<1);
    if(ageGated){ai.buildIdx++;ai.buildTimer=0;}
    else if(afford(cost)){
      const sz=BSIZES[bType.replace(' ','')]||1.5;
      let placed=false;
      for(let attempt=0;attempt<30&&!placed;attempt++){
        const a=Math.random()*Math.PI*2,r=6+Math.random()*18;
        const px=bx+Math.cos(a)*r,pz=bz+Math.sin(a)*r;
        if(Math.abs(px)>=HALF-4||Math.abs(pz)>=HALF-4||iW(px,pz)) continue;
        if(Object.values(buildings).some(b=>!b.dead&&_dist2D(px,pz,b.x,b.z)<sz+(b.size||1.5)+0.8)) continue;
        spend(cost);const b=mkBld(bType,px,pz);buildings[b.id]=b;
        if(bType==='House') td.maxPop+=5;
        gs.events.push({msg:`Enemy built ${bType}!`,type:'warn'});
        ai.buildIdx++;ai.buildTimer=0;placed=true;
      }
      if(!placed) ai.buildTimer=cfg.buildInterval*0.5;
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
  //  6. MILITARY — Train soldiers
  //  Tower-awareness: shift to Catapults when enemy has 3+ defenses
  // ══════════════════════════════════════════════════════════════════════════
  const enemyTowerThreat=ai.knownEnemyX!==undefined
    ?_towerThreat(ai.knownEnemyX,ai.knownEnemyZ,30,buildings,enemyTeam):0;
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
          c.tx=bs.x+(Math.random()-0.5)*2.5;c.tz=bs.z+(Math.random()-0.5)*2.5;
          c.state='moving';c._headingToSmith=true;c._waypoints=null;
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
    const cooldown=difficulty==='hard'
      ?(strategy==='boom'?cfg.buildInterval*1.5:cfg.buildInterval*2)
      :cfg.buildInterval*2.5;
    if(ai.researchTimer>=cooldown){
      ai.researchTimer=0;
      let list=[...cfg.researchList];
      if(difficulty==='hard'&&strategy==='boom')
        list=['Iron Tools','Loom','Horse Collar','Feudal Age','Masonry','Fletching','Scale Armor','Castle Age','Chemistry','Plate Armor'];
      else if(difficulty==='hard'&&strategy==='rush')
        list=['Iron Tools','Loom','Feudal Age','Fletching','Scale Armor','Masonry','Horse Collar','Castle Age','Chemistry','Plate Armor'];
      for(const techId of list){
        if(td.researched.includes(techId)) continue;
        if(td.age<(TECH_AGE[techId]||0)) continue;
        // Rush: delay Castle Age until a minimum army is ready
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
  //  9. SCOUTING — find base; keep roaming perimeter afterward
  // ══════════════════════════════════════════════════════════════════════════
  if(ai.knownEnemyX===undefined){
    outer: for(const id in units){
      const u=units[id];if(!u.dead&&u.team===teamNum&&u.ownerId===aiOwner){
        for(const bid in buildings){
          const b=buildings[bid];
          if(!b.dead&&b.team===enemyTeam&&_dist2D(u.x,u.z,b.x,b.z)<(u.vision||12)){
            ai.knownEnemyX=b.x;ai.knownEnemyZ=b.z;
            gs.events.push({msg:'Enemy base located!',type:'warn'});break outer;
          }
        }
      }
    }
  } else {
    for(const bid in buildings){
      const b=buildings[bid];
      if(!b.dead&&b.team===enemyTeam&&b.type==='Town Center'){ai.knownEnemyX=b.x;ai.knownEnemyZ=b.z;break;}
    }
  }

  // Scout: always roam, orbiting enemy perimeter once base is known
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
      const ex=ai.knownEnemyX!==undefined?ai.knownEnemyX:enemySpawn.x;
      const ez=ai.knownEnemyZ!==undefined?ai.knownEnemyZ:enemySpawn.z;
      const orbitEnemy=ai.knownEnemyX!==undefined&&Math.random()<0.6;
      let sx=myScout.x,sz=myScout.z,picked=false;
      for(let i=0;i<20&&!picked;i++){
        const angle=orbitEnemy?Math.random()*Math.PI*2:Math.atan2(ez-bz,ex-bx)+(Math.random()-0.5)*(0.8+i*0.15);
        const dist=orbitEnemy?20+Math.random()*20:15+Math.random()*35;
        const cx=Math.max(-HALF+4,Math.min(HALF-4,ex+Math.cos(angle)*dist));
        const cz=Math.max(-HALF+4,Math.min(HALF-4,ez+Math.sin(angle)*dist));
        if(iW(cx,cz)) continue;
        if(ai.scoutTarget&&_dist2D(cx,cz,ai.scoutTarget.x,ai.scoutTarget.z)<8) continue;
        sx=cx;sz=cz;picked=true;
      }
      if(!picked){sx=ex+(Math.random()-0.5)*10;sz=ez+(Math.random()-0.5)*10;}
      if(stuck&&iW(sx+(myScout.x-sx)/2,sz+(myScout.z-sz)/2)){
        const wps=_findWaterPath(myScout.x,myScout.z,sx,sz,heights,URES,VRES,MAP,HALF);
        myScout._waypoints=wps;if(wps.length>0){sx=wps[0].x;sz=wps[0].z;}
      }
      myScout.tx=sx;myScout.tz=sz;myScout.state='moving';
      ai.scoutTarget={x:sx,z:sz};ai.scoutLastPos={x:myScout.x,z:myScout.z};
    }
  }

  // ══════════════════════════════════════════════════════════════════════════
  //  9b. MODERATE HARASSMENT — occasionally raid enemy resource nodes
  // ══════════════════════════════════════════════════════════════════════════
  if(difficulty==='moderate'&&ai.knownEnemyX!==undefined){
    ai.harassTimer=(ai.harassTimer||0)+dt;
    if(ai.harassTimer>=120){
      ai.harassTimer=0;
      const harasser=Object.values(units).find(u=>
        !u.dead&&u.team===teamNum&&u.ownerId===aiOwner
        &&(u.type==='Scout'||u.type==='Swordsman')&&u.state==='idle');
      if(harasser){
        const tgt=resNodes.find(r=>!r.depleted&&_dist2D(r.x,r.z,ai.knownEnemyX,ai.knownEnemyZ)<25);
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
  if(difficulty==='hard'&&strategy==='rush'&&!ai.harassSent&&gs.gameTime>=50&&ai.knownEnemyX!==undefined){
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
      const rtx=ai.knownEnemyX,rtz=ai.knownEnemyZ;
      const sharedWps=iW((bx+rtx)/2,(bz+rtz)/2)?_findWaterPath(bx,bz,rtx,rtz,heights,URES,VRES,MAP,HALF):null;
      raiders.forEach(id=>{
        const u=units[id];if(!u) return;
        const ax=rtx+(Math.random()-0.5)*8,az=rtz+(Math.random()-0.5)*8;
        u.state='moving_to_attack';
        if(sharedWps&&sharedWps.length>0){
          u._waypoints=[...sharedWps.map(wp=>({...wp}))];
          u._waypoints[u._waypoints.length-1]={x:ax,z:az};
          u.tx=u._waypoints[0].x;u.tz=u._waypoints[0].z;
        } else {u._waypoints=null;u.tx=ax;u.tz=az;}
        u._pathLastPos={x:u.x,z:u.z};u._pathStuckTimer=0;
      });
    }
  }

  // ══════════════════════════════════════════════════════════════════════════
  //  12. ATTACK WAVES — role-based formation + flanking angle variance
  //
  //  Melee  (Swordsman/Knight) → front line, laterally spread
  //  Archer                    → 6 units behind the melee line
  //  Catapult                  → 12 units behind (advance last)
  //  Post-wipe timer prevents attacking before army rebuilds
  // ══════════════════════════════════════════════════════════════════════════
  ai.attackTimer+=dt;
  if(ai.postWipeTimer>0){ai.postWipeTimer=Math.max(0,ai.postWipeTimer-dt);ai.attackTimer=0;}

  const readyArmy=ai.army.filter(id=>units[id]&&!units[id].dead&&!units[id]._retreating);

  let target=null;
  if(ai.knownEnemyX!==undefined){
    const nb=Object.values(buildings).find(b=>!b.dead&&b.team===enemyTeam&&_dist2D(b.x,b.z,ai.knownEnemyX,ai.knownEnemyZ)<30);
    target=nb||{x:ai.knownEnemyX,z:ai.knownEnemyZ};
    if(nb){ai.knownEnemyX=nb.x;ai.knownEnemyZ=nb.z;}
  }
  if(!target) ai.attackTimer=0;

  let currentThreshold=cfg.attackThreshold;
  if(cfg.attackWaveSizes){
    if(ai.waveIndex==null) ai.waveIndex=0;
    currentThreshold=cfg.attackWaveSizes[ai.waveIndex%cfg.attackWaveSizes.length];
  }
  const minAttackTime=difficulty==='hard'?(strategy==='rush'?60:120):cfg.attackInterval*0.4;
  const shouldAttack=target!=null&&readyArmy.length>=currentThreshold
    &&ai.attackTimer>=cfg.attackInterval&&gs.gameTime>=minAttackTime;

  if(shouldAttack){
    ai.isAttacking=true;ai.attackTimer=0;
    if(cfg.attackWaveSizes) ai.waveIndex=((ai.waveIndex||0)+1)%cfg.attackWaveSizes.length;
    const wave=readyArmy.slice(0,currentThreshold);
    gs.events.push({msg:`⚔ Enemy ${strategy==='rush'?'raid':'assault'}! ${wave.length} warriors!`,type:'bad'});

    const tx=target.x,tz=target.z;
    // Flanking: slightly rotate march direction each wave
    const flankAngle=(Math.random()-0.5)*0.6;
    const bDX=tx-bx,bDZ=tz-bz,bLen=Math.sqrt(bDX*bDX+bDZ*bDZ)||1;
    const cosA=Math.cos(flankAngle),sinA=Math.sin(flankAngle);
    const fDX=(bDX*cosA-bDZ*sinA)/bLen,fDZ=(bDX*sinA+bDZ*cosA)/bLen;
    const perpX=-fDZ,perpZ=fDX; // perpendicular for column spread

    let sharedWps=null;
    if(iW((bx+tx)/2,(bz+tz)/2)) sharedWps=_findWaterPath(bx,bz,tx,tz,heights,URES,VRES,MAP,HALF);

    const meleeIds=wave.filter(id=>MELEE_TYPES.has(units[id]?.type));
    const archerIds=wave.filter(id=>units[id]?.type==='Archer');
    const catIds=wave.filter(id=>units[id]?.type==='Catapult');
    const otherIds=wave.filter(id=>!meleeIds.includes(id)&&!archerIds.includes(id)&&!catIds.includes(id));

    function dispatch(u,destX,destZ,holdBack){
      if(!u||u.ownerId!==aiOwner) return;
      let ax=destX+(Math.random()-0.5)*10,az=destZ+(Math.random()-0.5)*10;
      if(holdBack>0){ax=destX-fDX*holdBack+(Math.random()-0.5)*5;az=destZ-fDZ*holdBack+(Math.random()-0.5)*5;}
      if(iW(ax,az)){ax=destX;az=destZ;}
      u.state='moving_to_attack';
      if(sharedWps&&sharedWps.length>0){
        u._waypoints=[...sharedWps.map(wp=>({...wp}))];
        u._waypoints[u._waypoints.length-1]={x:ax,z:az};
        u.tx=u._waypoints[0].x;u.tz=u._waypoints[0].z;
      } else {u._waypoints=null;u.tx=ax;u.tz=az;}
      u._pathLastPos={x:u.x,z:u.z};u._pathStuckTimer=0;
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
  if(ai.isAttacking&&!stillMarching){ai.isAttacking=false;ai.attackTimer=0;}

  // ── Patrol near base when idle ──────────────────────────────────────────
  if(!ai.isAttacking&&!baseUnderAttack){
    for(const id of readyArmy){
      const u=units[id];
      if(!u||u.state!=='idle'||u.ownerId!==aiOwner||u._headingToSmith||u._retreating||u.type==='Scout') continue;
      const pt=safePt(bx,bz,difficulty==='hard'?20:16);
      if(pt){u.tx=pt.x;u.tz=pt.z;u.state='moving';}
    }
  }
}

module.exports={tickAI};
