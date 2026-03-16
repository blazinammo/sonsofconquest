'use strict';
/**
 * ai.js — AI player logic for Age of Realms
 * easy / moderate / hard difficulties
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

const DIFF_CFG={
  easy:{
    maxVillagers:4, maxArmy:3,
    attackInterval:600, attackThreshold:4,
    buildInterval:45, trainInterval:20,
    researchEnabled:false, ageUpEnabled:false,
    buildQueue:['House','Farm','House','Farm','House'],
    trainTypes:['Swordsman'], gatherRadius:30, unitPreference:'random',
    detectionRange:8, // how close enemy must be to trigger auto-attack
  },
  moderate:{
    maxVillagers:8, maxArmy:12,
    attackInterval:300, attackThreshold:6,
    buildInterval:22, trainInterval:10,
    researchEnabled:true, ageUpEnabled:true,
    buildQueue:['House','Farm','Lumbercamp','Farm','House','MiningCamp',
                'House','Barracks','House','Tower','House','Farm'],
    trainTypes:['Swordsman','Archer','Scout'], gatherRadius:40, unitPreference:'random',
    researchList:['Iron Tools','Loom','Feudal Age','Horse Collar','Scale Armor'],
    detectionRange:12,
  },
  hard:{
    maxVillagers:13, maxArmy:35,
    attackInterval:180, attackWaveSizes:[5,15,20,30,35], attackThreshold:5,
    buildInterval:12, trainInterval:6,
    researchEnabled:true, ageUpEnabled:true,
    buildQueue:['House','Farm','Lumbercamp','Farm','House','MiningCamp','Farm',
                'House','Barracks','House','Tower','House','Barracks',
                'House','Farm','House','Castle'],
    trainTypes:['Swordsman','Archer','Knight','Scout'], gatherRadius:50, unitPreference:'strongest',
    researchList:['Iron Tools','Loom','Masonry','Feudal Age','Fletching',
                  'Scale Armor','Horse Collar','Castle Age','Chemistry','Plate Armor'],
    detectionRange:16,
  },
};

const COMBAT_TYPES=new Set(['Swordsman','Archer','Knight','Catapult','Scout']);

function tickAI(lobby, dt, teamNum, difficulty, ctx){
  const{uid,UDEFS,BCOSTS,BHPS,BSIZES,MAP,HALF,URES,VRES,pox,poz,aox,aoz}=ctx;
  const cfg=DIFF_CFG[difficulty]||DIFF_CFG.moderate;
  const{gs}=lobby;
  const{units,buildings,teams,resNodes,heights}=gs;
  const td=teams[teamNum];
  const enemyTeam=teamNum===1?2:1;
  const aiOwner='ai_team_'+teamNum;

  if(!lobby.aiState) lobby.aiState={};
  if(!lobby.aiState[teamNum]){
    lobby.aiState[teamNum]={
      buildTimer:cfg.buildInterval*0.3*Math.random(),
      attackTimer:0, trainTimer:0,
      researchTimer:cfg.buildInterval*2,
      buildIdx:0, army:[],
      isAttacking:false,
    };
  }
  const ai=lobby.aiState[teamNum];

  function iW(x,z){ return _isW(x,z,heights,URES,VRES,MAP,HALF); }
  function afford(cost){
    return(!cost.food||td.food>=cost.food)
        &&(!cost.wood||td.wood>=cost.wood)
        &&(!cost.gold||td.gold>=cost.gold)
        &&(!cost.stone||td.stone>=cost.stone);
  }
  function spend(cost){
    if(cost.food)td.food-=cost.food;
    if(cost.wood)td.wood-=cost.wood;
    if(cost.gold)td.gold-=cost.gold;
    if(cost.stone)td.stone-=cost.stone;
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
    for(let i=0;i<12;i++){
      const a=Math.random()*Math.PI*2, r=4+Math.random()*spread;
      const px=Math.max(-HALF+3,Math.min(HALF-3,cx+Math.cos(a)*r));
      const pz=Math.max(-HALF+3,Math.min(HALF-3,cz+Math.sin(a)*r));
      if(!iW(px,pz)) return{x:px,z:pz};
    }
    return null;
  }

  const aiTC=Object.values(buildings).find(b=>b.team===teamNum&&b.type==='Town Center'&&!b.dead);
  if(!aiTC) return;
  const bx=aiTC.x, bz=aiTC.z;

  // ══════════════════════════════════════════════════════════════════════════
  //  1. AUTO-ATTACK / DEFENSE — all AI military units react to nearby enemies
  // ══════════════════════════════════════════════════════════════════════════
  const detRange=cfg.detectionRange||12;
  for(const id in units){
    const u=units[id];
    if(u.dead||u.team!==teamNum||u.ownerId!==aiOwner) continue;
    if(!COMBAT_TYPES.has(u.type)) continue;
    // Don't interrupt active combat or wave attacks
    if(u.state==='attacking'||u.state==='attacking_building') continue;
    // Don't interrupt a wave march unless an enemy is very close
    const waveMarch=u.state==='moving_to_attack';
    const closeRange=waveMarch?3:detRange;

    // Find nearest enemy unit within detection range
    let nearestEnemy=null, nearestDist=closeRange;
    for(const oid in units){
      const o=units[oid];
      if(!o.dead&&o.team!==teamNum){
        const d=_dist2D(u.x,u.z,o.x,o.z);
        if(d<nearestDist){nearestDist=d;nearestEnemy=o;}
      }
    }
    if(nearestEnemy){
      u.target=nearestEnemy.id;
      u.state='attacking';
      continue;
    }
    // Also attack nearby enemy buildings when idle
    if(u.state==='idle'||u.state==='moving'){
      let nearBld=null, nearBldDist=detRange*0.6;
      for(const bid in buildings){
        const b=buildings[bid];
        if(!b.dead&&b.team!==teamNum){
          const d=_dist2D(u.x,u.z,b.x,b.z);
          if(d<nearBldDist){nearBldDist=d;nearBld=b;}
        }
      }
      if(nearBld){u.target=nearBld.id;u.state='attacking_building';}
    }
  }

  // ══════════════════════════════════════════════════════════════════════════
  //  2. ECONOMY — Villager gathering (spread across resource types)
  // ══════════════════════════════════════════════════════════════════════════
  const myVills=Object.values(units).filter(u=>!u.dead&&u.team===teamNum&&u.type==='Villager'&&u.ownerId===aiOwner);
  // Count how many villagers are already gathering each resource type
  const gatherCount={food:0,wood:0,gold:0,stone:0};
  for(const v of myVills){
    if(v.state==='moving_to_gather'||v.state==='gathering'||v.state==='returning'){
      const rn=resNodes.find(r=>r.id===v.gatherTarget);
      if(rn) gatherCount[rn.type]=(gatherCount[rn.type]||0)+1;
    }
  }
  // Priority: gold > food > wood > stone (economically optimal)
  const resPriority=['gold','food','wood','stone'];
  for(const v of myVills){
    if(v.state==='moving_to_build'||v.state==='building'||v.state==='moving_to_farm'||v.state==='farming') continue;
    if(v.state!=='idle') continue;
    // Find best resource: prefer under-staffed types
    const nodeList=ctx.resMap?[...ctx.resMap.values()]:resNodes;
    let best=null, bestScore=-Infinity;
    for(const rn of nodeList){
      if(rn.depleted||rn.amount<=0) continue;
      const d=_dist2D(v.x,v.z,rn.x,rn.z);
      if(d>cfg.gatherRadius) continue;
      // Score: closer + under-staffed type + preferred type
      const typeBonus=(resPriority.indexOf(rn.type)>=0?(4-resPriority.indexOf(rn.type))*2:0);
      const staffPenalty=(gatherCount[rn.type]||0)*3;
      const score=typeBonus-staffPenalty-(d*0.1);
      if(score>bestScore){bestScore=score;best=rn;}
    }
    if(best){
      v.gatherTarget=best.id; v.state='moving_to_gather';
      v.tx=best.x+(Math.random()-0.5)*1.5; v.tz=best.z+(Math.random()-0.5)*1.5;
      gatherCount[best.type]=(gatherCount[best.type]||0)+1;
    }
  }

  // ══════════════════════════════════════════════════════════════════════════
  //  3. ECONOMY — Train more villagers
  // ══════════════════════════════════════════════════════════════════════════
  if(myVills.length<cfg.maxVillagers&&td.population<td.maxPop-1){
    const vcost=UDEFS.Villager.cost;
    if(afford(vcost)&&!aiTC.productionQueue.length){spend(vcost);aiTC.productionQueue.push('Villager');}
  }

  // ══════════════════════════════════════════════════════════════════════════
  //  4. ECONOMY — Construct buildings
  // ══════════════════════════════════════════════════════════════════════════
  // Emergency: if at pop cap and can afford House, build one now
  if(td.population>=td.maxPop-2&&afford(BCOSTS.House||{wood:30})){
    const alreadyBuilding=Object.values(buildings).some(b=>b.team===teamNum&&b.type==='House'&&b.underConstruction);
    if(!alreadyBuilding){
      const pt=safePt(bx,bz,14);
      if(pt){
        spend(BCOSTS.House||{wood:30});
        const b=mkBld('House',pt.x,pt.z);
        buildings[b.id]=b; td.maxPop+=5;
      }
    }
  }

  ai.buildTimer+=dt;
  if(ai.buildTimer>=cfg.buildInterval&&ai.buildIdx<cfg.buildQueue.length){
    const bType=cfg.buildQueue[ai.buildIdx];
    const cost=BCOSTS[bType]||{};
    // Age-gated: skip (advance index) if age requirement not met yet
    if((bType==='Castle'&&td.age<2)||(bType==='Barracks'&&td.age<0)){
      ai.buildIdx++; ai.buildTimer=0;
    } else if(afford(cost)){
      const sz=BSIZES[bType.replace(' ','')]||1.5;
      let placed=false;
      for(let attempt=0;attempt<25&&!placed;attempt++){
        const a=Math.random()*Math.PI*2, r=6+Math.random()*16;
        const px=bx+Math.cos(a)*r, pz=bz+Math.sin(a)*r;
        if(Math.abs(px)>=HALF-4||Math.abs(pz)>=HALF-4||iW(px,pz)) continue;
        const blocked=Object.values(buildings).some(b=>!b.dead&&_dist2D(px,pz,b.x,b.z)<sz+(b.size||1.5)+0.8);
        if(blocked) continue;
        spend(cost);
        const b=mkBld(bType,px,pz);
        buildings[b.id]=b;
        if(bType==='House') td.maxPop+=5;
        gs.events.push({msg:`Enemy built ${bType}!`,type:'warn'});
        ai.buildIdx++; ai.buildTimer=0; placed=true;
      }
      if(!placed) ai.buildTimer=cfg.buildInterval*0.6;
    }
  }

  // ══════════════════════════════════════════════════════════════════════════
  //  5. MILITARY — Train soldiers
  // ══════════════════════════════════════════════════════════════════════════
  ai.trainTimer+=dt;
  if(ai.trainTimer>=cfg.trainInterval){
    ai.trainTimer=0;
    ai.army=ai.army.filter(id=>units[id]&&!units[id].dead);
    if(ai.army.length<cfg.maxArmy){
      const bars=Object.values(buildings).filter(b=>b.team===teamNum&&b.type==='Barracks'&&!b.dead&&!b.underConstruction);
      for(const bar of bars){
        if(bar.productionQueue.length>0) continue;
        const candidates=cfg.trainTypes.filter(t=>{
          const d=UDEFS[t]; if(!d) return false;
          if(t==='Knight'&&td.age<1) return false;
          if(t==='Catapult'&&td.age<2) return false;
          return afford(d.cost)&&td.population+(d.pop||1)<=td.maxPop;
        });
        if(!candidates.length) continue;
        let pick;
        if(cfg.unitPreference==='strongest'){
          const priority=['Knight','Catapult','Archer','Swordsman','Scout'];
          pick=priority.find(t=>candidates.includes(t))||candidates[0];
        } else {
          pick=candidates[Math.floor(Math.random()*candidates.length)];
        }
        spend(UDEFS[pick].cost);
        bar.productionQueue.push(pick);
        break;
      }
    }
  }

  // Absorb all combat units (including Scout) into army list
  for(const u of Object.values(units)){
    if(!u.dead&&u.team===teamNum&&u.ownerId===aiOwner&&COMBAT_TYPES.has(u.type)&&!ai.army.includes(u.id)){
      ai.army.push(u.id);
    }
  }

  // ══════════════════════════════════════════════════════════════════════════
  //  6. RESEARCH
  // ══════════════════════════════════════════════════════════════════════════
  if(cfg.researchEnabled){
    ai.researchTimer+=dt;
    if(ai.researchTimer>=cfg.buildInterval*2.5){
      ai.researchTimer=0;
      for(const techId of cfg.researchList){
        if(td.researched.includes(techId)) continue;
        if(td.age<(TECH_AGE[techId]||0)) continue;
        const cost=TECH_COSTS[techId]||{};
        if(!afford(cost)) continue;
        spend(cost); td.researched.push(techId);
        if(techId==='Feudal Age'){td.age=1;gs.events.push({msg:'Enemy advances to Feudal Age!',type:'warn'});}
        if(techId==='Castle Age'){td.age=2;gs.events.push({msg:'Enemy advances to Castle Age!',type:'warn'});}
        if(techId==='Loom') for(const u of Object.values(units)) if(u.team===teamNum&&u.type==='Villager'){u.maxHp+=40;u.hp=Math.min(u.hp+40,u.maxHp);}
        if(techId==='Masonry') for(const b of Object.values(buildings)) if(b.team===teamNum){const newMax=Math.floor(b.maxHp*1.2);b.hp=Math.min(newMax,Math.floor(b.hp*(newMax/b.maxHp)));b.maxHp=newMax;}
        if(techId==='Scale Armor') for(const u of Object.values(units)) if(u.team===teamNum) u.def+=2;
        if(techId==='Plate Armor') for(const u of Object.values(units)) if(u.team===teamNum) u.def+=4;
        gs.events.push({msg:`Enemy researched ${techId}!`,type:'warn'});
        break;
      }
    }
  }

  // ══════════════════════════════════════════════════════════════════════════
  //  7. SCOUTING — discover enemy base location
  // ══════════════════════════════════════════════════════════════════════════
  // Check if any AI unit can see an enemy building
  if(ai.knownEnemyX===undefined){
    outer: for(const id in units){
      const u=units[id];
      if(!u.dead&&u.team===teamNum&&u.ownerId===aiOwner){
        for(const bid in buildings){
          const b=buildings[bid];
          if(!b.dead&&b.team===enemyTeam&&_dist2D(u.x,u.z,b.x,b.z)<(u.vision||12)){
            ai.knownEnemyX=b.x; ai.knownEnemyZ=b.z;
            gs.events.push({msg:'Enemy base located!',type:'warn'});
            break outer;
          }
        }
      }
    }
  } else {
    // Keep known position fresh
    for(const bid in buildings){
      const b=buildings[bid];
      if(!b.dead&&b.team===enemyTeam&&b.type==='Town Center'){ai.knownEnemyX=b.x;ai.knownEnemyZ=b.z;break;}
    }
  }

  // Scout movement — only direct the scout when it's not already in combat
  const myScout=Object.values(units).find(u=>!u.dead&&u.team===teamNum&&u.ownerId===aiOwner&&u.type==='Scout')
    ||Object.values(units).find(u=>!u.dead&&u.team===teamNum&&u.ownerId===aiOwner&&u.type!=='Villager'&&(u.state==='idle'||u.state==='moving'));

  if(ai.knownEnemyX===undefined&&myScout&&myScout.ownerId===aiOwner
     &&myScout.state!=='attacking'&&myScout.state!=='attacking_building'){
    if(!ai.scoutLastPos){ai.scoutLastPos={x:myScout.x,z:myScout.z};ai.scoutStuckTimer=0;}
    const moved=_dist2D(myScout.x,myScout.z,ai.scoutLastPos.x,ai.scoutLastPos.z);
    if(moved>=0.5){ai.scoutLastPos={x:myScout.x,z:myScout.z};ai.scoutStuckTimer=0;}
    else ai.scoutStuckTimer=(ai.scoutStuckTimer||0)+dt;
    const stuck=myScout.state==='moving'&&ai.scoutStuckTimer>=5;
    const needsWpt=myScout.state==='idle'||stuck
      ||(myScout.state==='moving'&&_dist2D(myScout.x,myScout.z,ai.scoutTarget?.x||myScout.x,ai.scoutTarget?.z||myScout.z)<3);
    if(needsWpt){
      if(stuck) ai.scoutStuckTimer=0;
      const ex=aox!==undefined?(teamNum===1?aox:pox):0;
      const ez=aoz!==undefined?(teamNum===1?aoz:poz):0;
      let sx=myScout.x,sz=myScout.z,picked=false;
      for(let i=0;i<16&&!picked;i++){
        const spread=(Math.random()-0.5)*(0.8+i*0.15);
        const angle=Math.atan2(ez-bz,ex-bx)+spread;
        const dist=15+Math.random()*35;
        let cx=Math.max(-HALF+4,Math.min(HALF-4,myScout.x+Math.cos(angle)*dist));
        let cz=Math.max(-HALF+4,Math.min(HALF-4,myScout.z+Math.sin(angle)*dist));
        if(iW(cx,cz)) continue;
        if(ai.scoutTarget&&_dist2D(cx,cz,ai.scoutTarget.x,ai.scoutTarget.z)<8) continue;
        sx=cx;sz=cz;picked=true;
      }
      if(!picked){sx=ex+(Math.random()-0.5)*10;sz=ez+(Math.random()-0.5)*10;}
      myScout.tx=sx;myScout.tz=sz;myScout.state='moving';
      ai.scoutTarget={x:sx,z:sz};ai.scoutLastPos={x:myScout.x,z:myScout.z};
    }
  } else if(ai.knownEnemyX!==undefined){
    ai.scoutLastPos=undefined;ai.scoutStuckTimer=0;
  }

  // ══════════════════════════════════════════════════════════════════════════
  //  8. BASE DEFENSE — rush nearby units to defend when enemy attacks base
  // ══════════════════════════════════════════════════════════════════════════
  // If any enemy unit gets within defense radius of our TC, send all idle army to intercept
  const DEFENSE_RADIUS=20;
  let baseUnderAttack=false;
  for(const id in units){
    const u=units[id];
    if(!u.dead&&u.team!==teamNum&&_dist2D(u.x,u.z,bx,bz)<DEFENSE_RADIUS){baseUnderAttack=true;break;}
  }
  if(baseUnderAttack){
    for(const id of ai.army){
      const u=units[id];
      if(!u||u.dead||u.ownerId!==aiOwner) continue;
      if(u.state==='attacking'||u.state==='attacking_building') continue;
      // Find closest enemy near base to intercept
      let closest=null,cd=DEFENSE_RADIUS*1.5;
      for(const oid in units){
        const o=units[oid];
        if(!o.dead&&o.team!==teamNum){const d=_dist2D(bx,bz,o.x,o.z);if(d<cd){cd=d;closest=o;}}
      }
      if(closest){u.target=closest.id;u.state='attacking';}
    }
  }

  // ══════════════════════════════════════════════════════════════════════════
  //  9. ATTACK WAVES — march on enemy base once located
  // ══════════════════════════════════════════════════════════════════════════
  ai.attackTimer+=dt;
  const readyArmy=ai.army.filter(id=>units[id]&&!units[id].dead);

  let target=null;
  if(ai.knownEnemyX!==undefined){
    const nearbyBld=Object.values(buildings).find(b=>!b.dead&&b.team===enemyTeam&&_dist2D(b.x,b.z,ai.knownEnemyX,ai.knownEnemyZ)<30);
    target=nearbyBld||{x:ai.knownEnemyX,z:ai.knownEnemyZ};
    if(nearbyBld){ai.knownEnemyX=nearbyBld.x;ai.knownEnemyZ=nearbyBld.z;}
  }
  if(!target) ai.attackTimer=0;

  let currentThreshold=cfg.attackThreshold;
  if(cfg.attackWaveSizes){
    if(ai.waveIndex==null) ai.waveIndex=0;
    currentThreshold=cfg.attackWaveSizes[ai.waveIndex%cfg.attackWaveSizes.length];
  }
  const shouldAttack=target!=null&&readyArmy.length>=currentThreshold
    &&ai.attackTimer>=cfg.attackInterval&&gs.gameTime>=cfg.attackInterval*0.4;

  if(shouldAttack){
    ai.isAttacking=true; ai.attackTimer=0;
    if(cfg.attackWaveSizes) ai.waveIndex=((ai.waveIndex||0)+1)%cfg.attackWaveSizes.length;
    const wave=readyArmy.slice(0,currentThreshold);
    gs.events.push({msg:`⚔ Enemy assault! ${wave.length} warriors marching!`,type:'bad'});
    const tx=target.x,tz=target.z;
    for(const id of wave){
      const u=units[id];
      if(!u||u.ownerId!==aiOwner) continue;
      let ax=tx+(Math.random()-0.5)*10,az=tz+(Math.random()-0.5)*10;
      if(iW(ax,az)){ax=tx;az=tz;}
      u.tx=ax;u.tz=az;u.state='moving_to_attack';
    }
  }

  // Prune and reset attack state
  ai.army=ai.army.filter(id=>units[id]&&!units[id].dead);
  const stillMarching=ai.army.some(id=>{const u=units[id];return u&&(u.state==='moving_to_attack'||u.state==='attacking'||u.state==='attacking_building');});
  if(ai.isAttacking&&!stillMarching){ai.isAttacking=false;ai.attackTimer=0;}

  // ── Patrol near base (non-attacking, non-scouting idle units) ──
  if(!ai.isAttacking&&!baseUnderAttack){
    for(const id of readyArmy){
      const u=units[id];
      if(!u||u.state!=='idle'||u.ownerId!==aiOwner) continue;
      if(u.type==='Scout'&&ai.knownEnemyX===undefined) continue; // scout is scouting
      const pt=safePt(bx,bz,16);
      if(pt){u.tx=pt.x;u.tz=pt.z;u.state='moving';}
    }
  }
}

module.exports={tickAI};
