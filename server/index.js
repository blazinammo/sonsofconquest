const express = require('express');
const { createServer } = require('http');
const { Server } = require('socket.io');
const path = require('path');
const { v4: uuidv4 } = require('uuid');
const { tickAI: tickAIPlayer } = require('./ai');

const app = express();
const httpServer = createServer(app);
const io = new Server(httpServer, { cors: { origin: '*' } });
app.use(express.static(path.join(__dirname, '../public')));

const MAP = 150, HALF = 75, TICK = 150;
const URES = 90, VRES = 90;

function uid() { return uuidv4().slice(0,8); }
function dist2D(ax,az,bx,bz) { return Math.sqrt((ax-bx)**2+(az-bz)**2); }

// noise with per-call phase offsets for full randomisation
function noise(x,z,s,a,ox=0,oz=0) {
  return Math.sin((x+ox)*s)*Math.cos((z+oz)*s*0.7)*a
       + Math.sin((x+ox)*s*2.1+0.5)*Math.cos((z+oz)*s*1.8)*a*0.4
       + Math.sin((x+ox)*s*4.3-1.2)*Math.cos((z+oz)*s*3.9+0.8)*a*0.15;
}
function noiseH(x,z,pox,poz,aox,aoz,seeds) {
  // Three octaves with random offsets, plus a large-scale basin layer
  const raw = noise(x,z,0.05,3.5,  seeds.o1x,seeds.o1z)
            + noise(x,z,0.12,1.2,  seeds.o2x,seeds.o2z)
            + noise(x,z,0.25,0.4,  seeds.o3x,seeds.o3z)
            + noise(x,z,0.018,seeds.basinAmp, seeds.o4x,seeds.o4z);
  // Flatten terrain near each spawn so bases are always playable
  const pd=Math.sqrt((x-pox)**2+(z-poz)**2), pf=1-Math.min(1,Math.max(0,(pd-12)/7));
  const ed=Math.sqrt((x-aox)**2+(z-aoz)**2), ef=1-Math.min(1,Math.max(0,(ed-12)/7));
  // Shift all heights by waterBias: negative = more water, positive = more land
  return raw*(1-Math.max(pf,ef)) + seeds.waterBias;
}
function makeSeeds() {
  // waterBias chosen from a weighted set so each map feels distinct:
  // ~30% mostly-land (bias +1.5..+2.5), ~40% moderate (0..+1), ~30% wet (-1..0)
  const r=Math.random();
  const waterBias = r<0.30 ? 1.5+Math.random()*1.0
                  : r<0.70 ? Math.random()*1.0
                  :          -1.0+Math.random()*1.0;
  // Large-scale basin amplitude — high values create big ocean basins
  const basinAmp = 1.5+Math.random()*3.5;
  const R=()=>(Math.random()-0.5)*400;
  return{o1x:R(),o1z:R(),o2x:R(),o2z:R(),o3x:R(),o3z:R(),o4x:R(),o4z:R(),basinAmp,waterBias};
}
function buildHeights(pox,poz,aox,aoz,seeds) {
  const h=new Array((URES+1)*(VRES+1));
  for (let r=0;r<=VRES;r++) for (let c=0;c<=URES;c++) {
    h[r*(URES+1)+c]=noiseH(-HALF+c/URES*MAP, -(HALF-r/VRES*MAP), pox,poz,aox,aoz,seeds);
  }
  return h;
}

// BFS on the height grid — returns true if a land path exists between two world positions.
// Uses 4-connected grid at the URES×VRES resolution with a small step size.
function landPathExists(wx1,wz1,wx2,wz2,h) {
  // Convert world coords to grid cells
  function toCell(wx,wz){
    return [Math.round((wx+HALF)/MAP*URES), Math.round((wz+HALF)/MAP*VRES)];
  }
  const [sc,sr]=toCell(wx1,wz1);
  const [ec,er]=toCell(wx2,wz2);
  const visited=new Uint8Array((URES+1)*(VRES+1));
  const queue=[[sc,sr]];
  visited[sr*(URES+1)+sc]=1;
  while(queue.length){
    const [c,r]=queue.shift();
    if(c===ec&&r===er) return true;
    for(const [dc,dr] of [[1,0],[-1,0],[0,1],[0,-1]]){
      const nc=c+dc, nr=r+dr;
      if(nc<0||nc>URES||nr<0||nr>VRES) continue;
      const idx=nr*(URES+1)+nc;
      if(visited[idx]) continue;
      visited[idx]=1;
      // Use grid cell centre world position for water check
      const wx=-HALF+nc/URES*MAP, wz=-(HALF-nr/VRES*MAP);
      if(!isW(wx,wz,h)) queue.push([nc,nr]);
    }
  }
  return false;
}
function getH(wx,wz,h) {
  const cx=Math.max(-HALF,Math.min(HALF-0.001,wx)), cz=Math.max(-HALF,Math.min(HALF-0.001,wz));
  const gx=(cx+HALF)/MAP*URES, gz=(cz+HALF)/MAP*VRES;
  const c0=Math.floor(gx),c1=Math.min(c0+1,URES), r0=Math.floor(gz),r1=Math.min(r0+1,VRES);
  const fx=gx-c0,fz=gz-r0;
  return h[r0*(URES+1)+c0]*(1-fx)*(1-fz)+h[r0*(URES+1)+c1]*fx*(1-fz)+h[r1*(URES+1)+c0]*(1-fx)*fz+h[r1*(URES+1)+c1]*fx*fz;
}
function isW(wx,wz,h) { return getH(wx,wz,h)<-1.3; }
function randAround(cx,cz,r0,r1,h,tries=80) {
  for (let i=0;i<tries;i++) {
    const a=Math.random()*Math.PI*2, r=r0+Math.random()*(r1-r0);
    const x=cx+Math.cos(a)*r, z=cz+Math.sin(a)*r;
    if (Math.abs(x)<HALF-3&&Math.abs(z)<HALF-3&&!isW(x,z,h)) return [x,z];
  }
  return [cx+r0,cz];
}

const UDEFS = {
  Villager: {hp:25,maxHp:25,atk:3,def:0,spd:0.040,rng:0.9,cost:{food:50},trainTime:5,pop:1,vision:18},
  Swordsman:{hp:70,maxHp:70,atk:14,def:4,spd:0.033,rng:1.3,cost:{food:60,gold:20},trainTime:9,pop:1,vision:16},
  Archer:   {hp:40,maxHp:40,atk:9,def:1,spd:0.038,rng:7.0,cost:{wood:25,gold:45},trainTime:8,pop:1,vision:22},
  Knight:   {hp:130,maxHp:130,atk:20,def:6,spd:0.052,rng:1.5,cost:{food:60,gold:75},trainTime:13,pop:2,vision:22},
  Catapult: {hp:90,maxHp:90,atk:40,def:1,spd:0.016,rng:11.0,cost:{wood:200,gold:100},trainTime:20,pop:3,vision:16},
  Scout:    {hp:55,maxHp:55,atk:5,def:1,spd:0.085,rng:1.2,cost:{food:80},trainTime:7,pop:1,vision:38},
};
const BCOSTS={House:{wood:30},Barracks:{wood:175},Farm:{wood:60},Blacksmith:{wood:100,stone:50},Tower:{stone:125},MiningCamp:{wood:100},Lumbercamp:{wood:100},Castle:{stone:650},Market:{wood:175}};
const BBUILD_TIME={House:20,Farm:20,Blacksmith:20,MiningCamp:20,Lumbercamp:20,Market:20,Tower:60,Barracks:40,Castle:120};
const BHPS={TownCenter:2400,Barracks:1000,House:350,Farm:240,Tower:1800,Blacksmith:700,Lumbercamp:400,MiningCamp:400,Castle:6000,Market:500};
const BSIZES={TownCenter:3.5,Barracks:2.5,House:1.5,Farm:2.0,Tower:1.2,Blacksmith:1.8,Lumbercamp:1.8,MiningCamp:1.8,Castle:5.0,Market:2.2};
const TECHS=[
  {id:'Iron Tools',cost:{food:100,gold:50},age:0},{id:'Town Watch',cost:{food:75},age:0},
  {id:'Loom',cost:{gold:50},age:0},{id:'Masonry',cost:{stone:100},age:0},
  {id:'Feudal Age',cost:{food:500},age:0},{id:'Fletching',cost:{food:100,wood:50},age:1},
  {id:'Scale Armor',cost:{food:100,gold:50},age:1},{id:'Horse Collar',cost:{food:75,wood:75},age:1},
  {id:'Castle Age',cost:{food:800,gold:200},age:1},{id:'Chemistry',cost:{food:300,gold:200},age:2},
  {id:'Plate Armor',cost:{gold:300},age:2},{id:'Imperial Age',cost:{food:1500,gold:500},age:2},
];

function afford(t,c){return(!c.food||t.food>=c.food)&&(!c.wood||t.wood>=c.wood)&&(!c.gold||t.gold>=c.gold)&&(!c.stone||t.stone>=c.stone);}
function spend(t,c){if(c.food)t.food-=c.food;if(c.wood)t.wood-=c.wood;if(c.gold)t.gold-=c.gold;if(c.stone)t.stone-=c.stone;}

function mkTeam(){return{food:200,wood:200,gold:100,stone:100,maxPop:10,population:0,score:0,age:0,researched:[]};}
function mkBuilding(type,x,z,team,ownerId,underConstruction=false){
  const key=type.replace(' ','');
  const maxHp=BHPS[key]||400;
  const buildTime=BBUILD_TIME[key]||20;
  return{id:uid(),type,x,z,team,ownerId:ownerId||('team'+team),
    hp:underConstruction?1:maxHp,maxHp,size:BSIZES[key]||1.5,
    productionQueue:[],productionTimer:0,dead:false,atkTimer:0,
    underConstruction,buildProgress:0,buildTime};
}
function mkUnit(type,x,z,team,ownerId){
  const d=UDEFS[type]||UDEFS.Villager;
  return{id:uid(),type,x,z,team,ownerId,hp:d.hp,maxHp:d.maxHp,atk:d.atk,def:d.def,spd:d.spd,rng:d.rng,vision:d.vision||7,tx:x,tz:z,state:'idle',target:null,gatherTarget:null,returnTC:null,carry:{food:0,wood:0,gold:0,stone:0},atkTimer:0,gatherTimer:0,dead:false,pop:d.pop||1};
}

function generateMap(pox,poz,aox,aoz){
  let seeds=makeSeeds();
  let h=buildHeights(pox,poz,aox,aoz,seeds);
  // Guarantee a land path between bases — nudge waterBias up until one exists
  let pathAttempts=0;
  while(!landPathExists(pox,poz,aox,aoz,h)&&pathAttempts<30){
    seeds={...seeds,waterBias:seeds.waterBias+0.15};
    h=buildHeights(pox,poz,aox,aoz,seeds);
    pathAttempts++;
  }
  if(pathAttempts>0) console.log(`[map] Raised waterBias ${pathAttempts}x to ensure land path (final bias: ${seeds.waterBias.toFixed(2)})`);
  const rn=[];
  const SAFE_R=14;
  function addR(type,x,z,extra={}){
    const amount=type==='gold'?400+Math.random()*400:type==='stone'?600+Math.random()*400:type==='wood'?300+Math.random()*300:200+Math.random()*200;
    rn.push({id:uid(),type,x,z,amount,maxAmount:amount,depleted:false,...extra});
  }
  // Named deposits near bases
  for(const[bx,bz]of[[pox,poz],[aox,aoz]]){
    // 3 gold + 3 food near each base (1.5× original 2)
    addR('gold',...randAround(bx,bz,7,16,h));addR('gold',...randAround(bx,bz,7,16,h));addR('gold',...randAround(bx,bz,12,20,h));
    addR('food',...randAround(bx,bz,6,14,h));addR('food',...randAround(bx,bz,6,14,h));addR('food',...randAround(bx,bz,10,18,h));
    // 15 trees near each base (1.5× original 10)
    for(let i=0;i<15;i++){const[tx,tz]=randAround(bx,bz,9,22,h);addR('wood',tx,tz,{isTree:true,variety:Math.random()<0.35?1:0});}
  }
  // Scattered deposits — all 1.5× original counts
  for(let i=0;i<12;i++){const x=(Math.random()-0.5)*MAP*0.85,z=(Math.random()-0.5)*MAP*0.85;if(!isW(x,z,h)&&dist2D(x,z,pox,poz)>14&&dist2D(x,z,aox,aoz)>14)addR('gold',x,z);}
  for(let i=0;i<15;i++){const x=(Math.random()-0.5)*MAP*0.85,z=(Math.random()-0.5)*MAP*0.85;if(!isW(x,z,h))addR('stone',x,z);}
  for(let i=0;i<18;i++){const x=(Math.random()-0.5)*MAP*0.85,z=(Math.random()-0.5)*MAP*0.85;if(!isW(x,z,h))addR('food',x,z);}
  // Trees across the map — 195 total (1.5× original 130)
  let attempts=0;
  while(rn.filter(r=>r.isTree).length<195&&attempts<4000){
    attempts++;
    const x=(Math.random()-0.5)*MAP*0.92,z=(Math.random()-0.5)*MAP*0.92;
    if(isW(x,z,h))continue;
    if(rn.some(r=>r.isTree&&dist2D(r.x,r.z,x,z)<2.0))continue;
    addR('wood',x,z,{isTree:true,variety:Math.random()<0.3?1:0});
  }
  return{heights:h,resNodes:rn,seeds};
}

function createLobby(name,hostId){
  const id=uuidv4().slice(0,6).toUpperCase();
  const a1=Math.random()*Math.PI*2, a2=a1+Math.PI+(Math.random()-0.5)*0.4, R=45;
  const pox=Math.round(Math.cos(a1)*R),poz=Math.round(Math.sin(a1)*R);
  const aox=Math.round(Math.cos(a2)*R),aoz=Math.round(Math.sin(a2)*R);
  const{heights,resNodes}=generateMap(pox,poz,aox,aoz);
  const teams={1:mkTeam(),2:mkTeam()};
  const units={},buildings={};

  function sb(type,x,z,team,ownerId){const b=mkBuilding(type,x,z,team,ownerId||('team'+team));buildings[b.id]=b;if(type==='House')teams[team].maxPop+=5;return b;}
  const tc1=sb('Town Center',pox,poz,1);sb('House',pox-8,poz-4,1);sb('House',pox-8,poz+4,1);sb('Lumbercamp',pox+6,poz-6,1);
  const tc2=sb('Town Center',aox,aoz,2);sb('House',aox+8,aoz-4,2);sb('House',aox+8,aoz+4,2);

  function su(type,x,z,team,owner){const u=mkUnit(type,x,z,team,owner);units[u.id]=u;teams[team].population+=u.pop;return u;}
  su('Villager',pox-3,poz-3,1,'team1');su('Villager',pox-3,poz,1,'team1');su('Villager',pox-3,poz+3,1,'team1');su('Scout',pox+3,poz,1,'team1');
  su('Villager',aox-4,aoz-3,2,'team2');su('Villager',aox-4,aoz,2,'team2');su('Villager',aox-4,aoz+3,2,'team2');su('Scout',aox+3,aoz,2,'team2');

  return{id,name,hostId,status:'waiting',players:{},aiPlayers:{},
    gs:{units,buildings,teams,resNodes,heights,pox,poz,aox,aoz,gameTime:0,tc1:tc1.id,tc2:tc2.id,events:[],projPool:[],incomeTimer:0},
    aiState:{},
    tickInterval:null};
}

function gameTick(lobby){
  const{gs}=lobby, dt=TICK/1000;
  const{units,buildings,teams,resNodes,heights}=gs;
  gs.gameTime+=dt;

  function iW(x,z){return isW(x,z,heights);}
  function gH(x,z){return getH(x,z,heights);}

  function moveU(u,tx,tz){
    const dx=tx-u.x,dz=tz-u.z,d=Math.sqrt(dx*dx+dz*dz);
    if(d<0.15)return true;
    const step=Math.min(u.spd*60*dt,d);
    let nx=u.x+(dx/d)*step,nz=u.z+(dz/d)*step;
    if(iW(nx,nz)){let mv=false;const ba=Math.atan2(dx,dz);for(let i=1;i<=8&&!mv;i++)for(const s of[1,-1]){const a=ba+s*i*(Math.PI/8),cx=u.x+Math.sin(a)*step,cz=u.z+Math.cos(a)*step;if(!iW(cx,cz)){nx=cx;nz=cz;mv=true;break;}}if(!mv)return false;}
    u.x=nx;u.z=nz;return false;
  }

  // ─ Unit ticks ─
  for(const id in units){
    const u=units[id];if(u.dead)continue;
    u.atkTimer=Math.max(0,u.atkTimer-dt);

    // auto-attack
    if((u.state==='idle'||u.state==='attack_move')&&u.atkTimer<=0&&!u.target){
      let best=null,bd=u.rng+6;
      for(const oid in units){const o=units[oid];if(!o.dead&&o.team!==u.team){const d=dist2D(u.x,u.z,o.x,o.z);if(d<bd){bd=d;best=o;}}}
      if(!best)for(const bid in buildings){const b=buildings[bid];if(!b.dead&&b.team!==u.team){const d=dist2D(u.x,u.z,b.x,b.z);if(d<bd){bd=d;u.state='attacking_building';u.target=bid;}}}
      if(best&&!u.target){u.target=best.id;if(u.state==='idle')u.state='attacking';}
    }

    switch(u.state){
      case 'moving':case 'attack_move':if(moveU(u,u.tx,u.tz))u.state='idle';break;
      case 'moving_to_attack':{
        moveU(u,u.tx,u.tz);
        for(const oid in units){const o=units[oid];if(!o.dead&&o.team!==u.team&&dist2D(u.x,u.z,o.x,o.z)<8){u.target=oid;u.state='attacking';break;}}
        break;
      }
      case 'attacking':{
        if(!u.target||!units[u.target]||units[u.target].dead){u.target=null;u.state='idle';break;}
        const t=units[u.target],d=dist2D(u.x,u.z,t.x,t.z);
        if(d>u.rng)moveU(u,t.x,t.z);
        else if(u.atkTimer<=0){
          const dmg=Math.max(1,u.atk-(t.def||0));t.hp-=dmg;u.atkTimer=1.2+Math.random()*0.4;
          if(u.rng>2)gs.projPool.push({id:uid(),fx:u.x,fy:gH(u.x,u.z)+1.5,fz:u.z,tx:t.x,ty:gH(t.x,t.z)+1,tz:t.z,color:u.type==='Catapult'?0xff6600:0xd8d8b0,life:1.8,maxLife:1.8});
          if(t.hp<=0){t.dead=true;teams[t.team].population-=(t.pop||1);teams[u.team].score+=10+(UDEFS[t.type]?.cost?.gold||0);gs.events.push({msg:`${t.type} killed`,type:'combat',team:u.team});u.target=null;u.state='idle';}
        }
        break;
      }
      case 'attacking_building':{
        if(!u.target||!buildings[u.target]||buildings[u.target].dead){u.target=null;u.state='idle';break;}
        const b=buildings[u.target],d=dist2D(u.x,u.z,b.x,b.z);
        if(d>u.rng+b.size)moveU(u,b.x,b.z);
        else if(u.atkTimer<=0){
          b.hp-=Math.max(1,u.atk-1);u.atkTimer=1.5;
          if(u.rng>2)gs.projPool.push({id:uid(),fx:u.x,fy:gH(u.x,u.z)+1.5,fz:u.z,tx:b.x,ty:gH(b.x,b.z)+1,tz:b.z,color:u.type==='Catapult'?0xff6600:0xd8d8b0,life:1.5,maxLife:1.5});
          if(b.hp<=0){b.dead=true;if(b.type==='House')teams[b.team].maxPop-=5;gs.events.push({msg:`${b.team===1?'Blue':'Red'} ${b.type} destroyed!`,type:b.team===u.team?'good':'bad'});u.target=null;u.state='idle';}
        }
        break;
      }
      case 'moving_to_build':{
        const bsite=buildings[u.buildTarget];
        if(!bsite||bsite.dead||!bsite.underConstruction){u.state='idle';u.buildTarget=null;break;}
        const arrived=moveU(u,u.tx,u.tz)||dist2D(u.x,u.z,bsite.x,bsite.z)<bsite.size+1.2;
        if(arrived){u.state='building';}
        break;
      }
      case 'building':{
        const bsite=buildings[u.buildTarget];
        if(!bsite||bsite.dead){u.state='idle';u.buildTarget=null;break;}
        if(!bsite.underConstruction){u.state='idle';u.buildTarget=null;break;}
        // Stay close to the building site; drift back if wandered
        if(dist2D(u.x,u.z,bsite.x,bsite.z)>bsite.size+2){u.state='moving_to_build';u.tx=bsite.x+(Math.random()-0.5)*bsite.size;u.tz=bsite.z+(Math.random()-0.5)*bsite.size;}
        break;
      }
      case 'moving_to_gather':{
        const rn=gs.resNodes.find(r=>r.id===u.gatherTarget);
        if(!rn||rn.depleted){u.state='idle';break;}
        if(moveU(u,rn.x,rn.z)||dist2D(u.x,u.z,rn.x,rn.z)<1.5)u.state='gathering';
        break;
      }
      case 'gathering':{
        const rn=gs.resNodes.find(r=>r.id===u.gatherTarget);
        if(!rn||rn.depleted||rn.amount<=0){u.state='idle';break;}
        u.gatherTimer-=dt;
        if(u.gatherTimer<=0){
          const rate=(teams[u.team].researched||[]).includes('Iron Tools')?7:5;
          const amt=Math.min(rate,rn.amount);rn.amount-=amt;u.carry[rn.type]=(u.carry[rn.type]||0)+amt;u.gatherTimer=1.0;
          if(rn.amount<=0)rn.depleted=true;
          if(Object.values(u.carry).reduce((a,b)=>a+b,0)>=25){
            let nearTC=null,nearD=999;
            for(const bid in buildings){const b=buildings[bid];if(!b.dead&&b.team===u.team&&b.type==='Town Center'){const d=dist2D(u.x,u.z,b.x,b.z);if(d<nearD){nearD=d;nearTC=b;}}}
            if(nearTC){u.state='returning';u.tx=nearTC.x;u.tz=nearTC.z;u.returnTC=nearTC.id;}
          }
        }
        break;
      }
      case 'returning':{
        const tc=buildings[u.returnTC];if(!tc||tc.dead){u.state='idle';break;}
        if(moveU(u,tc.x,tc.z)||dist2D(u.x,u.z,tc.x,tc.z)<3.5){
          const t=teams[u.team];
          for(const[res,amt]of Object.entries(u.carry)){t[res]=(t[res]||0)+amt;}
          gs.events.push({type:'gather',team:u.team,carry:{...u.carry}});
          u.carry={food:0,wood:0,gold:0,stone:0};
          const rn=gs.resNodes.find(r=>r.id===u.gatherTarget);
          if(rn&&!rn.depleted){u.state='moving_to_gather';u.tx=rn.x;u.tz=rn.z;}else u.state='idle';
        }
        break;
      }
    }
  }

  // ─ Unit separation (prevent stacking) ─
  const MIN_SEP=0.85; // minimum centre-to-centre distance in world units
  const PUSH=0.18;    // fraction of overlap to resolve per tick
  const uArr=Object.values(units).filter(u=>!u.dead);
  for(let i=0;i<uArr.length;i++){
    const a=uArr[i];
    for(let j=i+1;j<uArr.length;j++){
      const b=uArr[j];
      const dx=a.x-b.x,dz=a.z-b.z;
      const d2=dx*dx+dz*dz;
      if(d2>=MIN_SEP*MIN_SEP||d2===0)continue;
      const d=Math.sqrt(d2);
      const overlap=(MIN_SEP-d)*PUSH;
      const nx=dx/d,nz=dz/d;
      // Moving units yield more readily; idle/gathering units get pushed harder
      const aMoving=(a.state==='moving'||a.state==='attacking'||a.state==='moving_to_attack');
      const bMoving=(b.state==='moving'||b.state==='attacking'||b.state==='moving_to_attack');
      const aShare=bMoving?0.35:0.65;
      const bShare=aMoving?0.35:0.65;
      const ax2=a.x+nx*overlap*aShare, az2=a.z+nz*overlap*aShare;
      const bx2=b.x-nx*overlap*bShare, bz2=b.z-nz*overlap*bShare;
      if(!iW(ax2,az2)){a.x=ax2;a.z=az2;}
      if(!iW(bx2,bz2)){b.x=bx2;b.z=bz2;}
    }
  }

  // ─ Tower autofire ─
  for(const bid in buildings){
    const b=buildings[bid];if(b.dead||b.type!=='Tower'||b.underConstruction)continue;
    b.atkTimer-=dt;if(b.atkTimer>0)continue;
    for(const tuid in units){const u=units[tuid];if(!u.dead&&u.team!==b.team&&dist2D(b.x,b.z,u.x,u.z)<9){u.hp-=12;gs.projPool.push({id:uid(),fx:b.x,fy:gH(b.x,b.z)+5.5,fz:b.z,tx:u.x,ty:gH(u.x,u.z)+1,tz:u.z,color:0xffe070,life:1.2,maxLife:1.2});if(u.hp<=0){u.dead=true;teams[u.team].population-=(u.pop||1);}b.atkTimer=2.5;break;}}
    if(b.atkTimer<=0)b.atkTimer=0.5;
  }

  // ─ Castle autofire (50% more damage, 30% longer range than Tower) ─
  for(const bid in buildings){
    const b=buildings[bid];if(b.dead||b.type!=='Castle'||b.underConstruction)continue;
    b.atkTimer-=dt;if(b.atkTimer>0)continue;
    for(const tuid in units){const u=units[tuid];if(!u.dead&&u.team!==b.team&&dist2D(b.x,b.z,u.x,u.z)<11.7){u.hp-=18;gs.projPool.push({id:uid(),fx:b.x,fy:gH(b.x,b.z)+7,fz:b.z,tx:u.x,ty:gH(u.x,u.z)+1,tz:u.z,color:0xffa030,life:1.4,maxLife:1.4});if(u.hp<=0){u.dead=true;teams[u.team].population-=(u.pop||1);}b.atkTimer=2.5;break;}}
    if(b.atkTimer<=0)b.atkTimer=0.5;
  }

  // ─ Construction progress ─
  for(const bid in buildings){
    const b=buildings[bid];
    if(!b.underConstruction||b.dead) continue;
    // Count villagers actively building this site
    let builderCount=0;
    for(const uid2 in units){
      const u=units[uid2];
      if(!u.dead&&u.state==='building'&&u.buildTarget===bid) builderCount++;
    }
    if(builderCount>0){
      b.buildProgress+=dt; // 1 builder = normal speed (could scale with count)
      // HP grows proportionally so HP bar shows progress
      b.hp=Math.max(1,Math.round((b.buildProgress/b.buildTime)*b.maxHp));
      if(b.buildProgress>=b.buildTime){
        b.underConstruction=false;b.buildProgress=b.buildTime;b.hp=b.maxHp;
        if(b.type==='House') teams[b.team].maxPop+=5;
        gs.events.push({msg:`${b.type} construction complete!`,type:'good',team:b.team});
        // Release builders
        for(const uid2 in units){
          const u=units[uid2];
          if(!u.dead&&u.state==='building'&&u.buildTarget===bid){u.state='idle';u.buildTarget=null;}
        }
      }
    }
  }

  // ─ Production ─
  for(const bid in buildings){
    const b=buildings[bid];if(!b.productionQueue||!b.productionQueue.length)continue;
    b.productionTimer+=dt;const needed=UDEFS[b.productionQueue[0]]?.trainTime||9;
    if(b.productionTimer>=needed){
      const type=b.productionQueue.shift();b.productionTimer=0;
      const def=UDEFS[type],t=teams[b.team];
      if(t.population+(def?.pop||1)<=t.maxPop){
        let angle=Math.random()*Math.PI*2,dist=b.size+1.5;
        let ox=b.x+Math.cos(angle)*dist,oz=b.z+Math.sin(angle)*dist;
        for(let i=0;i<16&&iW(ox,oz);i++){angle+=Math.PI/8;ox=b.x+Math.cos(angle)*dist;oz=b.z+Math.sin(angle)*dist;}
        const nu=mkUnit(type,ox,oz,b.team,b.ownerId||('team'+b.team));
        units[nu.id]=nu;t.population+=(def.pop||1);
        gs.events.push({type:'trained',unitType:type,team:b.team});
      }
    }
  }

  // ─ Farm/Lumber income ─
  gs.incomeTimer+=dt;
  if(gs.incomeTimer>=5){
    gs.incomeTimer=0;
    for(const t of[1,2]){
      const farms=Object.values(buildings).filter(b=>!b.dead&&!b.underConstruction&&b.team===t&&b.type==='Farm').length;
      const lumber=Object.values(buildings).filter(b=>!b.dead&&!b.underConstruction&&b.team===t&&b.type==='Lumbercamp').length;
      const fa=(teams[t].researched||[]).includes('Horse Collar')?12:8;
      teams[t].food=Math.min(9999,teams[t].food+farms*fa);
      teams[t].wood=Math.min(9999,teams[t].wood+lumber*5);
    }
  }

  // ─ AI players ─
  const aiCtx={uid,UDEFS,BCOSTS,BHPS,BSIZES,MAP,HALF,URES,VRES};
  for(const[team,aiP] of Object.entries(lobby.aiPlayers||{})){
    tickAIPlayer(lobby, dt, Number(team), aiP.difficulty, aiCtx);
  }

  // ─ Score ─
  teams[1].score+=dt*0.5;teams[2].score+=dt*0.5;

  // ─ Win check ─
  const b1=buildings[gs.tc1],b2=buildings[gs.tc2];
  if(b1&&b1.dead){endGame(lobby,2);return;}
  if(b2&&b2.dead){endGame(lobby,1);return;}

  // ─ Prune dead ─
  for(const id in units)if(units[id].dead)delete units[id];
  gs.projPool=gs.projPool.filter(p=>p.life>0).map(p=>({...p,life:p.life-dt,maxLife:p.maxLife}));

  const unitsDelta={};
  for(const[id,u] of Object.entries(units)){
    unitsDelta[id]={id:u.id,x:u.x,z:u.z,tx:u.tx,tz:u.tz,hp:u.hp,maxHp:u.maxHp,state:u.state,team:u.team,type:u.type,pop:u.pop};
  }
  const bldsDelta={};
  for(const[id,b] of Object.entries(buildings)){
    bldsDelta[id]={id:b.id,x:b.x,z:b.z,hp:b.hp,maxHp:b.maxHp,type:b.type,team:b.team,size:b.size,
      productionQueue:b.productionQueue,dead:b.dead,
      underConstruction:b.underConstruction,buildProgress:b.buildProgress,buildTime:b.buildTime};
  }
  io.to(lobby.id).emit('gameState',{
    units:unitsDelta,buildings:bldsDelta,teams,resNodes:gs.resNodes.filter(r=>!r.depleted),
    projPool:gs.projPool,events:gs.events.splice(0),gameTime:gs.gameTime
  });
}


function endGame(lobby,winner){
  lobby.status='ended';if(lobby.tickInterval)clearInterval(lobby.tickInterval);
  io.to(lobby.id).emit('gameOver',{winner});
}

const lobbies={},players={};
function getLobbyPlayers(l){
  const humans=Object.values(l.players).map(p=>({id:p.id,name:p.name,team:p.team,isAI:false}));
  const ais=Object.entries(l.aiPlayers||{}).map(([team,ai])=>({
    id:'ai_'+team,name:`AI · ${ai.difficulty.charAt(0).toUpperCase()+ai.difficulty.slice(1)}`,
    team:Number(team),isAI:true,difficulty:ai.difficulty
  }));
  return [...humans,...ais];
}

io.on('connection',socket=>{
  console.log('Connected:',socket.id);

  socket.on('setName',({name})=>{
    players[socket.id]={id:socket.id,name:name.slice(0,20),lobbyId:null,team:null};
    socket.emit('nameSet',{id:socket.id});
  });

  socket.on('getLobbies',()=>{
    socket.emit('lobbiesList',Object.values(lobbies).map(l=>({id:l.id,name:l.name,status:l.status,playerCount:Object.keys(l.players).length,maxPlayers:4})));
  });

  socket.on('createLobby',({lobbyName})=>{
    const p=players[socket.id];if(!p)return;
    const lobby=createLobby(lobbyName||`${p.name}'s Realm`,socket.id);
    lobbies[lobby.id]=lobby;p.lobbyId=lobby.id;p.team=1;lobby.players[socket.id]=p;
    socket.join(lobby.id);
    const gs=lobby.gs;
    socket.emit('lobbyJoined',{lobbyId:lobby.id,team:1,isHost:true,players:getLobbyPlayers(lobby),
      mapData:{heights:Array.from(gs.heights),resNodes:gs.resNodes,pox:gs.pox,poz:gs.poz,aox:gs.aox,aoz:gs.aoz},
      initialState:{units:gs.units,buildings:gs.buildings,teams:gs.teams}});
    io.to(lobby.id).emit('lobbyUpdate',{players:getLobbyPlayers(lobby)});
  });

  socket.on('joinLobby',({lobbyId,team})=>{
    const p=players[socket.id];if(!p)return;
    const lobby=lobbies[lobbyId];
    if(!lobby||lobby.status!=='waiting'){socket.emit('error',{message:'Lobby unavailable'});return;}
    if(Object.keys(lobby.players).length>=4){socket.emit('error',{message:'Lobby full'});return;}
    const t1=Object.values(lobby.players).filter(x=>x.team===1).length;
    const t2=Object.values(lobby.players).filter(x=>x.team===2).length;
    let assignedTeam=(t1<=t2)?1:2;
    if(t1>=2)assignedTeam=2;if(t2>=2)assignedTeam=1;
    if(p.lobbyId){const ol=lobbies[p.lobbyId];if(ol)delete ol.players[socket.id];socket.leave(p.lobbyId);}
    p.lobbyId=lobby.id;p.team=assignedTeam;lobby.players[socket.id]=p;socket.join(lobby.id);
    const gs=lobby.gs;
    socket.emit('lobbyJoined',{lobbyId:lobby.id,team:p.team,isHost:lobby.hostId===socket.id,players:getLobbyPlayers(lobby),
      mapData:{heights:Array.from(gs.heights),resNodes:gs.resNodes,pox:gs.pox,poz:gs.poz,aox:gs.aox,aoz:gs.aoz},
      initialState:{units:gs.units,buildings:gs.buildings,teams:gs.teams}});
    io.to(lobby.id).emit('lobbyUpdate',{players:getLobbyPlayers(lobby)});
  });

  socket.on('switchTeam',({team})=>{
    const p=players[socket.id];if(!p||!p.lobbyId)return;
    const lobby=lobbies[p.lobbyId];if(!lobby||lobby.status!=='waiting')return;
    if(Object.values(lobby.players).filter(x=>x.team===team&&x.id!==socket.id).length>=2){socket.emit('error',{message:'Team full'});return;}
    p.team=team;io.to(lobby.id).emit('lobbyUpdate',{players:getLobbyPlayers(lobby)});
  });

  socket.on('startGame',()=>{
    const p=players[socket.id];if(!p||!p.lobbyId)return;
    const lobby=lobbies[p.lobbyId];if(!lobby||lobby.hostId!==socket.id)return;
    lobby.status='playing';
    const gs=lobby.gs;
    const teamToSocket={};
    for(const[sid,pl] of Object.entries(lobby.players)) teamToSocket[pl.team]=sid;
    for(const u of Object.values(gs.units)){
      if(teamToSocket[u.team]) u.ownerId=teamToSocket[u.team];
      else if(lobby.aiPlayers[u.team]) u.ownerId='ai_team_'+u.team;
    }
    for(const b of Object.values(gs.buildings)){
      if(teamToSocket[b.team]) b.ownerId=teamToSocket[b.team];
      else if(lobby.aiPlayers[b.team]) b.ownerId='ai_team_'+b.team;
    }
    for(const[sid,pl] of Object.entries(lobby.players)){
      io.to(sid).emit('gameStarted',{
        units:gs.units,buildings:gs.buildings,teams:gs.teams,team:pl.team,
        mapData:{heights:Array.from(gs.heights),resNodes:gs.resNodes,pox:gs.pox,poz:gs.poz,aox:gs.aox,aoz:gs.aoz}
      });
    }
    lobby.tickInterval=setInterval(()=>gameTick(lobby),TICK);
  });

  socket.on('cmd',cmd=>{
    const p=players[socket.id];if(!p||!p.lobbyId)return;
    const lobby=lobbies[p.lobbyId];if(!lobby||lobby.status!=='playing')return;
    const gs=lobby.gs;const{units,buildings,teams}=gs;

    if(cmd.type==='move'){for(const id of(cmd.unitIds||[])){const u=units[id];if(!u||u.ownerId!==socket.id)continue;u.state='moving';u.tx=cmd.x;u.tz=cmd.z;u.target=null;}}
    else if(cmd.type==='stop'){for(const id of(cmd.unitIds||[])){const u=units[id];if(!u||u.ownerId!==socket.id)continue;u.state='idle';u.target=null;}}
    else if(cmd.type==='attack'){for(const id of(cmd.unitIds||[])){const u=units[id];if(!u||u.ownerId!==socket.id)continue;if(units[cmd.targetId]){u.state='attacking';u.target=cmd.targetId;}else if(buildings[cmd.targetId]){u.state='attacking_building';u.target=cmd.targetId;}}}
    else if(cmd.type==='resume_build'){
      const b=buildings[cmd.buildingId];
      if(!b||b.dead||!b.underConstruction||b.team!==p.team)return;
      for(const id of(cmd.unitIds||[])){
        const u=units[id];
        // Any villager on the same team may help, regardless of original owner
        if(!u||u.dead||u.type!=='Villager'||u.team!==p.team)continue;
        u.state='moving_to_build';u.buildTarget=b.id;
        u.tx=b.x+(Math.random()-0.5)*b.size;u.tz=b.z+(Math.random()-0.5)*b.size;
      }
    }
    else if(cmd.type==='gather'){for(const id of(cmd.unitIds||[])){const u=units[id];if(!u||u.ownerId!==socket.id||u.type!=='Villager')continue;u.gatherTarget=cmd.resourceId;u.state='moving_to_gather';const rn=gs.resNodes.find(r=>r.id===cmd.resourceId);if(rn){u.tx=rn.x+(Math.random()-0.5);u.tz=rn.z+(Math.random()-0.5);}}}
    else if(cmd.type==='build'){
      const t=teams[p.team],cost=BCOSTS[cmd.buildType];if(!cost)return;
      if(!afford(t,cost)){socket.emit('error',{message:'Not enough resources'});return;}
      if(isW(cmd.x,cmd.z,gs.heights)){socket.emit('error',{message:'Cannot build on water!'});return;}
      spend(t,cost);
      // Building starts under construction — villagers must walk there and build it
      const b=mkBuilding(cmd.buildType,cmd.x,cmd.z,p.team,socket.id,true);
      buildings[b.id]=b;
      // Send assigned villagers to the site
      if(cmd.villagerIds)for(const vid of cmd.villagerIds){
        const v=units[vid];
        if(v&&v.ownerId===socket.id&&v.type==='Villager'){
          v.state='moving_to_build';v.buildTarget=b.id;
          v.tx=b.x+(Math.random()-0.5)*b.size;v.tz=b.z+(Math.random()-0.5)*b.size;
        }
      }
      io.to(lobby.id).emit('buildingPlaced',{building:b});
      gs.events.push({msg:`${cmd.buildType} construction started`,type:'info',team:p.team});
    }
    else if(cmd.type==='produce'){
      const b=buildings[cmd.buildingId];if(!b||b.ownerId!==socket.id)return;
      const def=UDEFS[cmd.unitType];if(!def)return;
      const t=teams[p.team];
      if(!afford(t,def.cost)){socket.emit('error',{message:'Not enough resources'});return;}
      if(t.population+(def.pop||1)>t.maxPop){socket.emit('error',{message:'Population cap reached! Build Houses.'});return;}
      spend(t,def.cost);b.productionQueue.push(cmd.unitType);
    }
    else if(cmd.type==='research'){
      const tech=TECHS.find(x=>x.id===cmd.techId);if(!tech)return;
      const t=teams[p.team];
      if(t.age<tech.age){socket.emit('error',{message:'Age requirement not met'});return;}
      if((t.researched||[]).includes(cmd.techId))return;
      if(!afford(t,tech.cost)){socket.emit('error',{message:'Not enough resources'});return;}
      spend(t,tech.cost);t.researched.push(cmd.techId);
      if(cmd.techId==='Feudal Age'){t.age=1;gs.events.push({msg:`Team ${p.team} advances to Feudal Age!`,type:'good'});}
      if(cmd.techId==='Castle Age'){t.age=2;gs.events.push({msg:`Team ${p.team} advances to Castle Age!`,type:'good'});}
      if(cmd.techId==='Imperial Age'){t.age=3;gs.events.push({msg:`Team ${p.team} reaches Imperial Age!`,type:'good'});}
      if(cmd.techId==='Loom')for(const u of Object.values(units)){if(u.team===p.team&&u.type==='Villager'){u.maxHp+=40;u.hp=Math.min(u.hp+40,u.maxHp);}}
      if(cmd.techId==='Masonry')for(const b of Object.values(buildings)){if(b.team===p.team){b.maxHp=Math.floor(b.maxHp*1.2);}}
      if(cmd.techId==='Scale Armor')for(const u of Object.values(units)){if(u.team===p.team)u.def+=2;}
      if(cmd.techId==='Plate Armor')for(const u of Object.values(units)){if(u.team===p.team)u.def+=4;}
      socket.emit('techResearched',{techId:cmd.techId,team:p.team});
    }
  });

  socket.on('addAI',({team,difficulty})=>{
    const p=players[socket.id];if(!p||!p.lobbyId)return;
    const lobby=lobbies[p.lobbyId];
    if(!lobby||lobby.status!=='waiting'||lobby.hostId!==socket.id)return;
    const t=Number(team);
    if(Object.values(lobby.players).some(pl=>pl.team===t)){
      socket.emit('error',{message:'That team already has a human player'});return;
    }
    if(!['easy','moderate','hard'].includes(difficulty)) return;
    if(!lobby.aiPlayers) lobby.aiPlayers={};
    lobby.aiPlayers[t]={difficulty};
    io.to(lobby.id).emit('lobbyUpdate',{players:getLobbyPlayers(lobby)});
  });

  socket.on('removeAI',({team})=>{
    const p=players[socket.id];if(!p||!p.lobbyId)return;
    const lobby=lobbies[p.lobbyId];
    if(!lobby||lobby.status!=='waiting'||lobby.hostId!==socket.id)return;
    if(lobby.aiPlayers) delete lobby.aiPlayers[Number(team)];
    io.to(lobby.id).emit('lobbyUpdate',{players:getLobbyPlayers(lobby)});
  });

  socket.on('chatMessage',({text})=>{
    const p=players[socket.id];if(!p||!p.lobbyId)return;
    io.to(p.lobbyId).emit('chat',{name:p.name,text:text.slice(0,200),team:p.team});
  });

  socket.on('disconnect',()=>{
    const p=players[socket.id];
    if(p?.lobbyId){const lobby=lobbies[p.lobbyId];if(lobby){delete lobby.players[socket.id];io.to(lobby.id).emit('lobbyUpdate',{players:getLobbyPlayers(lobby)});if(!Object.keys(lobby.players).length&&lobby.tickInterval){clearInterval(lobby.tickInterval);delete lobbies[lobby.id];}}}
    delete players[socket.id];console.log('Disconnected:',socket.id);
  });
});

const PORT=process.env.PORT||3000;
httpServer.listen(PORT,()=>console.log(`Age of Realms server running on port ${PORT}`));
