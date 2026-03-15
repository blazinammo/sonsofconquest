'use strict';
// ═══════════════════════════════════════════════════════════════
//  AGE OF REALMS — Multiplayer client
//  All 3D models, FOW, terrain, AI panel, tech tree, etc.
//  ported from Age of Conquest II reference game
// ═══════════════════════════════════════════════════════════════

const MAP = 150, HALF = 75;
const URES = 90, VRES = 90;
const WATER_LEVEL = -1.3;

// ── Socket ────────────────────────────────────────────────────
const socket = io();

// ── App State ─────────────────────────────────────────────────
let myId = null, myTeam = null, myName = '', isHost = false, currentLobbyId = null;
let gameStarted = false;

// ── Terrain / Map data (received from server) ─────────────────
let terrHeights = null;
let P_OX = 0, P_OZ = 0, AI_OX = 0, AI_OZ = 0;

// ── Game state (mirrored from server) ─────────────────────────
let serverUnits = {}, serverBuildings = {}, serverTeams = {}, serverResNodes = [];

// ── Local meshes (id → THREE.Object3D) ────────────────────────
const unitMeshes = {}, buildingMeshes = {}, resNodeMeshes = {};
// ── Snapshot interpolation ─────────────────────────────────────
const interpFrom={},interpTo={};
let interpT=0;
const INTERP_PERIOD=0.15;
const projMeshes = [];
const _clientProjs={};
const _projGeo=new THREE.SphereGeometry(0.09,5,5);
const _projMatNormal=new THREE.MeshStandardMaterial({color:0xd8d8b0,roughness:0.3,emissive:new THREE.Color(0xd8d8b0),emissiveIntensity:0.8});
const _projMatFire=new THREE.MeshStandardMaterial({color:0xff6600,roughness:0.2,metalness:0.2,emissive:new THREE.Color(0xff6600),emissiveIntensity:0.8});
const _projMatTower=new THREE.MeshStandardMaterial({color:0xffe070,roughness:0.3,emissive:new THREE.Color(0xffe070),emissiveIntensity:0.9});
const _projMatCastle=new THREE.MeshStandardMaterial({color:0xffa030,roughness:0.25,emissive:new THREE.Color(0xffa030),emissiveIntensity:1.1});
function _getProjMat(c){return c===0xff6600?_projMatFire:c===0xffe070?_projMatTower:c===0xffa030?_projMatCastle:_projMatNormal;}
function _acquireProjMesh(color){
  for(const cp of Object.values(_clientProjs)){if(cp.mesh&&!cp.mesh.visible){cp.mesh.material=_getProjMat(color);cp.mesh.visible=true;return cp.mesh;}}
  const m=new THREE.Mesh(_projGeo,_getProjMat(color));scene.add(m);return m;
}
const particlePool = [];
const envObjects = [];   // { mesh, x, z }

// ── Selection ─────────────────────────────────────────────────
let selectedUnitIds = [], selectedBuildingId = null, selectedResNodeId = null;

// ── Rally point visuals ────────────────────────────────────────────────────
// A dashed line from the building to its rally point + a flag marker
let _rallyLine = null;   // THREE.Line
let _rallyFlag = null;   // THREE.Mesh (flag marker at rally point)

// ── Build ghost ───────────────────────────────────────────────
let ghostState = null;

// ── Event log ─────────────────────────────────────────────────
const evLog = [];

// ── Three.js globals ──────────────────────────────────────────
let renderer, scene, camera, terrain, waterMesh, waterMat;
let sun, fillLight, sky;

// ── FOW ───────────────────────────────────────────────────────
const FOW_RES = 256, FOW_CELLS = 240, FOW_CELL = MAP / FOW_CELLS;
const fow    = new Uint8Array(FOW_CELLS * FOW_CELLS);   // integer state: 0=dark,1=shroud,2=visible
const fowVis = new Float32Array(FOW_CELLS * FOW_CELLS); // float level: 0.0=dark, 0.5=shroud, 1.0=visible
const fowPixels = new Uint8Array(FOW_RES * FOW_RES * 4);
let fowTexture = null, fowOrthoScene = null, fowOrthoCamera = null, fowQuadMat = null;
let fowTimer = 0;

// ── Minimap FOW ───────────────────────────────────────────────
const mmFowCanvas = document.createElement('canvas');
mmFowCanvas.width = 150; mmFowCanvas.height = 118;
const mmFowCtx = mmFowCanvas.getContext('2d');

const BLDG_VISION = {
  'Town Center':16,'Tower':15,'Barracks':11,'House':8,
  'Farm':8,'Blacksmith':9,'Lumbercamp':9,'MiningCamp':9,'Castle':19,'Market':11
};

// ── Camera ────────────────────────────────────────────────────
let camTarget, camDist = 32, camYaw = 0;
const keys = {};

// ── Minimap ───────────────────────────────────────────────────
let mmC, mmX, mmTerrainImg = null;

// ── Game time (for day/night etc) ─────────────────────────────
let gameTime = 0;

// =================================================================
//  PBR MESH HELPERS (exact copies from reference)
// =================================================================
function makePBRBox(w,h,d,color,roughness=0.7,metalness=0.0,emissive=0x000000,emissInt=0){
  const g=new THREE.BoxGeometry(w,h,d);
  const m=new THREE.MeshStandardMaterial({color,roughness,metalness,emissive,emissiveIntensity:emissInt});
  const mesh=new THREE.Mesh(g,m);
  mesh.castShadow=true; mesh.receiveShadow=true;
  return mesh;
}
function makePBRCyl(rt,rb,h,segs,color,roughness=0.7,metalness=0){
  const g=new THREE.CylinderGeometry(rt,rb,h,segs);
  const m=new THREE.MeshStandardMaterial({color,roughness,metalness});
  const mesh=new THREE.Mesh(g,m);
  mesh.castShadow=true; mesh.receiveShadow=true;
  return mesh;
}
function makePBRSphere(r,segs,color,roughness=0.6,metalness=0){
  const g=new THREE.SphereGeometry(r,segs,segs);
  const m=new THREE.MeshStandardMaterial({color,roughness,metalness});
  const mesh=new THREE.Mesh(g,m);
  mesh.castShadow=true; mesh.receiveShadow=true;
  return mesh;
}

// =================================================================
//  TERRAIN HELPERS
// =================================================================
function getHeight(wx,wz){
  if(!terrHeights) return 0;
  const cx=Math.max(-HALF,Math.min(HALF-0.001,wx));
  const cz=Math.max(-HALF,Math.min(HALF-0.001,wz));
  const gx=(cx+HALF)/MAP*URES, gz=(cz+HALF)/MAP*VRES;
  const col0=Math.floor(gx),col1=Math.min(col0+1,URES);
  const row0=Math.floor(gz),row1=Math.min(row0+1,VRES);
  const fx=gx-col0,fz=gz-row0;
  const h00=terrHeights[row0*(URES+1)+col0],h10=terrHeights[row0*(URES+1)+col1];
  const h01=terrHeights[row1*(URES+1)+col0],h11=terrHeights[row1*(URES+1)+col1];
  return h00*(1-fx)*(1-fz)+h10*fx*(1-fz)+h01*(1-fx)*fz+h11*fx*fz;
}
function isWater(wx,wz){ return getHeight(wx,wz)<WATER_LEVEL; }

// =================================================================
//  FOW SYSTEM (exact port from reference)
// =================================================================
function fowIdx(cx,cz){ return cz*FOW_CELLS+cx; }
function fowCell(wx,wz){
  const cx=Math.floor((wx+HALF)/FOW_CELL);
  const cz=Math.floor((wz+HALF)/FOW_CELL);
  if(cx<0||cz<0||cx>=FOW_CELLS||cz>=FOW_CELLS) return 0;
  return fow[fowIdx(cx,cz)];
}
function fowReveal(wx,wz,radiusWorld){
  const cx0=Math.floor((wx+HALF)/FOW_CELL);
  const cz0=Math.floor((wz+HALF)/FOW_CELL);
  const cr=Math.ceil(radiusWorld/FOW_CELL)+1; // +1 to include gradient fringe cells
  const fadeStart=radiusWorld*0.70; // inner 70% is fully visible
  for(let dz=-cr;dz<=cr;dz++) for(let dx=-cr;dx<=cr;dx++){
    const nx=cx0+dx,nz=cz0+dz;
    if(nx<0||nz<0||nx>=FOW_CELLS||nz>=FOW_CELLS) continue;
    // World-space distance from unit to this cell's centre
    const cellWX=-HALF+(nx+0.5)*FOW_CELL;
    const cellWZ=-HALF+(nz+0.5)*FOW_CELL;
    const dist=Math.sqrt((cellWX-wx)**2+(cellWZ-wz)**2);
    if(dist>radiusWorld) continue;
    // Smooth falloff: 1.0 in core, fades to 0.5 at exact radius edge
    const vis=dist<=fadeStart
      ? 1.0
      : 0.5+0.5*(1.0-(dist-fadeStart)/(radiusWorld-fadeStart));
    const idx=fowIdx(nx,nz);
    if(fowVis[idx]<vis) fowVis[idx]=vis;
    fow[idx]=2; // integer state for game logic queries
  }
}
function initFOWPlane(){
  fowTexture=new THREE.DataTexture(fowPixels,FOW_RES,FOW_RES,THREE.RGBAFormat);
  fowTexture.magFilter=THREE.LinearFilter;
  fowTexture.minFilter=THREE.LinearFilter;
  fowTexture.needsUpdate=true;
  fowOrthoScene=new THREE.Scene();
  fowOrthoCamera=new THREE.OrthographicCamera(-1,1,1,-1,0,1);
  const fowShader={
    uniforms:{uFow:{value:fowTexture},uInvVP:{value:new THREE.Matrix4()},uMapMin:{value:new THREE.Vector2(-HALF,-HALF)},uMapSize:{value:new THREE.Vector2(MAP,MAP)}},
    vertexShader:`varying vec2 vUv;void main(){vUv=uv;gl_Position=vec4(position.xy,0.0,1.0);}`,
    fragmentShader:`
      uniform sampler2D uFow;uniform mat4 uInvVP;uniform vec2 uMapMin;uniform vec2 uMapSize;varying vec2 vUv;
      void main(){
        vec4 ndcN=vec4(vUv*2.0-1.0,-1.0,1.0),ndcF=vec4(vUv*2.0-1.0,1.0,1.0);
        vec4 wN=uInvVP*ndcN,wF=uInvVP*ndcF;wN/=wN.w;wF/=wF.w;
        vec3 dir=normalize(wF.xyz-wN.xyz);
        if(abs(dir.y)<0.0001){gl_FragColor=vec4(0.,0.,0.,1.);return;}
        float t=-wN.y/dir.y;if(t<0.){gl_FragColor=vec4(0.,0.,0.,1.);return;}
        vec3 wp=wN.xyz+dir*t;
        vec2 fu=(wp.xz-uMapMin)/uMapSize;fu.y=1.0-fu.y;
        if(fu.x<0.||fu.x>1.||fu.y<0.||fu.y>1.){gl_FragColor=vec4(0.,0.,0.,1.);return;}
        vec2 ts=vec2(${FOW_RES}.0),tx=1.0/ts,f=fract(fu*ts),sf=smoothstep(0.0,1.0,f);
        vec4 c00=texture2D(uFow,fu),c10=texture2D(uFow,fu+vec2(tx.x,0.)),c01=texture2D(uFow,fu+vec2(0.,tx.y)),c11=texture2D(uFow,fu+tx);
        gl_FragColor=mix(mix(c00,c10,sf.x),mix(c01,c11,sf.x),sf.y);
      }`
  };
  const qm=new THREE.ShaderMaterial({...fowShader,transparent:true,depthTest:false,depthWrite:false});
  fowQuadMat=qm;
  fowOrthoScene.add(new THREE.Mesh(new THREE.PlaneGeometry(2,2),qm));
}
function _fowVisToAlpha(v){
  // Piecewise: 0.0→255 (full dark), 0.5→195 (shroud), 1.0→0 (clear)
  if(v<=0.5) return 255-v*120;           // 255 at 0.0, 195 at 0.5
  return 195*(1-(v-0.5)*2);             // 195 at 0.5, 0 at 1.0
}
function updateFOWTexture(){
  const N=FOW_CELLS;
  // Bilinearly upsample fowVis (float) directly into the texture — no box blur needed.
  // The smooth gradients written by fowReveal already give soft edges.
  for(let py=0;py<FOW_RES;py++) for(let px=0;px<FOW_RES;px++){
    const gx=(px/FOW_RES)*(N-1), gz=((FOW_RES-1-py)/FOW_RES)*(N-1);
    const x0=Math.floor(gx),x1=Math.min(x0+1,N-1);
    const z0=Math.floor(gz),z1=Math.min(z0+1,N-1);
    const fx=gx-x0, fz=gz-z0;
    const v=fowVis[z0*N+x0]*(1-fx)*(1-fz)
           +fowVis[z0*N+x1]*fx*(1-fz)
           +fowVis[z1*N+x0]*(1-fx)*fz
           +fowVis[z1*N+x1]*fx*fz;
    const idx=(py*FOW_RES+px)*4;
    fowPixels[idx]=8;fowPixels[idx+1]=10;fowPixels[idx+2]=18;
    fowPixels[idx+3]=Math.round(_fowVisToAlpha(v));
  }
  fowTexture.needsUpdate=true;
}
function tickFOW(dt){
  fowTimer+=dt;
  if(fowTimer<0.15) return;
  fowTimer=0;
  for(let i=0;i<fow.length;i++){
    if(fow[i]===2){
      fow[i]=1;
      // Clamp to shroud level — preserve partial visibility from last reveal
      if(fowVis[i]>0.5) fowVis[i]=0.5;
    }
  }
  // Reveal from my units — project the unit's elevated 3D position along the
  // camera ray to y=0 so the FOW circle is always visually centred on the unit
  // even when it stands on high terrain.
  for(const id in serverUnits){
    const u=serverUnits[id];
    if(u.team!==myTeam) continue;
    const mesh=unitMeshes[id];
    let rx=u.x, rz=u.z;
    if(mesh && camera){
      // Ray from camera through the unit's 3D mesh position, intersected with y=0
      const mx=mesh.position.x, my=mesh.position.y, mz=mesh.position.z;
      const cx=camera.position.x, cy=camera.position.y, cz=camera.position.z;
      const dx=mx-cx, dy=my-cy, dz=mz-cz;
      // t such that (cy + dy*t) = 0  →  t = -cy/dy
      if(Math.abs(dy)>0.001){
        const t=-cy/dy;
        rx=cx+dx*t;
        rz=cz+dz*t;
      } else {
        rx=mx; rz=mz;
      }
    }
    fowReveal(rx,rz,u.vision||7);
  }
  // Reveal from my buildings
  for(const id in serverBuildings){
    const b=serverBuildings[id];
    if(b.team!==myTeam) continue;
    fowReveal(b.x,b.z,BLDG_VISION[b.type]||7);
  }
  updateFOWTexture();
  // Show/hide enemy units
  for(const id in unitMeshes){
    const u=serverUnits[id];
    if(!u||u.team===myTeam) continue;
    unitMeshes[id].visible=fowCell(u.x,u.z)===2;
  }
  // Enemy buildings
  for(const id in buildingMeshes){
    const b=serverBuildings[id];
    if(!b||b.team===myTeam) continue;
    const v=fowCell(b.x,b.z);
    buildingMeshes[id].visible=v>=1;
  }
  // Resource nodes
  for(const id in resNodeMeshes){
    const rn=serverResNodes.find(r=>r.id===id);
    if(rn) resNodeMeshes[id].visible=fowCell(rn.x,rn.z)>=1;
  }
  // Env objects
  for(const obj of envObjects) obj.mesh.visible=fowCell(obj.x,obj.z)>=1;
}
function drawMinimapFOW(){
  const iw=150,ih=118;
  const id=mmFowCtx.createImageData(iw,ih);
  for(let py=0;py<ih;py++) for(let px=0;px<iw;px++){
    const wx=(px/iw)*MAP-HALF,wz=(py/ih)*MAP-HALF;
    const v=fowCell(wx,wz),i=(py*iw+px)*4;
    id.data[i]=0;id.data[i+1]=0;id.data[i+2]=0;
    id.data[i+3]=v===0?255:v===1?140:0;
  }
  mmFowCtx.putImageData(id,0,0);
  mmX.drawImage(mmFowCanvas,0,0);
}

// =================================================================
//  3D SCENE INIT
// =================================================================
function initScene(){
  const canvas=document.getElementById('canvas');
  renderer=new THREE.WebGLRenderer({canvas,antialias:true,powerPreference:'high-performance'});
  renderer.setSize(innerWidth,innerHeight);
  renderer.setPixelRatio(Math.min(devicePixelRatio,1.5));
  renderer.shadowMap.enabled=true;
  renderer.shadowMap.type=THREE.PCFSoftShadowMap;
  renderer.toneMapping=THREE.LinearToneMapping;
  renderer.toneMappingExposure=1.0;

  scene=new THREE.Scene();
  scene.background=new THREE.Color(0x6a8faa);
  scene.fog=new THREE.FogExp2(0x6a8faa,0.003);

  camera=new THREE.PerspectiveCamera(52,innerWidth/innerHeight,0.2,300);
  camera.position.set(0,30,30);
  camera.lookAt(0,0,0);

  // Lighting
  sun=new THREE.DirectionalLight(0xffffff,0.45);
  sun.position.set(40,70,30);
  sun.castShadow=true;
  sun.shadow.mapSize.set(1024,1024);
  sun.shadow.camera.near=1;sun.shadow.camera.far=250;
  sun.shadow.camera.left=-105;sun.shadow.camera.right=105;
  sun.shadow.camera.top=105;sun.shadow.camera.bottom=-105;
  sun.shadow.bias=-0.0003;
  scene.add(sun);
  fillLight=new THREE.DirectionalLight(0xddeeff,0.2);
  fillLight.position.set(-30,20,-20);
  scene.add(fillLight);
  sky=new THREE.HemisphereLight(0xc8ddf0,0x7a9060,0.6);
  scene.add(sky);
  scene.add(new THREE.AmbientLight(0x707070,0.7));

  window.addEventListener('resize',()=>{
    renderer.setSize(innerWidth,innerHeight);
    camera.aspect=innerWidth/innerHeight;
    camera.updateProjectionMatrix();
  });
}

// =================================================================
//  TERRAIN GENERATION (client-side from server heights)
// =================================================================
function buildTerrain(){
  const terrGeo=new THREE.PlaneGeometry(MAP,MAP,URES,VRES);
  const tPos=terrGeo.attributes.position;
  const tColor=new Float32Array(tPos.count*3);
  for(let row=0;row<=VRES;row++) for(let col=0;col<=URES;col++){
    const i=row*(URES+1)+col;
    const h=terrHeights[i];
    tPos.setZ(i,h);
    const slope=Math.abs(h);
    let r,g,b;
    if(h<-0.4){r=0.58;g=0.54;b=0.44;}        // sandy shore — warm buff
    else if(slope>3.0){r=0.52;g=0.50;b=0.46;}  // grey rock
    else if(slope>1.5){r=0.42;g=0.46;b=0.36;}  // rocky grass
    else{r=0.34+slope*0.02;g=0.42+slope*0.01;b=0.28;}  // muted grass
    tColor[i*3]=r;tColor[i*3+1]=g;tColor[i*3+2]=b;
  }
  terrGeo.setAttribute('color',new THREE.BufferAttribute(tColor,3));
  terrGeo.computeVertexNormals();
  const terrMat=new THREE.MeshLambertMaterial({vertexColors:true});
  terrain=new THREE.Mesh(terrGeo,terrMat);
  terrain.rotation.x=-Math.PI/2;
  terrain.receiveShadow=true;
  scene.add(terrain);

  // Water
  const waterGeo=new THREE.PlaneGeometry(MAP+40,MAP+40,1,1);
  waterMat=new THREE.MeshPhongMaterial({color:0x1a5878,emissive:0x0a2a3a,emissiveIntensity:0.3,specular:0x88bbdd,shininess:120,transparent:true,opacity:0.82});
  waterMesh=new THREE.Mesh(waterGeo,waterMat);
  waterMesh.rotation.x=-Math.PI/2;
  waterMesh.position.y=-1.4;
  scene.add(waterMesh);

  initFOWPlane();
  buildEnvironment();
  bakeMinimap();
}

// =================================================================
//  ENVIRONMENT (trees + rocks matching reference)
// =================================================================
function makeTree(x,z,variety=0){
  const g=new THREE.Group();
  const trunkH=1.2+Math.random()*0.8,trunkR=0.12+Math.random()*0.06;
  const trunk=makePBRCyl(trunkR*0.7,trunkR,trunkH,7,0x4a2e0e,0.9);
  trunk.position.y=trunkH/2;g.add(trunk);
  if(variety===0){
    const lc=[0x2d6b1e,0x357a22,0x245518][Math.floor(Math.random()*3)];
    const r=0.6+Math.random()*0.4;
    const top=makePBRSphere(r,7,lc,0.95);top.position.y=trunkH+r*0.6;g.add(top);
    const top2=makePBRSphere(r*0.7,6,lc-0x050500,0.95);top2.position.set(r*0.4,trunkH+r*0.3,0);g.add(top2);
  } else {
    const lc=0x1a5520;
    for(let i=0;i<3;i++){
      const cr=(0.7-i*0.18)*(1+Math.random()*0.2);
      const cone=new THREE.Mesh(new THREE.ConeGeometry(cr,1.1,7),new THREE.MeshStandardMaterial({color:lc-i*0x020400,roughness:0.9}));
      cone.castShadow=true;cone.position.y=trunkH+0.4+i*0.65;g.add(cone);
    }
  }
  const y=getHeight(x,z);
  g.position.set(x,y,z);g.rotation.y=Math.random()*Math.PI*2;
  const s=0.8+Math.random()*0.5;g.scale.set(s,s,s);
  g.visible=false;
  scene.add(g);
  envObjects.push({mesh:g,x,z});
}
function makeRock(x,z){
  const g=new THREE.Group();
  const count=1+Math.floor(Math.random()*3);
  for(let i=0;i<count;i++){
    const r=0.25+Math.random()*0.35;
    const rock=makePBRSphere(r,6,[0x7a7060,0x8a8070,0x6a6558][Math.floor(Math.random()*3)],0.85);
    rock.scale.set(1,0.65+Math.random()*0.35,1);
    rock.position.set((Math.random()-0.5)*0.5,r*0.5,(Math.random()-0.5)*0.5);
    rock.rotation.y=Math.random()*Math.PI;g.add(rock);
  }
  const y=getHeight(x,z);g.position.set(x,y,z);g.visible=false;
  scene.add(g);envObjects.push({mesh:g,x,z});
}
function buildEnvironment(){
  const SAFE_R=14;
  function randAround(cx,cz,rMin,rMax,tries=80){
    for(let i=0;i<tries;i++){
      const a=Math.random()*Math.PI*2,r=rMin+Math.random()*(rMax-rMin);
      const x=cx+Math.cos(a)*r,z=cz+Math.sin(a)*r;
      if(Math.abs(x)<HALF-3&&Math.abs(z)<HALF-3&&!isWater(x,z)) return [x,z];
    }
    return [cx+rMin,cz];
  }
  // Rocks  (trees are now server-side wood resource nodes)
  for(let i=0;i<40;i++){
    const x=(Math.random()-0.5)*MAP*0.88,z=(Math.random()-0.5)*MAP*0.88;
    if(Math.hypot(x-P_OX,z-P_OZ)<SAFE_R||Math.hypot(x-AI_OX,z-AI_OZ)<SAFE_R||isWater(x,z)) continue;
    makeRock(x,z);
  }
}

// =================================================================
//  RESOURCE NODE 3D MESHES (exact port from reference)
// =================================================================
function makeResNodeMesh(rn){
  const g=new THREE.Group();
  if(rn.type==='gold'){
    // Larger base rock with many prominent glowing veins
    const base=makePBRSphere(0.85,9,0x4a4030,0.6);base.scale.set(1.1,0.75,1.1);base.position.y=0.45;g.add(base);
    const mid=makePBRSphere(0.55,8,0x3a3020,0.65);mid.scale.set(0.9,0.8,0.9);mid.position.set(0.3,0.7,0.1);g.add(mid);
    // 8 prominent veins at varied angles
    for(let i=0;i<8;i++){
      const w=0.1+Math.random()*0.12, h=0.4+Math.random()*0.45;
      const vein=makePBRBox(w,h,w*0.8,0xd4a820,0.2,0.7);
      vein.position.set((Math.random()-0.5)*0.9,0.45+Math.random()*0.35,(Math.random()-0.5)*0.9);
      vein.rotation.set((Math.random()-0.5)*1.0,Math.random()*Math.PI,(Math.random()-0.5)*0.8);
      vein.material.emissive=new THREE.Color(0xb08010);vein.material.emissiveIntensity=0.55;g.add(vein);
    }
    // Secondary glint crystals on top
    for(let i=0;i<4;i++){
      const cr=makePBRBox(0.07,0.22,0.07,0xf0c030,0.15,0.8);
      cr.position.set((Math.random()-0.5)*0.5,0.9+Math.random()*0.3,(Math.random()-0.5)*0.5);
      cr.rotation.set(Math.random()*0.4,Math.random()*Math.PI,Math.random()*0.4);
      cr.material.emissive=new THREE.Color(0xd4a820);cr.material.emissiveIntensity=0.8;g.add(cr);
    }
    const gl=new THREE.PointLight(0xffcc20,1.2,5);gl.position.y=1.2;g.add(gl);
    g.scale.set(1.35,1.35,1.35);
  } else if(rn.type==='stone'){
    // Larger cluster with visible mineral striations
    const cnt=3+Math.floor(Math.random()*2);
    const stoneColors=[0x8a8880,0x9a9890,0x7a7870,0x6a6860];
    for(let i=0;i<cnt;i++){
      const r=0.5+Math.random()*0.35;
      const s=makePBRSphere(r,8,stoneColors[i%stoneColors.length],0.88);
      s.scale.set(0.85+Math.random()*0.4,0.72+Math.random()*0.2,0.9+Math.random()*0.2);
      s.position.set((Math.random()-0.5)*1.1,r*0.5,(Math.random()-0.5)*1.1);
      s.rotation.y=Math.random()*Math.PI;g.add(s);
    }
    // Mineral veins — light and dark striations across the stone
    for(let i=0;i<6;i++){
      const vein=makePBRBox(0.06,0.35+Math.random()*0.3,0.55+Math.random()*0.3,i%2===0?0xb8b8b0:0x505048,0.95);
      vein.position.set((Math.random()-0.5)*0.8,0.3+Math.random()*0.3,(Math.random()-0.5)*0.8);
      vein.rotation.set(Math.random()*0.6,Math.random()*Math.PI,(Math.random()-0.5)*0.5);
      g.add(vein);
    }
    g.scale.set(1.4,1.4,1.4);
  } else if(rn.type==='food'){
    const bush=makePBRSphere(0.4,7,0x2a6018,0.9);bush.position.y=0.35;g.add(bush);
    for(let i=0;i<8;i++){
      const berry=makePBRSphere(0.07,5,0xcc2820,0.5);
      const a=Math.random()*Math.PI*2,r=0.3+Math.random()*0.15;
      berry.position.set(Math.cos(a)*r,0.4+Math.random()*0.3,Math.sin(a)*r);g.add(berry);
    }
  } else if(rn.type==='wood'){
    // Use the full detailed tree mesh — variety stored on node from server
    const variety=rn.variety||0;
    const trunkH=1.2+Math.random()*0.8,trunkR=0.12+Math.random()*0.06;
    const trunk=makePBRCyl(trunkR*0.7,trunkR,trunkH,7,0x4a2e0e,0.9);
    trunk.position.y=trunkH/2;g.add(trunk);
    if(variety===0){
      const lc=[0x2d6b1e,0x357a22,0x245518][Math.floor(Math.random()*3)];
      const r=0.6+Math.random()*0.4;
      const top=makePBRSphere(r,7,lc,0.95);top.position.y=trunkH+r*0.6;g.add(top);
      const top2=makePBRSphere(r*0.7,6,lc-0x050500,0.95);top2.position.set(r*0.4,trunkH+r*0.3,0);g.add(top2);
    } else {
      const lc=0x1a5520;
      for(let i=0;i<3;i++){
        const cr=(0.7-i*0.18)*(1+Math.random()*0.2);
        const cone=new THREE.Mesh(new THREE.ConeGeometry(cr,1.1,7),new THREE.MeshStandardMaterial({color:lc-i*0x020400,roughness:0.9}));
        cone.castShadow=true;cone.position.y=trunkH+0.4+i*0.65;g.add(cone);
      }
    }
    const s=0.8+Math.random()*0.5;g.scale.set(s,s,s);
    g.rotation.y=Math.random()*Math.PI*2;
  }
  const y=getHeight(rn.x,rn.z);
  g.position.set(rn.x,y,rn.z);
  g.visible=false;
  scene.add(g);
  resNodeMeshes[rn.id]=g;
}

// =================================================================
//  BUILDING MESHES (exact port from reference)
// =================================================================
const STONE_C=0x9a9490, WOOD_C=0x7a5028, THATCH_C=0x8a7040;

function buildMesh_TownCenter(team){
  const g=new THREE.Group();
  const tc=team===1?'player':'enemy';
  const found=makePBRBox(6.5,0.4,6.5,0x8a8070,0.95);found.position.y=0.2;g.add(found);
  const keep=makePBRBox(5,3,5,STONE_C,0.85);keep.position.y=1.9;g.add(keep);
  for(let mx=-2;mx<=2;mx++) for(const mz of[-2.5,2.5]){if(Math.abs(mx)===1)continue;const m=makePBRBox(0.5,0.5,0.4,0x8a8070,0.9);m.position.set(mx,3.65,mz);g.add(m);}
  for(let mz=-2;mz<=2;mz++) for(const mx of[-2.5,2.5]){if(Math.abs(mz)===1)continue;const m=makePBRBox(0.4,0.5,0.5,0x8a8070,0.9);m.position.set(mx,3.65,mz);g.add(m);}
  for(const [tx,tz] of[[-2.2,-2.2],[2.2,-2.2],[-2.2,2.2],[2.2,2.2]]){
    const t=makePBRCyl(0.65,0.7,4.5,10,STONE_C-0x050505,0.85);t.position.set(tx,2.25,tz);g.add(t);
    const cap=makePBRCyl(0,0.75,0.8,10,tc==='player'?0x2244aa:0xaa2222,0.8);cap.position.set(tx,4.8,tz);g.add(cap);
    const ring=makePBRCyl(0.68,0.68,0.35,10,0x7a7468,0.9);ring.position.set(tx,4.35,tz);g.add(ring);
  }
  const gateL=makePBRBox(0.4,2.2,0.5,0x888070,0.9);gateL.position.set(-0.6,1.5,2.5);g.add(gateL);
  const gateR=makePBRBox(0.4,2.2,0.5,0x888070,0.9);gateR.position.set(0.6,1.5,2.5);g.add(gateR);
  const gateTop=makePBRBox(1.6,0.5,0.5,0x888070,0.9);gateTop.position.set(0,2.7,2.5);g.add(gateTop);
  const door=makePBRBox(0.9,1.9,0.1,0x1e0e04,0.99);door.position.set(0,1.15,2.56);g.add(door);
  const pole=makePBRCyl(0.04,0.04,2.5,5,0x2a1a08,0.9);pole.position.set(0,5.25,0);g.add(pole);
  const bannerC=tc==='player'?0x2a4ecc:0xcc2a2a, bannerE=tc==='player'?0x2244aa:0xaa2222;
  const banner=makePBRBox(0.7,0.5,0.04,bannerC,0.8,0,bannerE,0.5);banner.position.set(0.35,5.9,0);g.add(banner);
  const roof=makePBRBox(4.8,0.25,4.8,STONE_C+0x050505,0.9);roof.position.y=3.52;g.add(roof);
  return g;
}
function buildMesh_Barracks(team){
  const g=new THREE.Group();
  const c=team===1?0x2a3870:0x702a2a;
  const found=makePBRBox(5,0.3,3.5,0x8a8070,0.95);found.position.y=0.15;g.add(found);
  const walls=makePBRBox(4.2,2.4,3,WOOD_C,0.85);walls.position.y=1.35;g.add(walls);
  const roof=makePBRBox(4.6,0.2,3.4,0x5a3810,0.9);roof.position.y=2.65;g.add(roof);
  const ridge=new THREE.Mesh(new THREE.CylinderGeometry(0,0.3,3.6,4),new THREE.MeshStandardMaterial({color:0x4a2e08,roughness:0.9}));
  ridge.geometry.rotateY(Math.PI/4);ridge.position.y=3.1;ridge.rotation.y=Math.PI/2;g.add(ridge);
  const stripe=makePBRBox(4.25,0.35,0.08,c,0.7,0,c,0.2);stripe.position.set(0,2.3,1.52);g.add(stripe);
  const d=makePBRBox(0.75,1.6,0.1,0x1a0c04,0.99);d.position.set(0,1.0,1.52);g.add(d);
  const rack=makePBRBox(0.05,1.0,0.05,0x3a2008,0.95);rack.position.set(1.5,0.8,1.45);g.add(rack);
  const sword=makePBRBox(0.05,0.65,0.05,0xc0c0c0,0.3,0.8);sword.position.set(1.7,0.8,1.45);g.add(sword);
  return g;
}
function buildMesh_House(team){
  const g=new THREE.Group();
  const wc=team===1?0xc09858:0xa07040;
  const found=makePBRBox(2.8,0.25,2.8,0x8a8070,0.95);found.position.y=0.12;g.add(found);
  const walls=makePBRBox(2.4,1.8,2.4,wc,0.85);walls.position.y=1.05;g.add(walls);
  const roofMat=new THREE.MeshStandardMaterial({color:THATCH_C,roughness:0.95});
  const roofGeo=new THREE.CylinderGeometry(0.05,1.75,1.2,4);roofGeo.rotateY(Math.PI/4);
  const roof=new THREE.Mesh(roofGeo,roofMat);roof.castShadow=true;roof.position.y=2.55;g.add(roof);
  const win=makePBRBox(0.4,0.35,0.08,0x1a3050,0.2,0.1,0x2040a0,0.4);win.position.set(0.8,1.3,1.22);g.add(win);
  const door=makePBRBox(0.55,1.1,0.08,0x2a1804,0.99);door.position.set(0,0.65,1.22);g.add(door);
  const ch=makePBRBox(0.35,0.9,0.35,0x787060,0.9);ch.position.set(0.65,2.8,0);g.add(ch);
  return g;
}
function buildMesh_Farm(){
  const g=new THREE.Group();
  const soil=makePBRBox(4,0.12,4,0x7a5c30,0.98);soil.position.y=0.06;g.add(soil);
  for(let row=-1.5;row<=1.5;row+=0.75){const furrow=makePBRBox(3.8,0.1,0.2,0x6a4c28,0.99);furrow.position.set(0,0.1,row);g.add(furrow);}
  for(let cx=-1.5;cx<=1.5;cx+=0.6) for(let cz=-1.5;cz<=1.5;cz+=0.75){
    const crop=makePBRCyl(0.04,0.04,0.4+Math.random()*0.2,4,0x7a9040,0.9);crop.position.set(cx+(Math.random()-0.5)*0.2,0.2,cz);
    const head=makePBRSphere(0.06+Math.random()*0.03,4,0xd4a820,0.8);head.position.y=0.42;crop.add(head);g.add(crop);
  }
  const body=makePBRBox(0.15,0.5,0.15,0x8a7040,0.9);body.position.set(1.5,0.4,1.5);g.add(body);
  const arms=makePBRBox(0.6,0.1,0.1,0x8a7040,0.9);arms.position.set(1.5,0.65,1.5);g.add(arms);
  return g;
}
function buildMesh_Tower(team){
  const g=new THREE.Group();
  const found=makePBRBox(2.4,0.4,2.4,0x8a8070,0.95);found.position.y=0.2;g.add(found);
  const bot=makePBRBox(1.9,2.5,1.9,STONE_C,0.85);bot.position.y=1.65;g.add(bot);
  const mid=makePBRBox(1.7,2.0,1.7,STONE_C+0x050505,0.84);mid.position.y=4.15;g.add(mid);
  const plat=makePBRBox(2.1,0.3,2.1,0x7a7870,0.9);plat.position.y=5.3;g.add(plat);
  for(const [bx,bz] of[[-0.75,0],[0.75,0],[0,-0.75],[0,0.75]]){const b=makePBRBox(0.3,0.5,0.3,0x8a8878,0.9);b.position.set(bx,5.7,bz);g.add(b);}
  for(const [ax,az] of[[0,-0.96],[0,0.96],[-0.96,0],[0.96,0]]){const slit=makePBRBox(0.12,0.55,0.05,0x0a0604,0.99);slit.position.set(ax,3.5,az);g.add(slit);}
  const pole=makePBRCyl(0.03,0.03,1.5,5,0x2a1a08,0.9);pole.position.set(0,6.2,0);g.add(pole);
  const flagC=team===1?0x3344cc:0xcc3333, flagE=team===1?0x2233aa:0xaa2222;
  const flag=makePBRBox(0.45,0.3,0.04,flagC,0.7,0,flagE,0.4);flag.position.set(0.22,6.8,0);g.add(flag);
  return g;
}
function buildMesh_Blacksmith(){
  const g=new THREE.Group();
  const found=makePBRBox(3.2,0.3,2.8,0x8a8070,0.95);found.position.y=0.15;g.add(found);
  const walls=makePBRBox(2.8,2.2,2.4,0x5a5550,0.85);walls.position.y=1.25;g.add(walls);
  const rf=makePBRBox(3,0.18,2.7,0x3a3530,0.9);rf.position.y=2.45;g.add(rf);
  const ch=makePBRBox(0.45,1.4,0.45,0x3a3530,0.88);ch.position.set(0.8,3.05,0);g.add(ch);
  const fireGlow=makePBRBox(0.3,0.3,0.3,0xff5500,0.3,0,0xff4400,1.5);fireGlow.position.set(0.8,3.75,0);g.add(fireGlow);
  const fl=new THREE.PointLight(0xff6600,1.5,6);fl.position.set(0.8,3.8,0);g.add(fl);
  const anvil=makePBRBox(0.5,0.2,0.3,0x2a2820,0.9,0.4);anvil.position.set(-0.3,0.4,0.8);g.add(anvil);
  return g;
}
function buildMesh_Lumbercamp(){
  const g=new THREE.Group();
  const found=makePBRBox(3,0.2,2.5,0x7a6040,0.95);found.position.y=0.1;g.add(found);
  const shed=makePBRBox(2.5,1.8,2,WOOD_C,0.88);shed.position.y=1.05;g.add(shed);
  const rf=makePBRBox(2.7,0.15,2.2,0x5a3810,0.9);rf.position.y=2.0;g.add(rf);
  for(let li=0;li<4;li++){const log=makePBRCyl(0.15,0.18,1.2,7,0x6a4018,0.92);log.rotation.z=Math.PI/2;log.position.set((li-1.5)*0.3,0.18+Math.floor(li/2)*0.3,-1.3);g.add(log);}
  for(let li=0;li<3;li++){const log=makePBRCyl(0.15,0.18,1.2,7,0x7a5020,0.92);log.rotation.z=Math.PI/2;log.position.set((li-1)*0.32,0.48,-1.3);g.add(log);}
  return g;
}
function buildMesh_MiningCamp(){
  const g=new THREE.Group();
  const found=makePBRBox(3,0.2,2.5,0x8a8070,0.95);found.position.y=0.1;g.add(found);
  const shed=makePBRBox(2.3,1.7,2,0x7a7060,0.85);shed.position.y=0.98;g.add(shed);
  const rf=makePBRBox(2.5,0.15,2.2,0x5a5048,0.9);rf.position.y=1.9;g.add(rf);
  const cart=makePBRBox(0.6,0.35,0.4,0x3a3028,0.9);cart.position.set(1.1,0.28,-0.9);g.add(cart);
  for(let i=0;i<5;i++){const r=makePBRSphere(0.2+Math.random()*0.12,5,0x8a8070,0.9);r.scale.y=0.7;r.position.set(-0.8+(Math.random()-0.5)*0.5,0.15,-1+(Math.random()-0.5)*0.5);g.add(r);}
  return g;
}
function buildMesh_Castle(team){
  const g=new THREE.Group();
  const ac=team===1?0x2a4ecc:0xcc2a2a;
  const found=makePBRBox(9,0.45,9,0x8a8070,0.95);found.position.y=0.22;g.add(found);
  const main=makePBRBox(7,4,7,STONE_C,0.85);main.position.y=2.45;g.add(main);
  for(let bx=-3;bx<=3;bx+=1.2) for(const bz of[-3.5,3.5]){const m=makePBRBox(0.5,0.5,0.4,0x8a8878,0.9);m.position.set(bx,4.7,bz);g.add(m);}
  for(let bz=-3;bz<=3;bz+=1.2) for(const bx of[-3.5,3.5]){const m=makePBRBox(0.4,0.5,0.5,0x8a8878,0.9);m.position.set(bx,4.7,bz);g.add(m);}
  for(const [tx,tz] of[[-3,-3],[3,-3],[-3,3],[3,3]]){
    const t=makePBRCyl(0.9,1.0,6.5,10,STONE_C-0x080808,0.85);t.position.set(tx,3.25,tz);g.add(t);
    const cap=makePBRCyl(0,1.1,1.2,10,ac,0.75);cap.position.set(tx,7.1,tz);g.add(cap);
    const tr=makePBRCyl(1.02,1.02,0.4,10,0x7a7870,0.9);tr.position.set(tx,6.5,tz);g.add(tr);
  }
  const keep=makePBRBox(3.5,5.5,3.5,STONE_C+0x050505,0.83);keep.position.y=5.25;g.add(keep);
  const keepCap=makePBRCyl(0,2,1.5,4,ac,0.75);keepCap.position.y=9.0;keepCap.geometry.rotateY(Math.PI/4);g.add(keepCap);
  const gL=makePBRBox(0.45,2.8,0.5,0x8a8070,0.88);gL.position.set(-0.8,1.9,3.5);g.add(gL);
  const gR=gL.clone();gR.position.x=0.8;g.add(gR);
  const gT=makePBRBox(2.2,0.55,0.5,0x8a8070,0.88);gT.position.set(0,3.5,3.5);g.add(gT);
  const port=makePBRBox(1.4,2.4,0.08,0x2a2820,0.9,0.5);port.position.set(0,1.85,3.51);g.add(port);
  const pole=makePBRCyl(0.05,0.05,2.5,5,0x2a1a08,0.9);pole.position.set(0,10.5,0);g.add(pole);
  const flag=makePBRBox(0.9,0.6,0.05,ac,0.7,0,ac,0.5);flag.position.set(0.45,11.2,0);g.add(flag);
  return g;
}
function buildMesh_Market(team){
  const g=new THREE.Group();
  const c=team===1?0xd4a020:0xa02020;
  const found=makePBRBox(4.5,0.25,3.5,0x8a8070,0.95);found.position.y=0.12;g.add(found);
  const walls=makePBRBox(3.8,2,2.8,0xc8a868,0.82);walls.position.y=1.15;g.add(walls);
  const awning=makePBRBox(5,0.12,1.5,c,0.75);awning.position.set(0,2.3,-1.8);g.add(awning);
  const awn2=makePBRBox(0.08,1.5,0.08,0x8a6030,0.9);awn2.position.set(-2.3,1.55,-1.8);g.add(awn2);
  const awn3=awn2.clone();awn3.position.x=2.3;g.add(awn3);
  for(let si=-1;si<=1;si++){const stall=makePBRBox(0.9,0.7,0.5,0xd4a860,0.88);stall.position.set(si*1.0,0.55,1.3);g.add(stall);}
  return g;
}

function spawnBuildingMesh(b){
  let grp;
  switch(b.type){
    case 'Town Center': grp=buildMesh_TownCenter(b.team); break;
    case 'Barracks':    grp=buildMesh_Barracks(b.team);   break;
    case 'House':       grp=buildMesh_House(b.team);      break;
    case 'Farm':        grp=buildMesh_Farm();              break;
    case 'Tower':       grp=buildMesh_Tower(b.team);      break;
    case 'Blacksmith':  grp=buildMesh_Blacksmith();        break;
    case 'Lumbercamp':  grp=buildMesh_Lumbercamp();        break;
    case 'MiningCamp':  grp=buildMesh_MiningCamp();        break;
    case 'Castle':      grp=buildMesh_Castle(b.team);     break;
    case 'Market':      grp=buildMesh_Market(b.team);     break;
    default:            grp=buildMesh_House(b.team);       break;
  }
  const y=getHeight(b.x,b.z)+0.02;
  grp.position.set(b.x,y,b.z);

  // Selection ring
  const sz=b.size||1.5;
  const ring=new THREE.Mesh(new THREE.RingGeometry(sz+0.3,sz+0.7,28),new THREE.MeshBasicMaterial({color:b.team===myTeam?0x5ddb5d:0xff4444,side:THREE.DoubleSide,transparent:true,opacity:0.7}));
  ring.rotation.x=-Math.PI/2;ring.position.y=0.05;ring.visible=false;
  grp.add(ring);
  grp.userData.selRing=ring;

  // HP bar
  const hpBg=new THREE.Mesh(new THREE.PlaneGeometry(sz*1.4,0.18),new THREE.MeshBasicMaterial({color:0x1a1a1a,depthTest:false}));
  hpBg.rotation.x=-Math.PI/2;hpBg.position.set(0,sz*1.8+0.5,0);grp.add(hpBg);
  const hpFg=new THREE.Mesh(new THREE.PlaneGeometry(sz*1.4,0.18),new THREE.MeshBasicMaterial({color:b.team===myTeam?0x4cdd4c:0xee4444,depthTest:false}));
  hpFg.rotation.x=-Math.PI/2;hpFg.position.set(0,sz*1.8+0.52,0);grp.add(hpFg);
  grp.userData.hpFg=hpFg;grp.userData.hpFgWidth=sz*1.4;

  // Construction scaffold: ghost the building mesh + animated wireframe scaffold
  if(b.underConstruction){
    // Ghost all child meshes (low opacity) — visible but clearly unfinished
    grp.traverse(c=>{if(c.isMesh&&c.material){c.material=c.material.clone();c.material.transparent=true;c.material.opacity=0.3;}});
    // Wireframe scaffold box — its scaleY will grow 0→1 as construction advances
    const scafH=Math.max((b.size||1.5)*2, 1.5); // tall enough to be visible over flat buildings
    const scafGeo=new THREE.BoxGeometry(b.size*2+0.3,scafH,b.size*2+0.3);
    const scafMat=new THREE.MeshBasicMaterial({color:0xd4a84b,wireframe:true,transparent:true,opacity:0.7});
    const scaf=new THREE.Mesh(scafGeo,scafMat);
    scaf.position.y=scafH/2;
    scaf.scale.y=0.02; // starts nearly flat, grows to full height
    grp.add(scaf);grp.userData.scaffold=scaf;
    grp.userData.scafH=scafH;
    // Do NOT scale the whole group — flat buildings (Farm etc.) would disappear
  }
  scene.add(grp);
  buildingMeshes[b.id]=grp;
}

// =================================================================
//  UNIT MESHES (exact port from reference)
// =================================================================
function makeUnitMesh_Villager(team){
  const g=new THREE.Group();
  const tc=team===myTeam?'player':'enemy';
  const torso=makePBRBox(0.38,0.55,0.28,tc==='player'?0xd4a870:0xa06050,0.85);torso.position.y=0.52;g.add(torso);
  const tunic=makePBRBox(0.40,0.42,0.30,tc==='player'?0x8aa050:0x9a3030,0.82);tunic.position.y=0.48;g.add(tunic);
  for(const lx of[-0.1,0.1]){const leg=makePBRBox(0.14,0.4,0.16,0x6a4820,0.88);leg.position.set(lx,0.22,0);g.add(leg);}
  const head=makePBRSphere(0.2,8,0xe8c890,0.8);head.position.y=1.0;g.add(head);
  const hat=makePBRCyl(0.08,0.22,0.22,8,tc==='player'?0x4a7040:0x6a3020,0.85);hat.position.y=1.22;g.add(hat);
  for(const ax of[-0.26,0.26]){const arm=makePBRBox(0.12,0.38,0.14,0xd4a870,0.85);arm.position.set(ax,0.58,0);g.add(arm);}
  const tool=makePBRBox(0.06,0.55,0.06,0x5a3010,0.9);tool.position.set(0.34,0.6,0);g.add(tool);
  return g;
}
function makeUnitMesh_Swordsman(team){
  const g=new THREE.Group();
  const mc=team===myTeam?0x2a3880:0x802828;
  const torso=makePBRBox(0.44,0.6,0.34,0x6a6a78,0.3,0.6);torso.position.y=0.56;g.add(torso);
  const coat=makePBRBox(0.46,0.35,0.36,mc,0.75);coat.position.y=0.45;g.add(coat);
  for(const lx of[-0.12,0.12]){const leg=makePBRBox(0.16,0.42,0.18,0x5a5a68,0.4,0.5);leg.position.set(lx,0.23,0);g.add(leg);}
  const helmet=makePBRBox(0.34,0.34,0.36,0x7a7a88,0.3,0.65);helmet.position.y=1.06;g.add(helmet);
  const visor=makePBRBox(0.22,0.12,0.08,0x1a1a22,0.4,0.5);visor.position.set(0,1.04,0.2);g.add(visor);
  const hilt=makePBRBox(0.22,0.06,0.06,0x8a6030,0.5,0.4);hilt.position.set(0.38,0.8,0);g.add(hilt);
  const blade=makePBRBox(0.05,0.65,0.05,0xe0e0f0,0.2,0.8);blade.position.set(0.38,1.23,0);g.add(blade);
  const shield=makePBRBox(0.32,0.45,0.06,mc,0.7);shield.material.emissive=new THREE.Color(mc);shield.material.emissiveIntensity=0.08;shield.position.set(-0.38,0.72,0.08);g.add(shield);
  const boss=makePBRSphere(0.06,5,0xd4a820,0.3,0.6);boss.position.set(-0.38,0.72,0.14);g.add(boss);
  return g;
}
function makeUnitMesh_Archer(team){
  const g=new THREE.Group();
  const mc=team===myTeam?0x2a5a30:0x5a2a20;
  const torso=makePBRBox(0.40,0.58,0.30,0x6a5030,0.85);torso.position.y=0.55;g.add(torso);
  const hood=makePBRBox(0.38,0.3,0.32,mc,0.8);hood.position.y=0.72;g.add(hood);
  for(const lx of[-0.10,0.10]){const leg=makePBRBox(0.14,0.40,0.16,0x5a4020,0.85);leg.position.set(lx,0.22,0);g.add(leg);}
  const head=makePBRSphere(0.19,8,0xe0c090,0.8);head.position.y=1.0;g.add(head);
  const cap=makePBRCyl(0.08,0.2,0.18,8,mc,0.85);cap.position.y=1.2;g.add(cap);
  const bow=makePBRBox(0.05,0.75,0.05,0x6a3808,0.9);bow.position.set(0.36,0.85,0);g.add(bow);
  const bowStr=makePBRBox(0.02,0.7,0.02,0xd0c0a0,0.8);bowStr.position.set(0.34,0.85,0.04);g.add(bowStr);
  const quiver=makePBRCyl(0.06,0.07,0.35,6,0x5a3808,0.85);quiver.position.set(-0.22,0.7,-0.18);g.add(quiver);
  return g;
}
function makeUnitMesh_Knight(team){
  const g=new THREE.Group();
  const mc=team===myTeam?0x1a2a70:0x701a1a;
  const hBody=makePBRBox(0.65,0.55,1.3,0x5a3818,0.8);hBody.position.y=0.6;g.add(hBody);
  const hNeck=makePBRBox(0.3,0.5,0.35,0x5a3818,0.8);hNeck.position.set(0,0.9,-0.65);g.add(hNeck);
  const hHead=makePBRBox(0.25,0.32,0.45,0x4a2e10,0.8);hHead.position.set(0,1.1,-0.95);g.add(hHead);
  for(const [lx,lz] of[[-0.25,-0.35],[-0.25,0.35],[0.25,-0.35],[0.25,0.35]]){const leg=makePBRBox(0.14,0.55,0.14,0x4a2e10,0.82);leg.position.set(lx,0.28,lz);g.add(leg);}
  const torso=makePBRBox(0.44,0.55,0.34,0x7a7a88,0.35,0.6);torso.position.y=1.42;g.add(torso);
  const surcoat=makePBRBox(0.46,0.35,0.36,mc,0.72);surcoat.position.y=1.3;g.add(surcoat);
  const helm=makePBRBox(0.34,0.34,0.36,0x8a8a98,0.25,0.7);helm.position.y=1.92;g.add(helm);
  const lance=makePBRCyl(0.04,0.04,2.0,5,0x7a5020,0.85);lance.rotation.z=Math.PI/2;lance.position.set(1.2,1.6,-0.2);g.add(lance);
  const tip=makePBRBox(0.05,0.12,0.05,0xe0e0f0,0.2,0.9);tip.position.set(2.1,1.6,-0.2);g.add(tip);
  return g;
}
function makeUnitMesh_Catapult(team){
  const g=new THREE.Group();
  const mc=team===myTeam?0x3a5a20:0x5a2020;
  const base=makePBRBox(0.9,0.38,1.6,0x6a4818,0.88);base.position.y=0.44;g.add(base);
  for(const [wx,wz] of[[-0.55,-0.6],[-0.55,0.6],[0.55,-0.6],[0.55,0.6]]){
    const wheel=makePBRCyl(0.32,0.32,0.12,12,0x3a2808,0.9);wheel.rotation.z=Math.PI/2;wheel.position.set(wx,0.34,wz);g.add(wheel);
    const spoke=makePBRBox(0.55,0.05,0.05,0x5a3a10,0.88);spoke.rotation.z=Math.PI/2;spoke.position.set(wx,0.34,wz);g.add(spoke);
  }
  const arm=makePBRBox(0.1,1.4,0.1,0x5a3010,0.88);arm.position.set(0,1.3,0);g.add(arm);
  const cw=makePBRBox(0.35,0.35,0.35,0x3a2808,0.9);cw.position.set(0,0.7,0.5);g.add(cw);
  const cup=makePBRSphere(0.18,6,0x5a3010,0.88);cup.position.set(0,2.15,-0.2);g.add(cup);
  const rock=makePBRSphere(0.12,5,0x7a7060,0.9);rock.position.set(0,2.35,-0.2);g.add(rock);
  const stripe=makePBRBox(0.92,0.12,0.12,mc,0.7,0,mc,0.2);stripe.position.y=0.62;g.add(stripe);
  return g;
}
function makeUnitMesh_Scout(team){
  const g=new THREE.Group();
  const mc=team===myTeam?0x208060:0x806020;
  const hBody=makePBRBox(0.55,0.45,1.1,0x7a5028,0.8);hBody.position.y=0.55;g.add(hBody);
  const hNeck=makePBRBox(0.25,0.42,0.3,0x7a5028,0.8);hNeck.position.set(0,0.82,-0.55);g.add(hNeck);
  const hHead=makePBRBox(0.2,0.28,0.38,0x6a4018,0.8);hHead.position.set(0,0.98,-0.82);g.add(hHead);
  for(const [lx,lz] of[[-0.22,-0.3],[-0.22,0.3],[0.22,-0.3],[0.22,0.3]]){const leg=makePBRBox(0.11,0.5,0.11,0x6a4018,0.82);leg.position.set(lx,0.25,lz);g.add(leg);}
  const torso=makePBRBox(0.38,0.48,0.28,0x4a3018,0.85);torso.position.y=1.3;g.add(torso);
  const cloak=makePBRBox(0.42,0.42,0.1,mc,0.78);cloak.position.set(0,1.28,-0.14);g.add(cloak);
  const head=makePBRSphere(0.19,8,0xe0c090,0.8);head.position.y=1.78;g.add(head);
  const hood=makePBRCyl(0.1,0.2,0.18,8,mc,0.8);hood.position.y=1.9;g.add(hood);
  const horn=makePBRCyl(0.03,0.06,0.28,6,0xd4a820,0.4,0.6);horn.rotation.z=Math.PI/3;horn.position.set(0.32,1.45,-0.05);g.add(horn);
  return g;
}

function spawnUnitMesh(u){
  let grp;
  switch(u.type){
    case 'Villager':  grp=makeUnitMesh_Villager(u.team);  break;
    case 'Swordsman': grp=makeUnitMesh_Swordsman(u.team); break;
    case 'Archer':    grp=makeUnitMesh_Archer(u.team);    break;
    case 'Knight':    grp=makeUnitMesh_Knight(u.team);    break;
    case 'Catapult':  grp=makeUnitMesh_Catapult(u.team);  break;
    default:          grp=makeUnitMesh_Scout(u.team);     break;
  }
  // Selection ring
  const selRing=new THREE.Mesh(new THREE.RingGeometry(0.65,0.85,18),new THREE.MeshBasicMaterial({color:u.team===myTeam?0x5ddb5d:0xff4444,side:THREE.DoubleSide,transparent:true,opacity:0.8}));
  selRing.rotation.x=-Math.PI/2;selRing.position.y=0.02;selRing.visible=false;
  grp.add(selRing);grp.userData.selRing=selRing;

  // HP bar
  const hpBg=new THREE.Mesh(new THREE.PlaneGeometry(0.8,0.11),new THREE.MeshBasicMaterial({color:0x1a1a1a,depthTest:false}));
  hpBg.rotation.x=-Math.PI/2;hpBg.position.set(0,1.9,0);grp.add(hpBg);
  const hpFg=new THREE.Mesh(new THREE.PlaneGeometry(0.8,0.11),new THREE.MeshBasicMaterial({color:u.team===myTeam?0x4cdd4c:0xee4444,depthTest:false}));
  hpFg.rotation.x=-Math.PI/2;hpFg.position.set(0,1.92,0);grp.add(hpFg);
  grp.userData.hpFg=hpFg;grp.userData.hpFgWidth=0.8;

  const y=getHeight(u.x,u.z);
  grp.position.set(u.x,y,u.z);
  scene.add(grp);
  unitMeshes[u.id]=grp;
}

// =================================================================
//  MINIMAP
// =================================================================
function bakeMinimap(){
  const imgd=mmX.createImageData(150,118);
  for(let py=0;py<118;py++) for(let px=0;px<150;px++){
    const wx=(px/150)*MAP-HALF, wz=(py/118)*MAP-HALF;
    const h=getHeight(wx,wz);
    const i=(py*150+px)*4;
    if(h<WATER_LEVEL){
      const depth=Math.max(0,Math.min(1,(-h-1.3)/3));
      imgd.data[i]=Math.round(20+depth*10);imgd.data[i+1]=Math.round(55+depth*15);imgd.data[i+2]=Math.round(110+depth*30);
    } else if(h<-0.6){                 // sandy shallows
      imgd.data[i]=158;imgd.data[i+1]=143;imgd.data[i+2]=97;
    } else {
      const sl=Math.abs(h);
      if(sl>3.2){                      // bare rock
        imgd.data[i]=130;imgd.data[i+1]=115;imgd.data[i+2]=80;
      } else if(sl>1.8){               // rocky grass
        imgd.data[i]=100;imgd.data[i+1]=112;imgd.data[i+2]=60;
      } else {                         // lush grass
        imgd.data[i]=Math.round((0.25+sl*0.03)*255);
        imgd.data[i+1]=Math.round((0.47-sl*0.01)*255);
        imgd.data[i+2]=Math.round(0.17*255);
      }
    }
    imgd.data[i+3]=255;
  }
  mmTerrainImg=imgd;
}
function drawMinimap(){
  if(!mmTerrainImg) return;
  mmX.putImageData(mmTerrainImg,0,0);
  const sx=x=>(x+HALF)/MAP*150, sz=z=>(z+HALF)/MAP*118;
  // Resources
  for(const rn of serverResNodes){
    if(fowCell(rn.x,rn.z)===0) continue;
    mmX.fillStyle=rn.type==='gold'?'#ffd700':rn.type==='stone'?'#aaa8a0':rn.type==='wood'?'#2a6010':'#dd5050';
    mmX.fillRect(sx(rn.x)-2,sz(rn.z)-2,4,4);
  }
  // Buildings
  for(const id in serverBuildings){
    const b=serverBuildings[id];
    if(b.team!==myTeam&&fowCell(b.x,b.z)===0) continue;
    mmX.fillStyle=b.team===myTeam?'#4488ff':'#ff4422';
    const s=b.size*3;mmX.fillRect(sx(b.x)-s/2,sz(b.z)-s/2,s,s);
  }
  // Units
  for(const id in serverUnits){
    const u=serverUnits[id];
    if(u.team!==myTeam&&fowCell(u.x,u.z)!==2) continue;
    mmX.fillStyle=u.team===myTeam?'#88ff66':'#ff6644';
    mmX.fillRect(sx(u.x)-1.5,sz(u.z)-1.5,3,3);
  }
  drawMinimapFOW();
  mmX.strokeStyle='rgba(255,255,255,0.55)';mmX.lineWidth=1;
  mmX.strokeRect(sx(camTarget.x)-22,sz(camTarget.z)-17,44,34);
}

// =================================================================
//  CAMERA
// =================================================================
function initCamera(){
  camTarget=new THREE.Vector3(P_OX,0,P_OZ);
  document.addEventListener('keydown',e=>{keys[e.key.toLowerCase()]=true;onKeyDown(e);});
  document.addEventListener('keyup',e=>{keys[e.key.toLowerCase()]=false;});
  window.addEventListener('wheel',e=>{camDist=Math.max(10,Math.min(65,camDist+e.deltaY*0.04));});
}
// Smooth camera pan — velocity-based with friction so movement
// accelerates on key-hold and decelerates on key-release with no lerp jitter.
let _camVX=0,_camVZ=0;
function tickCamera(dt){
  const ACCEL=60, FRICTION=12, MAX_SPD=28;
  const rightX=Math.cos(camYaw),rightZ=-Math.sin(camYaw);
  const fwdX=Math.sin(camYaw),fwdZ=Math.cos(camYaw);

  let ax=0,az=0;
  if(keys['arrowleft'] ||keys['a']){ax-=rightX;az-=rightZ;}
  if(keys['arrowright']||keys['d']){ax+=rightX;az+=rightZ;}
  if(keys['arrowup']  ||keys['w']){ax-=fwdX;  az-=fwdZ;}
  if(keys['arrowdown'] ||keys['s']){ax+=fwdX;  az+=fwdZ;}

  const moving=ax!==0||az!==0;
  if(moving){
    _camVX+=ax*ACCEL*dt;
    _camVZ+=az*ACCEL*dt;
    // Clamp to max speed
    const spd=Math.sqrt(_camVX*_camVX+_camVZ*_camVZ);
    if(spd>MAX_SPD){_camVX=_camVX/spd*MAX_SPD;_camVZ=_camVZ/spd*MAX_SPD;}
  } else {
    // Friction — exponential decay, frame-rate independent
    const decay=Math.exp(-FRICTION*dt);
    _camVX*=decay;
    _camVZ*=decay;
    if(Math.abs(_camVX)<0.001)_camVX=0;
    if(Math.abs(_camVZ)<0.001)_camVZ=0;
  }

  if(keys['q'])camYaw-=dt*0.8;
  if(keys['e'])camYaw+=dt*0.8;

  camTarget.x+=_camVX*dt;
  camTarget.z+=_camVZ*dt;
  camTarget.x=Math.max(-HALF+5,Math.min(HALF-5,camTarget.x));
  camTarget.z=Math.max(-HALF+5,Math.min(HALF-5,camTarget.z));

  // Place camera directly — no lerp, no lag, no jitter
  camera.position.x=camTarget.x+Math.sin(camYaw)*camDist;
  camera.position.z=camTarget.z+Math.cos(camYaw)*camDist;
  camera.position.y=camDist*0.88;
  camera.lookAt(camTarget.x,0,camTarget.z);
}

// =================================================================
//  MOUSE / SELECTION
// =================================================================
const ray=new THREE.Raycaster();
const mpos=new THREE.Vector2();
let isDrag=false,dragS={x:0,y:0};
const selBox=document.getElementById('selbox');

function setupMouse(){
  const canvas=document.getElementById('canvas');
  canvas.addEventListener('mousedown',e=>{
    if(e.button===0){if(ghostState)return;isDrag=true;dragS={x:e.clientX,y:e.clientY};}
    if(e.button===2){e.preventDefault();if(ghostState){cancelBuildMode();return;}handleRMB(e);}
  });
  canvas.addEventListener('mousemove',e=>{
    if(ghostState){
      const wp=getWorldClick(e);
      if(wp){
        ghostState.mesh.position.x=wp.x;ghostState.mesh.position.z=wp.z;
        ghostState.mesh.position.y=getHeight(wp.x,wp.z)+ghostState.size*0.5;
        ghostState.mesh.material.color.set(isWater(wp.x,wp.z)?0xff3333:0x44ff88);
      }return;
    }
    if(!isDrag)return;
    const dx=e.clientX-dragS.x,dy=e.clientY-dragS.y;
    if(Math.abs(dx)>5||Math.abs(dy)>5){
      selBox.style.display='block';
      const x=Math.min(e.clientX,dragS.x),y=Math.min(e.clientY,dragS.y);
      selBox.style.left=x+'px';selBox.style.top=y+'px';
      selBox.style.width=Math.abs(dx)+'px';selBox.style.height=Math.abs(dy)+'px';
    }
  });
  canvas.addEventListener('mouseup',e=>{
    if(e.button!==0)return;
    selBox.style.display='none';
    if(ghostState){const wp=getWorldClick(e);if(wp)commitBuild(wp.x,wp.z);return;}
    const dx=e.clientX-dragS.x,dy=e.clientY-dragS.y;
    if(Math.abs(dx)<6&&Math.abs(dy)<6)handleLMBClick(e);
    else handleDragSel(dragS,{x:e.clientX,y:e.clientY});
    isDrag=false;
  });
  canvas.addEventListener('contextmenu',e=>e.preventDefault());
  document.getElementById('minimap').addEventListener('click',e=>{
    const r=e.target.getBoundingClientRect();
    const wx=((e.clientX-r.left)/150)*MAP-HALF;
    const wz=((e.clientY-r.top)/118)*MAP-HALF;
    // If units are selected, issue a move command to the clicked world position
    if(gameStarted&&selectedUnitIds.length>0){
      socket.emit('cmd',{type:'move',unitIds:selectedUnitIds,x:wx,z:wz});
      spawnClickMark(wx,wz);
    }
    // Always pan the camera to the clicked location
    camTarget.x=wx;
    camTarget.z=wz;
  });
}

function getWorldClick(e){
  mpos.set((e.clientX/innerWidth)*2-1,-(e.clientY/innerHeight)*2+1);
  ray.setFromCamera(mpos,camera);
  if(terrain){const hits=ray.intersectObject(terrain,false);if(hits.length>0)return hits[0].point;}
  const pl=new THREE.Plane(new THREE.Vector3(0,1,0),0);
  const v=new THREE.Vector3();ray.ray.intersectPlane(pl,v);return v;
}

function handleLMBClick(e){
  if(!gameStarted)return;
  mpos.set((e.clientX/innerWidth)*2-1,-(e.clientY/innerHeight)*2+1);
  ray.setFromCamera(mpos,camera);
  let hit=false;
  for(const id in unitMeshes){
    const u=serverUnits[id];if(!u||u.team!==myTeam)continue;
    const b3=new THREE.Box3().setFromObject(unitMeshes[id]);b3.expandByScalar(0.3);
    if(ray.ray.intersectsBox(b3)){if(!e.shiftKey)deselAll();selUnit(id);hit=true;break;}
  }
  if(!hit){
    for(const id in buildingMeshes){
      const b=serverBuildings[id];if(!b||b.team!==myTeam)continue;
      const b3=new THREE.Box3().setFromObject(buildingMeshes[id]);
      if(ray.ray.intersectsBox(b3)){if(!e.shiftKey)deselAll();selBuilding(id);hit=true;break;}
    }
  }
  // Check resource nodes (visible ones only)
  if(!hit){
    for(const rn of serverResNodes){
      const mesh=resNodeMeshes[rn.id];
      if(!mesh||!mesh.visible)continue;
      const b3=new THREE.Box3().setFromObject(mesh);b3.expandByScalar(0.4);
      if(ray.ray.intersectsBox(b3)){
        if(!e.shiftKey)deselAll();
        selectedResNodeId=rn.id;
        refreshSelUI();
        hit=true;break;
      }
    }
  }
  if(!hit&&!e.shiftKey)deselAll();
}

function handleDragSel(s,e2){
  const ndcX1=Math.min(s.x,e2.x)/innerWidth*2-1;
  const ndcX2=Math.max(s.x,e2.x)/innerWidth*2-1;
  const ndcY1=-(Math.max(s.y,e2.y)/innerHeight*2-1);
  const ndcY2=-(Math.min(s.y,e2.y)/innerHeight*2-1);
  deselAll();
  for(const id in unitMeshes){
    const u=serverUnits[id];if(!u||u.team!==myTeam)continue;
    const p=unitMeshes[id].position.clone().project(camera);
    if(p.x>=ndcX1&&p.x<=ndcX2&&p.y>=ndcY1&&p.y<=ndcY2)selUnit(id);
  }
}

function handleRMB(e){
  if(!gameStarted)return;

  // ── Rally point: RMB anywhere on ground while a building is selected ─────
  if(selectedBuildingId&&selectedUnitIds.length===0){
    const b=serverBuildings[selectedBuildingId];
    if(b&&b.team===myTeam){
      const wp=getWorldClick(e);if(!wp)return;
      // Check if RMB landed on a visible resource node
      let rnId=null;
      for(const rn of serverResNodes){
        if(rn.amount<=0)continue;
        const mesh=resNodeMeshes[rn.id];
        if(!mesh||!mesh.visible)continue;
        if(Math.sqrt((rn.x-wp.x)**2+(rn.z-wp.z)**2)<(rn.type==='wood'?1.8:2.2)){rnId=rn.id;break;}
      }
      socket.emit('cmd',{type:'setRally',buildingId:selectedBuildingId,x:wp.x,z:wp.z,resourceId:rnId});
      // Optimistically update local copy so the line redraws immediately
      const lb=serverBuildings[selectedBuildingId];
      if(lb){lb.rallyX=wp.x;lb.rallyZ=wp.z;lb.rallyResourceId=rnId;}
      drawRallyIndicator(selectedBuildingId);
      spawnClickMark(wp.x,wp.z);
      return;
    }
  }

  if(selectedUnitIds.length===0)return;
  const wp=getWorldClick(e);if(!wp)return;
  const tx=wp.x,tz=wp.z;

  // ── Resume construction: RMB on a friendly under-construction building ──
  // Check this before anything else so it takes priority over move
  const vids=selectedUnitIds.filter(id=>serverUnits[id]?.type==='Villager');
  if(vids.length){
    for(const id in serverBuildings){
      const b=serverBuildings[id];
      if(!b||b.team!==myTeam||!b.underConstruction)continue;
      if(Math.sqrt((b.x-tx)**2+(b.z-tz)**2)<(b.size||1.5)+2.5){
        socket.emit('cmd',{type:'resume_build',unitIds:vids,buildingId:id});
        spawnClickMark(tx,tz);
        return;
      }
    }
  }

  // Attack enemy unit?
  let eUnitId=null;
  for(const id in serverUnits){
    const u=serverUnits[id];
    if(!u||u.team===myTeam)continue;
    if(Math.sqrt((u.x-tx)**2+(u.z-tz)**2)<1.8){eUnitId=id;break;}
  }
  // Enemy building?
  let eBldId=null;
  if(!eUnitId) for(const id in serverBuildings){
    const b=serverBuildings[id];if(!b||b.team===myTeam)continue;
    if(Math.sqrt((b.x-tx)**2+(b.z-tz)**2)<(b.size||1.5)+1.5){eBldId=id;break;}
  }
  // Resource node?
  let rNodeId=null;
  if(!eUnitId&&!eBldId){
    for(const rn of serverResNodes){
      if(rn.amount>0&&Math.sqrt((rn.x-tx)**2+(rn.z-tz)**2)<2.0){rNodeId=rn.id;break;}
    }
  }
  if(eUnitId) socket.emit('cmd',{type:'attack',unitIds:selectedUnitIds,targetId:eUnitId});
  else if(eBldId) socket.emit('cmd',{type:'attack',unitIds:selectedUnitIds,targetId:eBldId});
  else if(rNodeId){
    if(vids.length) socket.emit('cmd',{type:'gather',unitIds:vids,resourceId:rNodeId});
  }
  else socket.emit('cmd',{type:'move',unitIds:selectedUnitIds,x:tx,z:tz});
  spawnClickMark(tx,tz);
}

function spawnClickMark(x,z){
  const ring=new THREE.Mesh(new THREE.RingGeometry(0.2,0.45,14),new THREE.MeshBasicMaterial({color:0x7ddc5e,side:THREE.DoubleSide,transparent:true,opacity:1}));
  ring.rotation.x=-Math.PI/2;ring.position.set(x,getHeight(x,z)+0.1,z);
  scene.add(ring);particlePool.push({mesh:ring,life:1,type:'mark'});
}

function deselAll(){
  for(const id of selectedUnitIds){const m=unitMeshes[id];if(m&&m.userData.selRing)m.userData.selRing.visible=false;}
  selectedUnitIds=[];
  if(selectedBuildingId){const m=buildingMeshes[selectedBuildingId];if(m&&m.userData.selRing)m.userData.selRing.visible=false;selectedBuildingId=null;}
  selectedResNodeId=null;
  clearRallyIndicator();
  refreshSelUI();
}
function selUnit(id){
  if(selectedUnitIds.includes(id))return;
  if(selectedBuildingId){const m=buildingMeshes[selectedBuildingId];if(m&&m.userData.selRing)m.userData.selRing.visible=false;selectedBuildingId=null;}
  selectedUnitIds.push(id);
  const m=unitMeshes[id];if(m&&m.userData.selRing)m.userData.selRing.visible=true;
  refreshSelUI();
}
function selBuilding(id){
  deselAll();selectedBuildingId=id;
  const m=buildingMeshes[id];if(m&&m.userData.selRing)m.userData.selRing.visible=true;
  drawRallyIndicator(id);
  refreshSelUI();
}

// =================================================================
//  RALLY POINT INDICATOR
// =================================================================
function clearRallyIndicator(){
  if(_rallyLine){scene.remove(_rallyLine);_rallyLine.geometry.dispose();_rallyLine=null;}
  if(_rallyFlag){scene.remove(_rallyFlag);_rallyFlag=null;}
}
function drawRallyIndicator(buildingId){
  clearRallyIndicator();
  const b=serverBuildings[buildingId];
  if(!b||b.rallyX===null||b.rallyZ===null) return;
  if(b.team!==myTeam) return;

  const bx=b.x, by=getHeight(b.x,b.z)+0.3, bz=b.z;
  const rx=b.rallyX, ry=getHeight(b.rallyX,b.rallyZ)+0.3, rz=b.rallyZ;

  // Colour: yellow for move rally, green for resource rally
  const isResourceRally=b.rallyResourceId!=null;
  const rallyColor=isResourceRally?0x44dd88:0xffdd44;

  // Dashed line — alternating segments between building and rally point
  const points=[];
  const SEGS=20;
  for(let i=0;i<=SEGS;i++){
    const t=i/SEGS;
    // Skip every other segment to create dashes
    if(Math.floor(i/2)*2!==i&&i>0) continue;
    points.push(new THREE.Vector3(bx+(rx-bx)*t, by+(ry-by)*t, bz+(rz-bz)*t));
    if(i<SEGS){
      const t2=Math.min(1,(i+0.7)/SEGS);
      points.push(new THREE.Vector3(bx+(rx-bx)*t2, by+(ry-by)*t2, bz+(rz-bz)*t2));
    }
  }
  const lineGeo=new THREE.BufferGeometry().setFromPoints(points);
  const lineMat=new THREE.LineBasicMaterial({color:rallyColor,transparent:true,opacity:0.85,depthTest:false});
  _rallyLine=new THREE.LineSegments(lineGeo,lineMat);
  scene.add(_rallyLine);

  // Small flag/diamond marker at rally point
  const flagGeo=new THREE.ConeGeometry(0.35,0.7,4);
  const flagMat=new THREE.MeshBasicMaterial({color:rallyColor,transparent:true,opacity:0.9,depthTest:false});
  _rallyFlag=new THREE.Mesh(flagGeo,flagMat);
  _rallyFlag.position.set(rx,ry+0.35,rz);
  _rallyFlag.rotation.y=Math.PI/4;
  scene.add(_rallyFlag);
}

// =================================================================
//  GAME STATE SYNC
// =================================================================
function syncGameState(state){
  const{units,buildings,teams,resNodes,projPool,events,gameTime:gt}=state;
  gameTime=gt||gameTime;

  // ─ Teams ─
  serverTeams=teams||{};
  const myT=serverTeams[myTeam]||{};
  const enemyTeam=myTeam===1?2:1;
  const enemyT=serverTeams[enemyTeam]||{};
  updateResUI(myT);
  updateAIPanel(enemyT);

  // ─ Resource nodes delta — server now sends only {id,amount} each tick.
  // Merge into serverResNodes; static fields (x,z,type,maxAmount,isTree,variety)
  // were set once on game start and are preserved here.
  if(resNodes&&resNodes.length>0){
    if(resNodes[0].x!==undefined){
      // Full node data (game start) — replace entirely
      serverResNodes=resNodes;
    } else {
      // Delta — only amount changed, update in place
      const deltaMap={};for(const d of resNodes) deltaMap[d.id]=d.amount;
      serverResNodes=serverResNodes.filter(r=>{
        if(deltaMap[r.id]!==undefined){r.amount=deltaMap[r.id];return true;}
        return false; // depleted (not in delta) — remove
      });
    }
  } else if(resNodes&&resNodes.length===0){
    serverResNodes=[];
  }
  if(selectedResNodeId&&!serverResNodes.find(r=>r.id===selectedResNodeId)){selectedResNodeId=null;refreshSelUI();}
  for(const rn of serverResNodes){
    if(!resNodeMeshes[rn.id])makeResNodeMesh(rn);
    const mesh=resNodeMeshes[rn.id];
    if(mesh){
      const pct=Math.max(0.08,rn.amount/rn.maxAmount);
      if(rn.type==='wood'){
        // Trees shrink as they're chopped — Y scale reduces more than XZ to simulate felling
        mesh.scale.set(pct*mesh.userData.baseScale||pct, pct*mesh.userData.baseScale||pct, pct*mesh.userData.baseScale||pct);
      } else {
        mesh.scale.set(pct,pct,pct);
      }
    }
  }

  // ─ Units ─
  // Step 1: merge sparse delta into serverUnits FIRST so serverUnits is always
  // the full live picture. Delta only contains units that changed this tick.
  for(const id in units) serverUnits[id]=units[id];

  // Step 2: death detection — server stops sending a unit when it dies.
  // The server also prunes dead units from its own map, so after a few ticks
  // a dead unit simply disappears from every delta. We detect death by tracking
  // which ids the server has ever acknowledged; once absent from several consecutive
  // deltas we consider it dead. Simple approach: server sends explicit dead flag
  // OR unit vanishes from delta AND has no mesh yet — but the safest approach
  // is to only remove meshes for units the server explicitly marks dead (dead:true)
  // OR that have been absent from ALL deltas for >1s (stale).
  // Since our delta skips unchanged units, we can't use "absent = dead".
  // Instead: server sets unit.dead=true in the delta when a unit dies this tick,
  // and we check for that here.
  for(const id in unitMeshes){
    const u=serverUnits[id];
    // Remove mesh if unit is explicitly dead OR no longer tracked at all
    if(!u||u.dead===true){
      if(buildingMeshes[id])continue;
      spawnDeathFX(unitMeshes[id].position,u?.team||serverUnits[id]?.team||1);
      scene.remove(unitMeshes[id]);delete unitMeshes[id];
      delete interpFrom[id];delete interpTo[id];
      delete serverUnits[id];
      selectedUnitIds=selectedUnitIds.filter(x=>x!==id);
    }
  }

  // Step 3: spawn meshes for any unit we know about but haven't rendered yet
  for(const id in serverUnits){
    const u=serverUnits[id];
    if(!u||u.dead)continue;
    if(!unitMeshes[id]){
      spawnUnitMesh(u);
      const mesh=unitMeshes[id];
      if(mesh){mesh.position.x=u.x;mesh.position.z=u.z;mesh.position.y=getHeight(u.x,u.z);}
      interpFrom[id]={x:u.x,z:u.z};interpTo[id]={x:u.x,z:u.z};continue;
    }
    // Step 4: update interpolation targets for units that changed this tick
    if(!units[id]) continue; // not in delta this tick — skip, keep last interp target
    const mesh=unitMeshes[id];
    interpFrom[id]={x:mesh.position.x,z:mesh.position.z};
    interpTo[id]={x:u.x,z:u.z};
    const hpFg=mesh.userData.hpFg;
    if(hpFg){const pct=u.hp/u.maxHp;hpFg.scale.x=Math.max(0.01,pct);hpFg.position.x=-(mesh.userData.hpFgWidth/2)*(1-pct);hpFg.material.color.set(pct>0.6?0x4cdd4c:pct>0.3?0xffaa20:0xee3030);}
    if(u.state==='moving'||u.state==='moving_to_attack'||u.state==='attacking'){
      const dx=u.tx-u.x,dz=u.tz-u.z;
      if(Math.abs(dx)+Math.abs(dz)>0.1)mesh.rotation.y=Math.atan2(dx,dz);
    }
  }
  interpT=0;

  // ─ Buildings ─
  // Merge delta into serverBuildings; handle dead:true as an explicit removal signal
  for(const id in buildings){
    const b=buildings[id];
    if(b.dead){
      // Building was destroyed this tick — fire death effect and remove mesh
      if(buildingMeshes[id]){
        spawnDeathFX(buildingMeshes[id].position,serverBuildings[id]?.team||1);
        scene.remove(buildingMeshes[id]);delete buildingMeshes[id];
        if(selectedBuildingId===id){selectedBuildingId=null;refreshSelUI();}
      }
      delete serverBuildings[id];
    } else {
      // Live building — update serverBuildings and sync mesh
      serverBuildings[id]=b;
      if(!buildingMeshes[id])spawnBuildingMesh(b);
      const mesh=buildingMeshes[id];if(!mesh)continue;
      // Construction animation
      if(b.underConstruction&&b.buildTime>0){
        const pct=Math.max(0.02,b.buildProgress/b.buildTime);
        if(mesh.userData.scaffold){
          mesh.userData.scaffold.scale.y=pct;
          const scafH=mesh.userData.scafH||3;
          mesh.userData.scaffold.position.y=(scafH/2)*pct;
        }
      } else if(!b.underConstruction&&mesh.userData.scaffold&&mesh.userData.scaffold.visible){
        mesh.userData.scaffold.visible=false;
        mesh.traverse(c=>{if(c.isMesh&&c.material&&c.material.opacity<1){c.material.opacity=1;c.material.transparent=false;}});
      }
      const hpFg=mesh.userData.hpFg;
      if(hpFg){const pct=b.hp/b.maxHp;hpFg.scale.x=Math.max(0.01,pct);hpFg.position.x=-(mesh.userData.hpFgWidth/2)*(1-pct);hpFg.material.color.set(b.underConstruction?0xd4a84b:pct>0.6?0x4cdd4c:pct>0.3?0xffaa20:0xee3030);if(!b.underConstruction&&pct<0.4&&Math.random()<0.02)spawnSmoke(mesh.position);}
      // Redraw rally indicator if this is the selected building and rally changed
      if(id===selectedBuildingId) drawRallyIndicator(id);
    }
  }
  // Remove meshes for any building the server no longer tracks at all
  // (handles edge cases like joining mid-game after a building was already gone)
  for(const id in buildingMeshes){
    if(!serverBuildings[id]){
      scene.remove(buildingMeshes[id]);delete buildingMeshes[id];
      if(selectedBuildingId===id){selectedBuildingId=null;refreshSelUI();}
    }
  }

  // ─ Projectiles ─
  const activeProjIds=new Set((projPool||[]).map(p=>p.id).filter(Boolean));
  for(const id in _clientProjs){
    if(!activeProjIds.has(id)){if(_clientProjs[id].mesh)_clientProjs[id].mesh.visible=false;delete _clientProjs[id];}
  }
  if(projPool)for(const p of projPool){
    if(!p.id)continue;
    if(!_clientProjs[p.id]){
      const mesh=_acquireProjMesh(p.color);
      const elapsed=(p.maxLife||1.8)-p.life;
      _clientProjs[p.id]={fx:p.fx,fy:p.fy||1,fz:p.fz,tx:p.tx,ty:p.ty||1,tz:p.tz,maxLife:p.maxLife||1.8,elapsed,mesh};
    }
  }

  // ─ Events ─
  if(events)for(const ev of events){
    if(ev.type==='gather'&&ev.team===myTeam){spawnResGainPopupFromTeam(ev.carry);}
    else if(ev.type==='farm_income'&&ev.team===myTeam){spawnResGainPopupAtWorld({[ev.res]:ev.amt},ev.x,ev.z);}
    else if(ev.msg)logEv(ev.msg,ev.type||'info');
    else if(ev.type==='trained'&&ev.team===myTeam)alert2(`${ev.unitType} ready!`);
    else if(ev.type==='combat'){}
  }

}

// =================================================================
//  UI — Resources
// =================================================================
function updateResUI(t){
  if(!t)t=serverTeams[myTeam]||{};
  const lo=v=>v<30;
  const el=(id,v)=>{const e=document.getElementById(id);if(!e)return;e.textContent=Math.floor(v||0);e.className='rv'+(lo(v)?' low':'');};
  el('r-food',t.food);el('r-wood',t.wood);el('r-gold',t.gold);el('r-stone',t.stone);
  const pop=document.getElementById('r-pop');if(pop)pop.textContent=`${t.population||0}/${t.maxPop||10}`;
  const score=document.getElementById('r-score');if(score)score.textContent=Math.floor(t.score||0);
  // Age badge
  const ageNames=['DARK AGE','FEUDAL AGE','CASTLE AGE','IMPERIAL AGE'];
  const ageIcons=['🏚','⚔','🏰','👑'];
  const an=document.getElementById('age-name'),ai=document.getElementById('age-icon');
  if(an)an.textContent=ageNames[t.age||0];if(ai)ai.textContent=ageIcons[t.age||0];
}
function updateAIPanel(t){
  const et=document.getElementById('ai-food');if(et)et.textContent=Math.floor(t.food||0);
  const ew=document.getElementById('ai-wood');if(ew)ew.textContent=Math.floor(t.wood||0);
  const eg=document.getElementById('ai-gold');if(eg)eg.textContent=Math.floor(t.gold||0);
  const ep=document.getElementById('ai-pop');if(ep)ep.textContent=`${t.population||0}/${t.maxPop||10}`;
}

// =================================================================
//  UI — Selection panel
// =================================================================
const UNIT_DEFS={
  Villager: {hp:25,maxHp:25,atk:3,def:0,spd:0.040,rng:0.9,cost:{food:50},trainTime:5,pop:1,icon:'👷',vision:18},
  Swordsman:{hp:70,maxHp:70,atk:14,def:4,spd:0.033,rng:1.3,cost:{food:60,gold:20},trainTime:9,pop:1,icon:'⚔',vision:16},
  Archer:   {hp:40,maxHp:40,atk:9,def:1,spd:0.038,rng:7.0,cost:{wood:25,gold:45},trainTime:8,pop:1,icon:'🏹',vision:22},
  Knight:   {hp:130,maxHp:130,atk:20,def:6,spd:0.052,rng:1.5,cost:{food:60,gold:75},trainTime:13,pop:2,icon:'🐴',vision:22},
  Catapult: {hp:90,maxHp:90,atk:40,def:1,spd:0.016,rng:11.0,cost:{wood:200,gold:100},trainTime:20,pop:3,icon:'💣',vision:16},
  Scout:    {hp:55,maxHp:55,atk:5,def:1,spd:0.085,rng:1.2,cost:{food:80},trainTime:7,pop:1,icon:'🏇',vision:38},
};
const BUILD_COSTS={House:{wood:30},Barracks:{wood:175},Farm:{wood:60},Blacksmith:{wood:100,stone:50},Tower:{stone:125},MiningCamp:{wood:100},Lumbercamp:{wood:100},Castle:{stone:650},Market:{wood:175}};
const TECHS=[
  {id:'Iron Tools',name:'Iron Tools',icon:'⚒',cost:{food:100,gold:50},desc:'Gatherers collect 40% faster',age:0},
  {id:'Town Watch',name:'Town Watch',icon:'👁',cost:{food:75},desc:'Towers +2 range',age:0},
  {id:'Loom',name:'Loom',icon:'🧵',cost:{gold:50},desc:'Villagers +40 HP',age:0},
  {id:'Masonry',name:'Masonry',icon:'🧱',cost:{stone:100},desc:'Buildings +20% HP',age:0},
  {id:'Feudal Age',name:'→ Feudal Age',icon:'⚔',cost:{food:500},desc:'Unlock Archers, Knights, advanced buildings',age:0},
  {id:'Fletching',name:'Fletching',icon:'🏹',cost:{food:100,wood:50},desc:'Archers & towers +3 attack',age:1},
  {id:'Scale Armor',name:'Scale Armor',icon:'🛡',cost:{food:100,gold:50},desc:'Infantry +2 armor',age:1},
  {id:'Horse Collar',name:'Horse Collar',icon:'🐴',cost:{food:75,wood:75},desc:'Farms produce 50% more food',age:1},
  {id:'Castle Age',name:'→ Castle Age',icon:'🏰',cost:{food:800,gold:200},desc:'Unlock Castle, Catapult',age:1},
  {id:'Chemistry',name:'Chemistry',icon:'⚗',cost:{food:300,gold:200},desc:'Catapults +40% damage',age:2},
  {id:'Plate Armor',name:'Plate Armor',icon:'⚔',cost:{gold:300},desc:'All units +4 armor',age:2},
  {id:'Imperial Age',name:'→ Imperial Age',icon:'👑',cost:{food:1500,gold:500},desc:'Maximum age — full might',age:2},
];

function refreshSelUI(){
  const panel=document.getElementById('act-panel');if(!panel)return;
  panel.innerHTML='';
  const myT=serverTeams[myTeam]||{};

  if(selectedUnitIds.length>0){
    const id=selectedUnitIds[0],u=serverUnits[id];
    if(!u)return;
    const def=UNIT_DEFS[u.type]||{};
    setEl('sel-portrait',def.icon||'⚔');
    setEl('sel-name',u.type+(selectedUnitIds.length>1?` ×${selectedUnitIds.length}`:''));
    setEl('sel-type','Unit · '+(u.team===myTeam?'Ally':'Enemy'));
    const pct=u.hp/u.maxHp;
    const hp=document.getElementById('sel-hp');if(hp){hp.style.width=(pct*100)+'%';hp.style.background=pct>0.6?'#4cdd4c':pct>0.3?'#ffaa20':'#ee3030';}
    document.getElementById('sel-stats').innerHTML=`<span class="stat-chip">⚔ ${u.atk}</span><span class="stat-chip">🛡 ${u.def}</span><span class="stat-chip">💨 ${Math.round(u.spd*1000)/10}</span><span class="stat-chip">🎯 ${u.rng?.toFixed(1)||'?'}</span><span class="stat-chip scout">👁 ${u.vision||7}</span>`;
    const stMap={idle:'⏸ Standing by',moving:'→ Moving',attacking:'⚔ Attacking!',attacking_building:'🔨 Assaulting!',gathering:'⛏ Gathering',moving_to_gather:'→ To resource',returning:'← Returning',moving_to_attack:'⚔ Marching!',moving_to_build:'→ To site',building:'🔨 Building…'};
    setEl('sel-status',stMap[u.state]||u.state);
    if(u.team===myTeam){
      addActBtn(panel,'👣','Move',()=>{});
      addActBtn(panel,'⚔','Attack Move',()=>{for(const id of selectedUnitIds){const u=serverUnits[id];if(u)u.state='attack_move';}});
      addActBtn(panel,'🛑','Stop [S]',()=>socket.emit('cmd',{type:'stop',unitIds:selectedUnitIds}),'S');
      if(selectedUnitIds.every(id=>serverUnits[id]?.type==='Villager')){
        addActBtn(panel,'🏚','Build House [H]',()=>tryBuild('House'),'H');
        addActBtn(panel,'⚔','Build Barracks [B]',()=>tryBuild('Barracks'),'B');
        addActBtn(panel,'🌾','Build Farm [F]',()=>tryBuild('Farm'),'F');
        addActBtn(panel,'⚒','Build Blacksmith',()=>tryBuild('Blacksmith'));
        addActBtn(panel,'🗼','Build Tower [T]',()=>tryBuild('Tower'),'T');
        addActBtn(panel,'⛏','Mining Camp',()=>tryBuild('MiningCamp'));
        addActBtn(panel,'🪵','Lumbercamp',()=>tryBuild('Lumbercamp'));
        if((myT.age||0)>=2)addActBtn(panel,'🏰','Build Castle [C]',()=>tryBuild('Castle'),'C');
        addActBtn(panel,'🏪','Build Market',()=>tryBuild('Market'));
      }
    }
  } else if(selectedBuildingId){
    const b=serverBuildings[selectedBuildingId];if(!b)return;
    const icons={'Town Center':'🏰',Barracks:'⚔',House:'🏚',Farm:'🌾',Tower:'🗼',Blacksmith:'⚒',Castle:'🏯',Market:'🏪',Lumbercamp:'🪵',MiningCamp:'⛏'};
    setEl('sel-portrait',icons[b.type]||'🏠');
    setEl('sel-name',b.type);setEl('sel-type','Building · '+(b.team===myTeam?'Yours':'Enemy'));
    const pct=b.hp/b.maxHp;
    const hp=document.getElementById('sel-hp');if(hp){hp.style.width=(pct*100)+'%';hp.style.background=pct>0.6?'#4cdd4c':pct>0.3?'#ffaa20':'#ee3030';}
    document.getElementById('sel-stats').innerHTML=`<span class="stat-chip">HP ${b.hp||0}/${b.maxHp||1}</span>`;
    const progTxt=b.underConstruction?`🏗 Building… ${Math.round((b.buildProgress||0)/(b.buildTime||20)*100)}%`:b.productionQueue?.length?`⚒ Training: ${b.productionQueue[0]}`:'⏸ Idle';
    setEl('sel-status',progTxt);
    if(b.team===myTeam&&!b.underConstruction){
      if(b.type==='Town Center'){
        addActBtn(panel,'👷','Train Villager [V]',()=>trainUnit(b.id,'Villager'),'V');
        addActBtn(panel,'🔬','Research [R]',()=>showTech(),'R');
      } else if(b.type==='Barracks'){
        addActBtn(panel,'⚔','Train Swordsman [S]',()=>trainUnit(b.id,'Swordsman'),'S');
        addActBtn(panel,'🏹','Train Archer [A]',()=>trainUnit(b.id,'Archer'),'A');
        addActBtn(panel,'🏇','Train Scout [O]',()=>trainUnit(b.id,'Scout'),'O');
        if((myT.age||0)>=1)addActBtn(panel,'🐴','Train Knight [K]',()=>trainUnit(b.id,'Knight'),'K');
        if((myT.age||0)>=2)addActBtn(panel,'💣','Train Catapult [C]',()=>trainUnit(b.id,'Catapult'),'C');
      } else if(b.type==='Market'){
        addActBtn(panel,'🌾→💰','Sell 100 Food',()=>sellResource('food'));
        addActBtn(panel,'🪵→💰','Sell 100 Wood',()=>sellResource('wood'));
        addActBtn(panel,'🪨→💰','Sell 100 Stone',()=>sellResource('stone'));
      }
    }
  } else if(selectedResNodeId){
    const rn=serverResNodes.find(r=>r.id===selectedResNodeId);
    if(!rn){selectedResNodeId=null;}
    else{
      const icons={gold:'⛏ Gold',stone:'🪨 Stone',wood:'🪵 Wood',food:'🍒 Food'};
      const colours={gold:'#f0c030',stone:'#aaa8a0',wood:'#7a5028',food:'#cc2820'};
      const pct=rn.amount/rn.maxAmount;
      const col=colours[rn.type]||'#c8a050';
      setEl('sel-portrait',{gold:'⛏',stone:'🪨',wood:'🌲',food:'🍒'}[rn.type]||'❓');
      setEl('sel-name',icons[rn.type]||rn.type);
      setEl('sel-type','Resource Node');
      const hp=document.getElementById('sel-hp');
      if(hp){hp.style.width=(pct*100)+'%';hp.style.background=col;}
      const amt=Math.round(rn.amount);
      const max=Math.round(rn.maxAmount);
      document.getElementById('sel-stats').innerHTML=
        `<span class="stat-chip" style="color:${col};">${amt} / ${max}</span>`+
        `<span class="stat-chip">${Math.round(pct*100)}% remaining</span>`;
      setEl('sel-status',amt>0?'Available to gather':'Depleted');
    }
  } else {
    setEl('sel-portrait','🏰');setEl('sel-name','No Selection');setEl('sel-type','Click a unit or building');
    const hp=document.getElementById('sel-hp');if(hp)hp.style.width='100%';
    document.getElementById('sel-stats').innerHTML='';setEl('sel-status','');
  }
}
function setEl(id,v){const e=document.getElementById(id);if(e)e.textContent=v;}
function addActBtn(panel,icon,label,fn,key=''){
  const btn=document.createElement('button');btn.className='ab';
  btn.innerHTML=`<span>${icon}</span><span class="ab-key">${key}</span><span class="tt">${label}</span>`;
  btn.onclick=fn;panel.appendChild(btn);
}
function sellResource(res){
  // Client-side; server doesn't have sell yet, just do it locally for now
  const t=serverTeams[myTeam];if(!t)return;
  if((t[res]||0)<100){alert2('Not enough '+res+'!',true);return;}
  // We'll use a simple cmd for it
  socket.emit('cmd',{type:'research',techId:'_sell_'+res}); // server will ignore, handled client
  t[res]-=100;t.gold=(t.gold||0)+50;updateResUI(t);logEv('Traded 100 '+res+' for 50 gold','info');
}
function trainUnit(buildingId,type){socket.emit('cmd',{type:'produce',buildingId,unitType:type});}

// =================================================================
//  BUILD MODE
// =================================================================
function tryBuild(type){
  const vill=selectedUnitIds.find(id=>serverUnits[id]?.type==='Villager');
  if(!vill){alert2('Select a Villager first!',true);return;}
  const cost=BUILD_COSTS[type]||{};
  const t=serverTeams[myTeam]||{};
  if(cost.food&&t.food<cost.food||cost.wood&&t.wood<cost.wood||cost.gold&&t.gold<cost.gold||cost.stone&&t.stone<cost.stone){alert2('Not enough resources!',true);return;}
  cancelBuildMode();
  const sizeMap={House:2.5,Barracks:3.5,Farm:3,Blacksmith:3,Tower:2,MiningCamp:2.5,Lumbercamp:2.5,Castle:5,Market:3};
  const size=sizeMap[type]||3;
  const ghostGeo=new THREE.BoxGeometry(size,2,size);
  const ghostMat=new THREE.MeshBasicMaterial({color:0x44ff88,transparent:true,opacity:0.35,depthWrite:false});
  const ghostMesh=new THREE.Mesh(ghostGeo,ghostMat);ghostMesh.position.y=1;scene.add(ghostMesh);
  ghostState={type,mesh:ghostMesh,villId:vill,size};
  document.getElementById('build-cursor').classList.add('active');
  document.getElementById('canvas').style.cursor='crosshair';
}
function cancelBuildMode(){
  if(ghostState){scene.remove(ghostState.mesh);ghostState=null;}
  const bc=document.getElementById('build-cursor');if(bc)bc.classList.remove('active');
  const cv=document.getElementById('canvas');if(cv)cv.style.cursor='';
}
function commitBuild(wx,wz){
  if(!ghostState)return;
  if(isWater(wx,wz)){alert2('Cannot build on water!',true);return;}
  const{type,villId}=ghostState;
  socket.emit('cmd',{type:'build',buildType:type,x:wx,z:wz,villagerIds:[villId]});
  cancelBuildMode();
  logEv(`Building ${type}…`,'good');
}

// =================================================================
//  TECH TREE
// =================================================================
function showTech(){
  const pop=document.getElementById('tech-pop'),list=document.getElementById('tech-list');
  if(!pop||!list)return;
  const myT=serverTeams[myTeam]||{};
  list.innerHTML='';
  for(const t of TECHS){
    const locked=t.age>(myT.age||0),done=(myT.researched||[]).includes(t.id);
    const div=document.createElement('div');
    div.className='ti'+(done?' done':'')+(locked?' locked':'');
    const costStr=Object.entries(t.cost).map(([k,v])=>`${v} ${k}`).join(', ');
    div.innerHTML=`<div class="ti-icon">${t.icon}</div><div class="ti-body"><div class="ti-name">${t.name}</div><div class="ti-cost">${costStr}</div><div class="ti-desc">${t.desc}</div></div>${done?'<div class="ti-check">✓</div>':''}`;
    if(!done&&!locked)div.onclick=()=>researchTech(t.id);
    list.appendChild(div);
  }
  pop.style.display='block';
}
function closeTech(){const p=document.getElementById('tech-pop');if(p)p.style.display='none';}
function researchTech(techId){
  socket.emit('cmd',{type:'research',techId});
  closeTech();
}

// =================================================================
//  PARTICLES / FX
// =================================================================
function spawnDeathFX(pos,team){
  for(let i=0;i<8;i++){
    const c=team===myTeam?0x4466ff:0xff3322;
    const m=makePBRSphere(0.07+Math.random()*0.1,4,c,0.4);
    m.material.emissive=new THREE.Color(c);m.material.emissiveIntensity=0.5;
    m.position.copy(pos);m.position.y+=0.5;scene.add(m);
    const vel=new THREE.Vector3((Math.random()-0.5)*0.25,0.12+Math.random()*0.2,(Math.random()-0.5)*0.25);
    particlePool.push({mesh:m,life:1.4,vel,type:'death'});
  }
}
function spawnSmoke(pos){
  const m=makePBRSphere(0.15+Math.random()*0.1,5,0x888888,0.9);
  m.material.transparent=true;m.material.opacity=0.6;
  m.position.set(pos.x+(Math.random()-0.5)*0.5,pos.y+2+Math.random(),pos.z+(Math.random()-0.5)*0.5);
  scene.add(m);particlePool.push({mesh:m,life:1.5,vel:new THREE.Vector3(0,0.02,0),type:'smoke'});
}
function tickParticles(dt){
  for(let i=particlePool.length-1;i>=0;i--){
    const p=particlePool[i];
    p.life-=dt*(p.type==='smoke'?0.5:0.8);
    if(p.type==='death'){p.mesh.position.add(p.vel);p.vel.y-=0.009;p.mesh.material.opacity=p.life;p.mesh.scale.multiplyScalar(0.98);}
    else if(p.type==='smoke'){p.mesh.position.add(p.vel);p.mesh.scale.addScalar(0.02);p.mesh.material.opacity=p.life*0.5;}
    else if(p.type==='mark'){p.mesh.scale.set(1+(1-p.life)*3,1,1+(1-p.life)*3);p.mesh.material.opacity=p.life;}
    if(p.life<=0){scene.remove(p.mesh);particlePool.splice(i,1);}
  }
}

// ── Resource gain popup ──
const RES_COLORS={food:'#7ddd50',wood:'#c8a050',gold:'#ffd700',stone:'#b0a898'};
const RES_ICONS={food:'🌾',wood:'🪵',gold:'💰',stone:'🪨'};
function spawnResGainPopupFromTeam(carry){
  if(!carry)return;
  spawnResGainPopup(carry, innerWidth/2+Math.random()*100-50, innerHeight*0.3+Math.random()*60);
}
function spawnResGainPopupAtWorld(carry, wx, wz){
  if(!carry||!camera)return;
  // Project world position to screen space
  const v=new THREE.Vector3(wx, getHeight(wx,wz)+3, wz);
  v.project(camera);
  const sx=(v.x+1)/2*innerWidth;
  const sy=(-v.y+1)/2*innerHeight;
  // Only show if in front of camera (z<1) and roughly on screen
  if(v.z>1||sx<-60||sx>innerWidth+60||sy<-60||sy>innerHeight+60) return;
  spawnResGainPopup(carry, sx, sy);
}
function spawnResGainPopup(carry, screenX, screenY){
  if(!carry)return;
  const parts=Object.entries(carry).filter(([,v])=>v>0);if(!parts.length)return;
  const label=document.createElement('div');label.className='res-popup';
  label.style.left=screenX+'px';
  label.style.top=screenY+'px';
  label.style.transform='translate(-50%,-50%)';
  label.innerHTML=parts.map(([res,amt])=>`<span style="color:${RES_COLORS[res]||'#fff'}">${RES_ICONS[res]||''}+${Math.floor(amt)}</span>`).join(' ');
  document.body.appendChild(label);
  let elapsed=0;const startY=parseFloat(label.style.top);
  const anim=()=>{elapsed+=16;const t=elapsed/1400;label.style.top=(startY-t*40)+'px';label.style.opacity=String(1-Math.pow(t,2));if(t<1)requestAnimationFrame(anim);else label.remove();};
  requestAnimationFrame(anim);
}

// ── Day/Night cycle ──
function tickDayNight(t){
  // Flat overcast — no intensity swing, just a very slow gentle sky tint shift
  const cycle=(Math.sin(t*0.005)+1)/2;
  const sr=0.55+cycle*0.06,sg=0.64+cycle*0.06,sb=0.72+cycle*0.06;
  if(scene){scene.background=new THREE.Color(sr,sg,sb);if(scene.fog)scene.fog.color.set(sr,sg,sb);}
  // Sun position moves slowly for soft shadow direction change, intensity stays constant
  const sa=t*0.005;
  if(sun)sun.position.set(Math.sin(sa)*80,90,Math.cos(sa)*40);
}
function tickWater(t){
  if(waterMesh)waterMesh.position.y=-1.4+Math.sin(t*0.4)*0.06;
  if(waterMat)waterMat.emissiveIntensity=0.2+Math.sin(t*0.6)*0.08;
}

// =================================================================
//  ALERTS / LOG
// =================================================================
function logEv(msg,type=''){
  evLog.unshift({msg,type});if(evLog.length>10)evLog.pop();
  const el=document.getElementById('ev-entries');
  if(el)el.innerHTML=evLog.map(e=>`<div class="ev ${e.type}">${e.msg}</div>`).join('');
}
function alert2(msg,danger=false){
  const al=document.getElementById('alerts');if(!al)return;
  const d=document.createElement('div');d.className='alert-msg'+(danger?' red':'');d.textContent=msg;
  al.appendChild(d);setTimeout(()=>d.remove(),4000);
}

// =================================================================
//  KEYBOARD
// =================================================================
function onKeyDown(e){
  if(!gameStarted)return;
  if(document.getElementById('tech-pop')?.style.display==='block'){if(e.key==='Escape')closeTech();return;}
  const k=e.key.toLowerCase();
  if(k==='escape'){cancelBuildMode();deselAll();}
  if(selectedBuildingId){
    const b=serverBuildings[selectedBuildingId];if(b&&b.team===myTeam){
      if(k==='v'&&b.type==='Town Center')trainUnit(b.id,'Villager');
      if(k==='r'&&b.type==='Town Center')showTech();
      if(k==='s'&&b.type==='Barracks')trainUnit(b.id,'Swordsman');
      if(k==='a'&&b.type==='Barracks')trainUnit(b.id,'Archer');
      if(k==='o'&&b.type==='Barracks')trainUnit(b.id,'Scout');
      if(k==='k'&&b.type==='Barracks')trainUnit(b.id,'Knight');
    }
  }
  if(selectedUnitIds.length>0){
    if(k==='s')socket.emit('cmd',{type:'stop',unitIds:selectedUnitIds});
    if(k==='h')tryBuild('House');
    if(k==='b')tryBuild('Barracks');
    if(k==='f')tryBuild('Farm');
    if(k==='t')tryBuild('Tower');
    if(k==='c'&&(serverTeams[myTeam]?.age||0)>=2)tryBuild('Castle');
  }
}

// =================================================================
//  CHAT
// =================================================================
function sendChat(){
  const inp=document.getElementById('chat-input');if(!inp)return;
  const text=inp.value.trim();if(!text)return;
  socket.emit('chatMessage',{text});inp.value='';
}
document.getElementById('chat-input')?.addEventListener('keydown',e=>{if(e.key==='Enter')sendChat();});

// =================================================================
//  LOBBY UI
// =================================================================
function showScreen(id){
  for(const s of document.querySelectorAll('.screen'))s.classList.add('hidden');
  const el=document.getElementById(id);if(el)el.classList.remove('hidden');
}

function enterLobby(){
  const inp=document.getElementById('name-input');
  myName=inp?.value.trim();
  const err=document.getElementById('name-error');
  if(!myName){if(err)err.textContent='Please enter your name';return;}
  if(err)err.textContent='';
  socket.emit('setName',{name:myName});
}
function refreshLobbies(){socket.emit('getLobbies');}
function createLobby(){
  const inp=document.getElementById('lobby-name-input');
  const name=inp?.value.trim()||`${myName}'s Realm`;
  socket.emit('createLobby',{lobbyName:name});
}
function joinByCode(){
  const inp=document.getElementById('join-id-input');
  const code=inp?.value.trim().toUpperCase();
  const err=document.getElementById('join-error');
  if(!code){if(err)err.textContent='Enter a room code';return;}
  socket.emit('joinLobby',{lobbyId:code,team:1});
}
function switchTeam(t){socket.emit('switchTeam',{team:t});}
function startGame(){socket.emit('startGame');}
function leaveLobby(){
  currentLobbyId=null;myTeam=null;
  showScreen('screen-lobby');
  socket.emit('getLobbies');
}
function returnToLobby(){
  gameStarted=false;
  const hud=document.getElementById('game-hud');if(hud)hud.style.display='none';
  showScreen('screen-lobby');socket.emit('getLobbies');
}

// =================================================================
//  SOCKET EVENTS
// =================================================================
socket.on('connect',()=>{console.log('Connected');});

socket.on('nameSet',({id})=>{
  myId=id;
  const nl=document.getElementById('lobby-player-name');if(nl)nl.textContent=myName;
  socket.emit('getLobbies');
  showScreen('screen-lobby');
});

socket.on('lobbiesList',lobbies=>{
  const list=document.getElementById('lobby-list');if(!list)return;
  if(!lobbies.length){list.innerHTML='<div style="color:#3a2510;font-size:0.8rem;text-align:center;padding:20px;">No games — create one!</div>';return;}
  list.innerHTML=lobbies.map(l=>`
    <div class="lobby-item" onclick="joinLobby('${l.id}')">
      <div><div class="lobby-item-name">${l.name}</div><div class="lobby-item-info">${l.status==='playing'?'In Progress':'Waiting'}</div></div>
      <div style="display:flex;align-items:center;gap:8px;"><span style="color:#a08040;font-size:0.78rem;">${l.playerCount}/4</span><span class="btn-sm" style="pointer-events:none;">${l.status==='waiting'?'JOIN':'WATCH'}</span></div>
    </div>`).join('');
});
window.joinLobby=function(id){socket.emit('joinLobby',{lobbyId:id,team:1});};

socket.on('lobbyJoined',({lobbyId,team,isHost:ih,players,mapData,initialState})=>{
  currentLobbyId=lobbyId;myTeam=Number(team);isHost=ih;
  if(mapData&&mapData.heightsB64&&!mapData.heights){
    const buf=Uint8Array.from(atob(mapData.heightsB64),c=>c.charCodeAt(0)).buffer;
    mapData.heights=Array.from(new Float32Array(buf));
  }
  const rc=document.getElementById('room-code-display');if(rc)rc.textContent=lobbyId;
  if(mapData){
    terrHeights=mapData.heights;P_OX=mapData.pox;P_OZ=mapData.poz;AI_OX=mapData.aox;AI_OZ=mapData.aoz;
    if(initialState){serverUnits=initialState.units||{};serverBuildings=initialState.buildings||{};serverTeams=initialState.teams||{};}
    if(mapData.resNodes)serverResNodes=mapData.resNodes;
  }
  updateRoomUI(players,team,ih);
  showScreen('screen-room');
});

socket.on('lobbyUpdate',({players})=>{
  const me=players.find(p=>p.id===myId||p.socketId===myId);
  if(me) myTeam=Number(me.team);
  updateRoomUI(players,myTeam,isHost);
});

function updateRoomUI(players,team,ih){
  const list=document.getElementById('room-player-list');
  if(list)list.innerHTML=players.map(p=>{
    const t=Number(p.team);
    const dot=`<div class="player-dot ${t===1?'pdot1':'pdot2'}"></div>`;
    const nameStyle='color:#c8a050;font-size:0.83rem;font-family:\'Cinzel\',serif;';
    const badge=p.isAI
      ?`<span style="font-size:0.68rem;padding:1px 5px;border-radius:3px;background:rgba(212,168,75,0.12);border:1px solid rgba(212,168,75,0.3);color:#a08040;margin-left:5px;">${p.difficulty}</span>`
      :'';
    const teamColor=t===1?'#4a90d9':'#e05c44';
    return `<div class="player-item">
      ${dot}
      <span style="${nameStyle}">${p.isAI?'🤖 ':''} ${p.name}${badge}</span>
      <span style="margin-left:auto;font-size:0.75rem;color:${teamColor};">Team ${p.team}</span>
    </div>`;
  }).join('');

  const b1=document.getElementById('btn-team1'),b2=document.getElementById('btn-team2');
  if(b1)b1.classList.toggle('active',Number(team)===1);
  if(b2)b2.classList.toggle('active',Number(team)===2);
  const bs=document.getElementById('btn-start');
  if(bs)bs.style.display=ih?'':'none';

  // ── AI controls (host only) ──────────────────────────────────────────────
  // Inject or update a panel below the start button
  let aiCtrl=document.getElementById('ai-controls');
  if(ih){
    if(!aiCtrl){
      aiCtrl=document.createElement('div');
      aiCtrl.id='ai-controls';
      aiCtrl.style.cssText='margin-top:12px;border-top:1px solid rgba(107,79,16,0.4);padding-top:12px;';
      const bsParent=bs?bs.parentNode:null;
      if(bsParent) bsParent.appendChild(aiCtrl);
    }
    const DIFF_OPTS='<option value="easy">Easy</option><option value="moderate" selected>Moderate</option><option value="hard">Hard</option>';
    const SEL_STYLE='background:rgba(20,12,3,0.9);border:1px solid #6b4f10;color:#f0d06a;font-family:\'Cinzel\',serif;font-size:0.7rem;padding:3px 5px;border-radius:3px;cursor:pointer;';
    const BTN_STYLE='padding:4px 10px;background:rgba(212,168,75,0.08);border:1px solid rgba(107,79,16,0.5);border-radius:3px;color:#d4a84b;font-family:\'Cinzel\',serif;font-size:0.68rem;cursor:pointer;letter-spacing:0.08em;';
    const REM_STYLE='padding:4px 8px;background:rgba(160,40,40,0.15);border:1px solid rgba(160,40,40,0.4);border-radius:3px;color:#e05c44;font-family:\'Cinzel\',serif;font-size:0.68rem;cursor:pointer;';
    const LABEL='color:#6a4a18;font-size:0.7rem;font-family:\'Cinzel\',serif;letter-spacing:0.12em;text-transform:uppercase;margin-bottom:7px;';

    function aiRowFor(teamNum,teamLabel){
      const ai=players.find(p=>p.isAI&&Number(p.team)===teamNum);
      const human=players.find(p=>!p.isAI&&Number(p.team)===teamNum);
      const color=teamNum===1?'#4a90d9':'#e05c44';
      let inner;
      if(human){
        inner=`<span style="font-size:0.72rem;color:${color};opacity:0.5;">Human player on this team</span>`;
      } else if(ai){
        inner=`<span style="color:#c8a050;font-size:0.75rem;">🤖 ${ai.difficulty.charAt(0).toUpperCase()+ai.difficulty.slice(1)} AI</span>`
             +`<button style="${REM_STYLE}margin-left:auto;" onclick="removeAI(${teamNum})">✕ Remove</button>`;
      } else {
        inner=`<select id="ai-diff-${teamNum}" style="${SEL_STYLE}">${DIFF_OPTS}</select>`
             +`<button style="${BTN_STYLE}margin-left:6px;" onclick="addAI(${teamNum})">+ Add AI</button>`;
      }
      return `<div style="display:flex;align-items:center;gap:6px;padding:5px 0;border-bottom:1px solid rgba(107,79,16,0.15);">
        <span style="color:${color};font-family:'Cinzel',serif;font-size:0.7rem;min-width:65px;">${teamLabel}</span>
        ${inner}
      </div>`;
    }

    aiCtrl.innerHTML=`<div style="${LABEL}">🤖 AI Players</div>`
      +aiRowFor(1,'⚔ BLUE')
      +aiRowFor(2,'🔥 RED');
  } else if(aiCtrl){
    aiCtrl.remove();
  }
}

function addAI(teamNum){
  const sel=document.getElementById('ai-diff-'+teamNum);
  socket.emit('addAI',{team:teamNum,difficulty:sel?sel.value:'moderate'});
}
function removeAI(teamNum){
  socket.emit('removeAI',{team:teamNum});
}

socket.on('gameStarted',({units,buildings,teams,mapData,team})=>{
  serverUnits=units;serverBuildings=buildings;serverTeams=teams;
  if(team!=null) myTeam=Number(team);
  if(mapData&&mapData.heightsB64&&!mapData.heights){
    const buf=Uint8Array.from(atob(mapData.heightsB64),c=>c.charCodeAt(0)).buffer;
    mapData.heights=Array.from(new Float32Array(buf));
  }
  if(mapData){terrHeights=mapData.heights;P_OX=mapData.pox;P_OZ=mapData.poz;AI_OX=mapData.aox;AI_OZ=mapData.aoz;
    if(mapData.resNodes)serverResNodes=mapData.resNodes;}
  startGameClient();
});

socket.on('gameState',state=>{
  if(gameStarted)syncGameState(state);
});

socket.on('buildingPlaced',({building})=>{
  serverBuildings[building.id]=building;
  if(!buildingMeshes[building.id])spawnBuildingMesh(building);
});

socket.on('techResearched',({techId,team})=>{
  if(team===myTeam){logEv(`✓ ${techId} researched!`,'good');alert2(`✓ ${techId} complete!`);}
  else{logEv(`Enemy researched ${techId}!`,'warn');}
});

socket.on('chat',({name,text,team})=>{
  const msgs=document.getElementById('chat-messages');if(!msgs)return;
  const div=document.createElement('div');div.className='chat-msg';
  div.innerHTML=`<span class="chat-name t${team}">${name}:</span> <span style="color:#a08040;">${text}</span>`;
  msgs.appendChild(div);msgs.scrollTop=msgs.scrollHeight;
});

socket.on('gameOver',({winner})=>{
  const title=document.getElementById('gameover-title');
  const sub=document.getElementById('gameover-sub');
  if(winner===myTeam){
    if(title){title.textContent='VICTORY!';title.style.color='#f0d06a';}
    if(sub)sub.textContent='Your team conquers the realm!';
  } else {
    if(title){title.textContent='DEFEAT';title.style.color='#e05c44';}
    if(sub)sub.textContent='Your empire has fallen...';
  }
  showScreen('screen-gameover');
  gameStarted=false;
});

socket.on('error',({message})=>{
  alert2(message,true);
  const je=document.getElementById('join-error');if(je)je.textContent=message;
});

// =================================================================
//  START GAME CLIENT-SIDE
// =================================================================
function startGameClient(){
  showScreen('_none');
  const hud=document.getElementById('game-hud');if(hud)hud.style.display='';

  // Team label
  const tl=document.getElementById('team-label');
  if(tl){tl.textContent=myTeam===1?'⚔ TEAM BLUE':'🔥 TEAM RED';tl.style.color=myTeam===1?'#4a90d9':'#e05c44';}

  mmC=document.getElementById('minimap');mmX=mmC.getContext('2d');
  buildTerrain();
  initCamera();
  setupMouse();

  // Spawn all initial meshes
  for(const id in serverBuildings)spawnBuildingMesh(serverBuildings[id]);
  for(const id in serverUnits)spawnUnitMesh(serverUnits[id]);
  // Resource nodes will come in via gameState

  const mySpawnX=myTeam===1?P_OX:AI_OX;
  const mySpawnZ=myTeam===1?P_OZ:AI_OZ;
  fowReveal(mySpawnX,mySpawnZ,18);

  // Log
  logEv('⚔ Your empire begins. Build and conquer!','good');
  logEv('🌫 Fog of war active. Explore to reveal.','warn');
  logEv(`🎮 You are ${myTeam===1?'Team Blue':'Team Red'}`,'info');
  if(tl){tl.textContent=myTeam===1?'⚔ TEAM BLUE':'🔥 TEAM RED';tl.style.color=myTeam===1?'#4a90d9':'#e05c44';}

  gameStarted=true;
  camTarget=new THREE.Vector3(mySpawnX,0,mySpawnZ);

  // Tips
  setTimeout(()=>alert2('Scout has 38 vision — explore the map!'),5000);
  setTimeout(()=>alert2('Build Houses to increase population cap!'),20000);
  setTimeout(()=>alert2('Research technologies in your Town Center!'),35000);

  startRenderLoop();
}

// =================================================================
//  INTERPOLATION TICK
// =================================================================
function tickInterp(dt){
  interpT+=dt;
  const t=Math.min(1,interpT/INTERP_PERIOD);
  // Unit positions
  for(const id in unitMeshes){
    const mesh=unitMeshes[id],fr=interpFrom[id],to=interpTo[id];
    if(!fr||!to)continue;
    const nx=fr.x+(to.x-fr.x)*t,nz=fr.z+(to.z-fr.z)*t;
    if(Math.abs(nx-mesh.position.x)>0.02||Math.abs(nz-mesh.position.z)>0.02){
      mesh.position.x=nx;mesh.position.z=nz;mesh.position.y=getHeight(nx,nz);
    }
  }
  // Projectiles — fully client-side, animates every frame
  for(const id in _clientProjs){
    const p=_clientProjs[id];
    p.elapsed+=dt;
    const pt=Math.min(1,p.elapsed/p.maxLife);
    const arc=Math.sin(pt*Math.PI)*1.5;
    p.mesh.position.set(p.fx+(p.tx-p.fx)*pt,p.fy+(p.ty-p.fy)*pt+arc,p.fz+(p.tz-p.fz)*pt);
    if(pt>=1){p.mesh.visible=false;delete _clientProjs[id];}
  }
}

// =================================================================
//  RENDER LOOP
// =================================================================
let lastT=performance.now(),mmTimer=0,resTimer=0,selTimer=0;
const _vpMatrix=new THREE.Matrix4();

function startRenderLoop(){
  function loop(){
    requestAnimationFrame(loop);
    const now=performance.now();
    const dt=Math.min((now-lastT)/1000,0.05);
    lastT=now;
    gameTime+=dt;

    tickCamera(dt);
    tickInterp(dt);
    tickFOW(dt);
    tickParticles(dt);
    tickDayNight(gameTime);
    tickWater(gameTime);

    mmTimer+=dt;if(mmTimer>0.15){mmTimer=0;drawMinimap();}
    resTimer+=dt;if(resTimer>0.5){resTimer=0;updateResUI();}
    selTimer+=dt;if(selTimer>0.25){selTimer=0;if(selectedUnitIds.length||selectedBuildingId||selectedResNodeId)refreshSelUI();}

    renderer.autoClear=true;
    renderer.render(scene,camera);
    if(fowQuadMat){
      _vpMatrix.multiplyMatrices(camera.projectionMatrix,camera.matrixWorldInverse);const vp=_vpMatrix;
      fowQuadMat.uniforms.uInvVP.value.copy(vp).invert();
      renderer.autoClear=false;
      renderer.render(fowOrthoScene,fowOrthoCamera);
      renderer.autoClear=true;
    }
  }
  loop();
}

// =================================================================
//  BOOT
// =================================================================
(function boot(){
  initScene();
  // Loading bar
  let p=0;
  const fill=document.getElementById('loading-fill');
  const iv=setInterval(()=>{
    p+=Math.random()*12+5;
    if(fill)fill.style.width=Math.min(p,100)+'%';
    if(p>=100){clearInterval(iv);setTimeout(()=>{
      const ld=document.getElementById('loading');if(ld)ld.style.display='none';
      showScreen('screen-title');
    },500);}
  },130);
})();
