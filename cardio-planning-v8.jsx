const { useState, useEffect, useCallback, useMemo, useRef } = React;
// Firebase injected via window (loaded separately in index.html)
// In CodeSandbox: data is kept in memory only (no persistence)
// In production (Netlify): Firebase syncs automatically
const db = typeof window !== "undefined" && window.firebaseDB ? window.firebaseDB : null;
const PLANNING_DOC = db && window.firebaseDoc ? window.firebaseDoc(db, "planning", "main") : null;
const setDoc = typeof window !== "undefined" && window.firebaseSetDoc ? window.firebaseSetDoc : null;
const onSnapshot = typeof window !== "undefined" && window.firebaseOnSnapshot ? window.firebaseOnSnapshot : null;

/* ════ FÉRIÉS ════ */
function getFeries(y){
  const f=new Set(),add=(m,d)=>f.add(`${y}-${String(m).padStart(2,"0")}-${String(d).padStart(2,"0")}`);
  add(1,1);add(5,1);add(5,8);add(7,14);add(8,15);add(11,1);add(11,11);add(12,25);
  const a=y%19,b=Math.floor(y/100),c=y%100,d2=Math.floor(b/4),e=b%4,ff=Math.floor((b+8)/25),g=Math.floor((b-ff+1)/3),h=(19*a+b-d2-g+15)%30,ii=Math.floor(c/4),k=c%4,l=(32+2*e+2*ii-h-k)%7,m2=Math.floor((a+11*h+22*l)/451),mo=Math.floor((h+l-7*m2+114)/31),dy=((h+l-7*m2+114)%31)+1;
  const paques=new Date(y,mo-1,dy); add(mo,dy);
  [1,39,50].forEach(o=>{const dt=new Date(paques);dt.setDate(dt.getDate()+o);add(dt.getMonth()+1,dt.getDate());});
  return f;
}
const FC={};
function isFerie(y,m,d){if(!FC[y])FC[y]=getFeries(y);return FC[y].has(`${y}-${String(m+1).padStart(2,"0")}-${String(d).padStart(2,"0")}`);}

/* ════ CONSTANTES ════ */
const MOIS=["Janvier","Février","Mars","Avril","Mai","Juin","Juillet","Août","Septembre","Octobre","Novembre","Décembre"];
const JOURSC=["Dim","Lun","Mar","Mer","Jeu","Ven","Sam"];
const JOURSL=["Dimanche","Lundi","Mardi","Mercredi","Jeudi","Vendredi","Samedi"];
const SLOTL={M:"Matin",AM:"Après-midi",N:"Nuit",JOUR:"Journée"};
const SLOTS={M:"M",AM:"AM",N:"N",JOUR:"J"};
const APP_VERSION="v8.31 — 18/07/2026";
/* ════ PÉRIODE GLOBALE (configurable dans Paramètres) ════ */
let PCFG={len:4,startM:6}; // défaut: 4 mois à partir de Juillet
function perStart(y,m){
  const d=((m-PCFG.startM)%12+12)%12;
  const off=d%PCFG.len;
  let sm=m-off,sy=y;
  if(sm<0){sm+=12;sy--;}
  return{sy,sm};
}
function perNext(sy,sm){const t=sm+PCFG.len;return{sy:t>11?sy+1:sy,sm:t%12};}
function perPrev(sy,sm){const t=sm-PCFG.len;return{sy:t<0?sy-1:sy,sm:(t+12)%12};}
function perDaysList(sy,sm){
  const days=[];
  for(let i=0;i<PCFG.len;i++){
    const mm=(sm+i)%12,yy=sm+i>11?sy+1:sy;
    const dim=new Date(yy,mm+1,0).getDate();
    for(let d=1;d<=dim;d++)days.push({y:yy,m:mm,d});
  }
  return days;
}
const SYS=["GARDE","REPOS_GARDE","TOUR_HC","TOUR_USIC","ABSENCE"];
const EDIT_PIN_DEFAULT="1234";

/* ════ HELPERS ════ */
const dIM=(y,m)=>new Date(y,m+1,0).getDate();
const isWE=(y,m,d)=>{const w=new Date(y,m,d).getDay();return w===0||w===6||isFerie(y,m,d);};
const dow=(y,m,d)=>new Date(y,m,d).getDay();
const dKey=(y,m,d)=>`${y}-${String(m+1).padStart(2,"0")}-${String(d).padStart(2,"0")}`;
const sk=(y,m,d,sl)=>`${dKey(y,m,d)}|${sl}`;
const nk=(mid,y,m,d,sl)=>`${mid}|${dKey(y,m,d)}|${sl}`;
function getMon(y,m,d){const dt=new Date(y,m,d),day=dt.getDay(),diff=dt.getDate()-(day===0?6:day-1);return new Date(y,m,diff);}
function wKey(y,m,d){const mo=getMon(y,m,d);return `${mo.getFullYear()}-${mo.getMonth()}-${mo.getDate()}`;}
const ld=(k,f)=>{try{const v=localStorage.getItem(k);return v?JSON.parse(v):f;}catch{return f;}};
const sv=(k,v)=>{try{localStorage.setItem(k,JSON.stringify(v));}catch{}};
function parseDate(s){const[y,m,d]=s.split("-").map(Number);return[y,m-1,d];}

/* ════ GROUPES ════ */
const GRP={
  CORO:["MP","VA","BS","HV","TOM","NH"],TAVI:["HV","TOM"],
  STIM:["CV","TH","CBV","MG","MV","JC","SA"],EEP:["TD","JSL","ND","MG","MV","JC","SA"],
  EEP_AG:["TD","JSL","ND","MG","MV","JC","SA"],ETO:["JSS","PM","CB","AB"],
  DOBU:["JSS","PM","CB","AB","YL","MCD","BF","PL"],DEFIB:["CV","CBV","TH","MG"],
  PM_CS:["CV","CBV","TH","MG"],REVEAL:["CV","CBV","TH","MG"],FOP:["TD","CV","JSS","PM","CB","AB"],
  EE_CHL:["BL"],EE_CHB:["BS"],RYTHMO:["TH","CV","CBV","MG"],
  CARDIOPEDS:["YB","RA"],VASC_CHL:["EJ","LP","LF","JL","IV"],
};

const SALLES_CHL=["CHL-1","CHL-2","CHL-3","CHL-4","CHL-5","CHL-6","CHL-7","Holter","HC-Exam"];
const S_STIM="Salle-Stim",S_EEP="Salle-EEP",S_EE_CHL="EE-CHL",S_EE_CHB="EE-CHB";

const DEFAULT_ACTES=[
  {id:"GARDE",label:"Garde nuit",short:"G",color:"#93c47d",bg:"#f85149",hasSalle:false,salles:[],isSystem:true,site:"tous",medecinsAutorise:[]},
  {id:"REPOS_GARDE",label:"Repos post-garde",short:"RG",color:"#ffe599",bg:"#8b949e",hasSalle:false,salles:[],isSystem:true,site:"tous",medecinsAutorise:["VA","HV","TOM","NH","CV","TH","CBV","JSL","TD","ND","JSS","PM","MG","CB","AB"]},
  {id:"TOUR_HC",label:"Tour médical HC",short:"HC",color:"#388bfd",bg:"#388bfd",hasSalle:false,salles:[],isSystem:true,site:"tous",medecinsAutorise:[]},
  {id:"TOUR_USIC",label:"Tour médical USIC",short:"USIC",color:"#4285f4",bg:"#4285f4",hasSalle:false,salles:[],isSystem:true,site:"tous",medecinsAutorise:[]},
  {id:"TP",label:"Temps partiel",short:"TP",color:"#8b949e",bg:"#8b949e",hasSalle:false,salles:[]},
  {id:"ABSENCE",label:"Absence / Congé",short:"ABS",color:"#e06666",bg:"#e06666",hasSalle:false,salles:[],isSystem:true,site:"tous",medecinsAutorise:[]},
  {id:"CORO",label:"Coronarographie",short:"CORO",color:"#76a5af",bg:"#76a5af",hasSalle:true,salles:["Angio-1","Angio-2","Angio-3"],isSystem:false,site:"tous",medecinsAutorise:GRP.CORO,maxParSalle:1},
  {id:"TAVI",label:"TAVI",short:"TAVI",color:"#76a5af",bg:"#76a5af",hasSalle:true,salles:["Angio-1","Angio-2","Angio-3"],isSystem:false,site:"tous",medecinsAutorise:GRP.TAVI,maxParSalle:1},
  {id:"FOP",label:"FOP / FAG",short:"FOP",color:"#76a5af",bg:"#76a5af",hasSalle:true,salles:["Angio-1","Angio-2","Angio-3"],isSystem:false,site:"tous",medecinsAutorise:GRP.FOP,maxParSalle:1},
  {id:"STIM",label:"Stimulation",short:"Stim",color:"#e3b341",bg:"#e3b341",hasSalle:false,salles:[S_STIM],isSystem:false,site:"CHL",medecinsAutorise:GRP.STIM,fixedSalle:S_STIM},
  {id:"STIM_AG",label:"Stimulation AG",short:"Stim-AG",color:"#f97316",bg:"#f97316",hasSalle:false,salles:[S_STIM],isSystem:false,site:"CHL",medecinsAutorise:GRP.STIM,fixedSalle:S_STIM},
  {id:"EEP_AG",label:"EEP sous AG",short:"EEP-AG",color:"#f97316",bg:"#f97316",hasSalle:false,salles:[S_STIM],isSystem:false,site:"CHL",medecinsAutorise:GRP.EEP_AG,fixedSalle:S_STIM},
  {id:"EEP",label:"Électrophysiologie",short:"EEP",color:"#e3b341",bg:"#e3b341",hasSalle:false,salles:[S_EEP],isSystem:false,site:"CHL",medecinsAutorise:GRP.EEP,fixedSalle:S_EEP},
  {id:"CS_CHL",label:"Consultation CHL",short:"CsL",color:"#c9daf8",bg:"#388bfd",hasSalle:true,salles:SALLES_CHL,isSystem:false,site:"CHL",medecinsAutorise:["MP","VA","BS","HV","TOM","NH","CV","TH","CBV","JSL","TD","ND","JSS","PM","MG","CB","AB","SD","YL","MCD","BF"],maxParSalle:1},
  {id:"ETT_CHL",label:"ETT",short:"ETT",color:"#ea9999",bg:"#ea9999",hasSalle:true,salles:SALLES_CHL,isSystem:false,site:"CHL",medecinsAutorise:["MP","VA","BS","HV","TOM","NH","CV","TH","CBV","JSL","TD","ND","JSS","PM","MG","CB","AB"],maxParSalle:1},
  {id:"ETO_CHL",label:"ETO",short:"ETO",color:"#46bdc6",bg:"#46bdc6",hasSalle:true,salles:SALLES_CHL,isSystem:false,site:"CHL",medecinsAutorise:GRP.ETO,maxParSalle:1},
  {id:"DOBU",label:"Dobutamine",short:"Dobu",color:"#46bdc6",bg:"#46bdc6",hasSalle:true,salles:["CHL-4","CHL-5"],isSystem:false,site:"CHL",medecinsAutorise:GRP.DOBU,maxParSalle:1},
  {id:"PM_CS",label:"Cs Pacemaker",short:"CsPM",color:"#c9daf8",bg:"#c9daf8",hasSalle:true,salles:SALLES_CHL,isSystem:false,site:"CHL",medecinsAutorise:GRP.PM_CS,maxParSalle:1},
  {id:"DEFIB_CS",label:"Cs DAI",short:"CsDAI",color:"#c9daf8",bg:"#c9daf8",hasSalle:true,salles:SALLES_CHL,isSystem:false,site:"CHL",medecinsAutorise:GRP.DEFIB,maxParSalle:1},
  {id:"REVEAL",label:"Reveal",short:"Reveal",color:"#e3b341",bg:"#e3b341",hasSalle:true,salles:SALLES_CHL,isSystem:false,site:"CHL",medecinsAutorise:GRP.REVEAL,maxParSalle:1},
  {id:"VASC_CHL",label:"Vasculaire CHL",short:"Vasc",color:"#94a3b8",bg:"#94a3b8",hasSalle:true,salles:SALLES_CHL,isSystem:false,site:"CHL",medecinsAutorise:GRP.VASC_CHL,maxParSalle:1},
  {id:"EE_CHL",label:"Épreuve effort CHL",short:"EE",color:"#4ade80",bg:"#4ade80",hasSalle:true,salles:[S_EE_CHL],isSystem:false,site:"CHL",medecinsAutorise:["VA","BS","HV","TOM","NH","CV","TH","CBV","JSL","TD","ND","JSS","PM","MG","CB","AB","BL"],fixedSalle:S_EE_CHL,maxParSalle:1},
  {id:"CS_CHB",label:"Consultation CHB",short:"CsB",color:"#b4a7d6",bg:"#b4a7d6",hasSalle:true,salles:["CHB-1","CHB-2","CHB-3"],isSystem:false,site:"CHB",medecinsAutorise:["BS","HV","TOM","NH","CV","TH","CBV","JSL","TD","ND","JSS","PM","MG","CB","AB"],maxParSalle:1},
  {id:"CARDIOPEDS",label:"Cardiopédiatrie",short:"Pédia",color:"#f9a8d4",bg:"#f9a8d4",hasSalle:true,salles:["CHB-1","CHB-2","CHB-3"],isSystem:false,site:"CHB",medecinsAutorise:GRP.CARDIOPEDS,maxParSalle:1},
  {id:"VASC_CHB2",label:"Vasculaire CHB",short:"Vasc",color:"#64748b",bg:"#64748b",hasSalle:true,salles:["CHB-VASC","CHB-3"],isSystem:false,site:"CHB",medecinsAutorise:GRP.VASC_CHL,fixedSalle:"CHB-VASC",maxParSalle:1},
  {id:"EE_CHB",label:"Réadaptation cardiaque",short:"Réab",color:"#b4a7d6",bg:"#b4a7d6",hasSalle:true,salles:[S_EE_CHB],isSystem:false,site:"CHB",medecinsAutorise:GRP.EE_CHB,fixedSalle:S_EE_CHB,maxParSalle:1},
  {id:"RYTHMO_CHB",label:"Rythmologie CHB",short:"CsPM",color:"#b4a7d6",bg:"#b4a7d6",hasSalle:true,salles:["Rythmo-CHB"],isSystem:false,site:"CHB",medecinsAutorise:GRP.RYTHMO,maxParSalle:1},
  {id:"DOBU_CHB",label:"Dobu/ETO CHB",short:"Dobu",color:"#6db8c4",bg:"#6db8c4",hasSalle:true,salles:["CHB-1","CHB-2"],isSystem:false,site:"CHB",medecinsAutorise:["JSS","PM","CB","AB"],maxParSalle:1},
  {id:"SCINTI",label:"Scintigraphie",short:"Scinti",color:"#c3aed6",bg:"#c3aed6",hasSalle:false,salles:[],isSystem:false,site:"CHB",medecinsAutorise:["JSS","CB","AB","MG"],maxParSalle:1},
  {id:"BIP",label:"BIP CHB",short:"BIP",color:"#46bdc6",bg:"#46bdc6",hasSalle:true,salles:["CHB-1","CHB-2","CHB-3"],isSystem:false,site:"CHB",medecinsAutorise:["BS","HV","TOM","NH","CV","TH","CBV","JSL","TD","ND","JSS","PM","MG","CB","AB"],maxParSalle:1},
  {id:"FORMATION",label:"Formation",short:"Form",color:"#a3e635",bg:"#a3e635",hasSalle:false,salles:[],isSystem:false,site:"tous",medecinsAutorise:["MP","VA","BS","HV","TOM","NH","CV","TH","CBV","JSL","TD","ND","JSS","PM","MG","CB","AB","EJ","LP","LF","JL","IV"]},
];

const MEDECINS_INIT=[
  {id:1,nom:"Pécheux",prenom:"Max",init:"MP",color:"#6366f1",garde:false,tourMed:false,role:"medecin"},
  {id:2,nom:"Aumegeat",prenom:"Valérie",init:"VA",color:"#f43f5e",garde:true,tourMed:true,role:"medecin"},
  {id:3,nom:"Segrestin",prenom:"Benoit",init:"BS",color:"#10b981",garde:false,tourMed:true,role:"medecin"},
  {id:4,nom:"Verheyde",prenom:"Hugo",init:"HV",color:"#3b82f6",garde:true,tourMed:true,role:"medecin"},
  {id:5,nom:"Denimal",prenom:"Tom",init:"TOM",color:"#f59e0b",garde:true,tourMed:true,role:"medecin"},
  {id:6,nom:"Hadjaj-Aoul",prenom:"Nabil",init:"NH",color:"#8b5cf6",garde:true,tourMed:true,role:"medecin"},
  {id:7,nom:"Vannesson",prenom:"Claire",init:"CV",color:"#06b6d4",garde:true,tourMed:true,role:"medecin"},
  {id:8,nom:"Hus",prenom:"Thibault",init:"TH",color:"#ec4899",garde:true,tourMed:true,role:"medecin"},
  {id:9,nom:"Belin-Vincent",prenom:"Cassandre",init:"CBV",color:"#14b8a6",garde:true,tourMed:true,role:"medecin"},
  {id:10,nom:"Sion-Lemaire",prenom:"Juliette",init:"JSL",color:"#f97316",garde:true,tourMed:true,role:"medecin"},
  {id:11,nom:"Defrancq",prenom:"Thomas",init:"TD",color:"#84cc16",garde:true,tourMed:true,role:"medecin"},
  {id:12,nom:"Destrait",prenom:"Nicolas",init:"ND",color:"#a855f7",garde:true,tourMed:true,role:"medecin"},
  {id:13,nom:"Savart",prenom:"Jean-Sébastien",init:"JSS",color:"#0ea5e9",garde:true,tourMed:true,role:"medecin"},
  {id:14,nom:"Muller",prenom:"Pierre",init:"PM",color:"#ef4444",garde:true,tourMed:true,role:"medecin"},
  {id:15,nom:"Gorski",prenom:"Maxime",init:"MG",color:"#d946ef",garde:true,tourMed:true,role:"medecin"},
  {id:16,nom:"Beria",prenom:"Chloé",init:"CB",color:"#22c55e",garde:true,tourMed:true,role:"medecin"},
  {id:17,nom:"Bouvier",prenom:"Antoine",init:"AB",color:"#fb923c",garde:true,tourMed:true,role:"medecin"},
  {id:18,nom:"Duchatel",prenom:"Sandra",init:"SD",color:"#94a3b8",garde:false,tourMed:false,role:"ide"},
  {id:19,nom:"Verhaeghe",prenom:"Matthieu",init:"MV",color:"#818cf8",garde:false,tourMed:false,role:"attache"},
  {id:20,nom:"Cardot",prenom:"Joséphine",init:"JC",color:"#f9a8d4",garde:false,tourMed:false,role:"attache"},
  {id:21,nom:"Sghaier",prenom:"Ahmed",init:"SA",color:"#6ee7b7",garde:false,tourMed:false,role:"attache"},
  {id:22,nom:"Lefetz",prenom:"Yann",init:"YL",color:"#fcd34d",garde:false,tourMed:false,role:"attache"},
  {id:23,nom:"Clement-Dupont",prenom:"Maiween",init:"MCD",color:"#f472b6",garde:false,tourMed:false,role:"attache"},
  {id:24,nom:"Biausque",prenom:"Frédéric",init:"BF",color:"#34d399",garde:false,tourMed:false,role:"attache"},
  {id:25,nom:"Lejeune",prenom:"Philippe",init:"PL",color:"#60a5fa",garde:false,tourMed:false,role:"attache"},
  {id:26,nom:"Bourgois",prenom:"Lionel",init:"BL",color:"#4ade80",garde:false,tourMed:false,role:"attache"},
  {id:27,nom:"Bouzguenda",prenom:"Yvan",init:"YB",color:"#38bdf8",garde:false,tourMed:false,role:"attache"},
  {id:28,nom:"Richard",prenom:"Adélaïde",init:"RA",color:"#fb7185",garde:false,tourMed:false,role:"attache"},
  {id:29,nom:"Joly",prenom:"Etienne",init:"EJ",color:"#a3e635",garde:false,tourMed:false,role:"attache"},
  {id:30,nom:"Plovier",prenom:"Loreen",init:"LP",color:"#e879f9",garde:false,tourMed:false,role:"attache"},
  {id:31,nom:"Faurez",prenom:"Lisa",init:"LF",color:"#f97316",garde:false,tourMed:false,role:"attache"},
  {id:32,nom:"Lantez",prenom:"Juliette",init:"JL",color:"#14b8a6",garde:false,tourMed:false,role:"attache"},
  {id:33,nom:"Interne Vasc.",prenom:"",init:"IV",color:"#94a3b8",garde:false,tourMed:false,role:"attache"},
];

const lightenHex=(hex,amt)=>{try{const h=hex.replace("#","");const r=parseInt(h.slice(0,2),16),g=parseInt(h.slice(2,4),16),b=parseInt(h.slice(4,6),16);const f=(v)=>Math.round(v+(255-v)*amt);return "rgb("+f(r)+","+f(g)+","+f(b)+")";}catch(e){return hex;}};
const acteRecapIn=(a,site)=>{if(!a)return false;const arr=a.recapSites||[];return arr.includes(site)||a.recapSite===site||(site==="PLATEAU"&&!!a.ptCardio);};
/* ════ THEME ════ */
function applyTheme(dark){
  const r=document.documentElement;
  if(dark){
    r.style.setProperty("--bg","#1a1f2e");r.style.setProperty("--bg2","#242938");
    r.style.setProperty("--bg-n","#141720");r.style.setProperty("--bg-we","#1f1a0e");
    r.style.setProperty("--vac-bg","#2a3040");r.style.setProperty("--garde-bg","#0f2318");
    r.style.setProperty("--ast-bg","#11291c");r.style.setProperty("--ast-bord","#2f6b45");
    r.style.setProperty("--bg-weh","#231e0e");r.style.setProperty("--bg-td","#0f1f1a");
    r.style.setProperty("--border","#3d4559");r.style.setProperty("--border2","#2d3347");
    r.style.setProperty("--txt","#e8ecf0");r.style.setProperty("--txt2","#8d95a8");r.style.setProperty("--txt3","#4d5568");
    r.style.setProperty("--nav-act","#1e3328");r.style.setProperty("--nav-act-c","#4ade80");
    r.style.setProperty("--hdr","#141720");r.style.setProperty("--th","#1e2436");r.style.setProperty("--td-fix","#1e2436");
    r.style.setProperty("--today-c","#4ade80");r.style.setProperty("--inp","#242938");
    r.style.setProperty("--modal","#242938");r.style.setProperty("--card","#242938");
    r.style.setProperty("--icon","#3d4559");r.style.setProperty("--shadow","rgba(0,0,0,.5)");
  } else {
    r.style.setProperty("--bg","#f1f5f9");r.style.setProperty("--bg2","#ffffff");
    r.style.setProperty("--bg-n","#e2e8f0");
    r.style.setProperty("--vac-bg","#e2e8f0");r.style.setProperty("--garde-bg","#f0fdf4");
    r.style.setProperty("--ast-bg","#dcfce7");r.style.setProperty("--ast-bord","#4ade80");r.style.setProperty("--bg-we","#fef9ee");
    r.style.setProperty("--bg-weh","#fef3c7");r.style.setProperty("--bg-td","#f0fdf4");
    r.style.setProperty("--border","#cbd5e1");r.style.setProperty("--border2","#e2e8f0");
    r.style.setProperty("--txt","#1e293b");r.style.setProperty("--txt2","#475569");r.style.setProperty("--txt3","#94a3b8");
    r.style.setProperty("--nav-act","#dcfce7");r.style.setProperty("--nav-act-c","#15803d");
    r.style.setProperty("--hdr","#1e293b");r.style.setProperty("--th","#f8fafc");r.style.setProperty("--td-fix","#f8fafc");
    r.style.setProperty("--today-c","#15803d");r.style.setProperty("--inp","#f8fafc");
    r.style.setProperty("--modal","#ffffff");r.style.setProperty("--card","#ffffff");
    r.style.setProperty("--icon","#e2e8f0");r.style.setProperty("--shadow","rgba(0,0,0,.1)");
  }
}
applyTheme(false);
document.documentElement.style.fontSize="120%";

/* ════ STYLES ════ */
const S={
  app:{minHeight:"100vh",background:"var(--bg)",fontFamily:"'Sora','Segoe UI',sans-serif",color:"var(--txt)"},
  hdr:{background:"var(--hdr)",borderBottom:"1px solid var(--border)",padding:"0 10px",display:"flex",alignItems:"center",height:50,position:"sticky",top:0,zIndex:100,gap:6},
  nav:{display:"flex",gap:1,flex:1,overflowX:"auto",flexWrap:"nowrap",scrollbarWidth:"none",msOverflowStyle:"none",WebkitOverflowScrolling:"touch"},
  nb:{padding:"4px 9px",borderRadius:6,border:"none",background:"transparent",cursor:"pointer",fontSize:11,fontWeight:500,color:"rgba(255,255,255,.65)",whiteSpace:"nowrap",flexShrink:0},
  nba:{background:"var(--nav-act)",color:"var(--nav-act-c)",fontWeight:700},
  mTit:{fontSize:16,fontWeight:800,margin:0,color:"var(--txt)"},
  arr:{width:26,height:26,borderRadius:6,border:"1px solid var(--border)",background:"var(--bg2)",cursor:"pointer",fontSize:14,color:"var(--txt2)"},
  oriTog:{display:"flex",background:"var(--bg2)",borderRadius:6,padding:2,gap:1,border:"1px solid var(--border)"},
  oriB:{padding:"3px 7px",borderRadius:4,border:"none",background:"transparent",color:"var(--txt2)",cursor:"pointer",fontSize:10,fontWeight:600},
  oriBa:{background:"#1d4ed8",color:"#fff"},
  main:{padding:"10px",maxWidth:1900,margin:"0 auto"},
  bar:{display:"flex",alignItems:"center",marginBottom:10,gap:7},
  thFix:{padding:"5px 9px",background:"var(--th)",fontWeight:700,fontSize:10,color:"var(--txt2)",textTransform:"uppercase",letterSpacing:.4,borderRight:"2px solid var(--border)",whiteSpace:"nowrap"},
  th:{padding:"3px 2px",textAlign:"center",background:"var(--th)",fontSize:10,color:"var(--txt2)",minWidth:30,borderRight:"1px solid var(--border)",borderBottom:"1px solid var(--border)"},
  thWE:{background:"var(--bg-weh)"},thTD:{background:"var(--bg-td)",color:"var(--today-c)"},
  thN:{fontSize:12,fontWeight:800,color:"var(--txt)"},thJ:{fontSize:7,color:"var(--txt3)",textTransform:"uppercase"},
  tdFix:{padding:"3px 8px",background:"var(--td-fix)",borderRight:"2px solid var(--border)",verticalAlign:"middle"},
  td:{padding:"0",textAlign:"center",verticalAlign:"top",minWidth:30,borderRight:"1px solid var(--border2)",background:"var(--bg2)",position:"relative"},
  tdWE:{background:"var(--bg-we)",height:28,maxHeight:28,overflow:"hidden"},tdN:{background:"var(--bg-n)"},
  tdConfl:{background:"#fee2e2",outline:"1px solid #ef4444"},
  av:{width:24,height:24,borderRadius:"50%",display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:9,fontWeight:800,flexShrink:0},
  avT:{width:28,height:28,borderRadius:"50%",display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:10,fontWeight:800},
  card:{background:"var(--card)",border:"1px solid var(--border)",borderRadius:9,padding:"10px 12px"},
  ov:{position:"fixed",inset:0,background:"rgba(0,0,0,.6)",display:"flex",alignItems:"center",justifyContent:"center",zIndex:1000,backdropFilter:"none"},
  mb:{background:"var(--modal)",border:"1px solid var(--border)",borderRadius:12,padding:18,width:500,maxWidth:"95vw",maxHeight:"90vh",overflowY:"auto",boxShadow:"0 20px 60px var(--shadow)"},
  mHd:{display:"flex",justifyContent:"space-between",alignItems:"flex-start",marginBottom:12},
  mTit2:{fontSize:14,fontWeight:800,color:"var(--txt)"},
  xBtn:{background:"none",border:"none",fontSize:22,cursor:"pointer",color:"var(--txt2)",lineHeight:1,padding:0},
  actGrd:{display:"grid",gridTemplateColumns:"1fr 1fr",gap:5,marginBottom:8},
  actTog:{padding:"7px 9px",borderRadius:7,border:"1px solid var(--border)",cursor:"pointer",display:"flex",flexDirection:"column",gap:2,textAlign:"left",background:"var(--bg2)"}, 
  qBtn:{padding:"5px 9px",borderRadius:7,border:"1px solid #ef4444",background:"#fef2f2",color:"#dc2626",cursor:"pointer",fontSize:11,fontWeight:600},
  fGrd:{display:"grid",gridTemplateColumns:"1fr 1fr",gap:8},
  fl:{display:"block",fontSize:10,fontWeight:700,color:"var(--txt2)",marginBottom:3,textTransform:"uppercase",letterSpacing:.4},
  fi:{padding:"6px 9px",borderRadius:7,border:"1px solid var(--border)",background:"var(--inp)",color:"var(--txt)",fontSize:13,outline:"none",fontFamily:"'Sora',sans-serif"},
  icnBtn:{background:"var(--icon)",border:"1px solid var(--border)",borderRadius:6,padding:"4px 7px",cursor:"pointer",fontSize:12,color:"var(--txt2)"},
  btnP:{padding:"6px 12px",borderRadius:7,border:"none",background:"#1d4ed8",color:"#fff",cursor:"pointer",fontSize:12,fontWeight:700},
  btnAbs:{padding:"4px 9px",borderRadius:6,border:"1px solid #ef4444",background:"#fef2f2",color:"#dc2626",cursor:"pointer",fontSize:11,fontWeight:600},
  notif:{position:"fixed",top:58,right:12,padding:"8px 13px",borderRadius:8,border:"1.5px solid",fontSize:12,fontWeight:600,zIndex:2000,color:"var(--txt)"},
  tmRow:{background:"var(--card)",border:"1px solid var(--border)",borderRadius:8,padding:"10px 12px",marginBottom:6,display:"flex",gap:12,flexWrap:"wrap",alignItems:"flex-start"},
};

/* ════ MICRO COMPONENTS ════ */
function hexToLum(hex){
  // Returns perceived luminance 0-1
  const r=parseInt(hex.slice(1,3),16)/255,g=parseInt(hex.slice(3,5),16)/255,b=parseInt(hex.slice(5,7),16)/255;
  const toL=c=>c<=0.04045?c/12.92:Math.pow((c+0.055)/1.055,2.4);
  return 0.2126*toL(r)+0.7152*toL(g)+0.0722*toL(b);
}
function Badge({a,salle,hasNote,hideSalle=false}){
  if(!a)return null;
  const col=a.color||"#888888";
  return(
    <div style={{position:"relative",display:"inline-block",margin:"1px 1px"}}>
      <div style={{background:col,color:"#111",
        fontSize:10,fontWeight:800,fontFamily:"'JetBrains Mono',monospace",
        borderRadius:4,padding:"4px 0",lineHeight:1.3,textAlign:"center",
        width:44,minWidth:44,maxWidth:44,overflow:"hidden",
        whiteSpace:"nowrap",textOverflow:"ellipsis"}}>
        <span style={{display:"block",padding:"0 3px"}}>{a.short}</span>
        {!hideSalle&&salle&&<span style={{display:"block",fontSize:7,opacity:.85,padding:"0 2px"}}>{salle}</span>}
      </div>
      {hasNote&&<div style={{position:"absolute",top:-1,right:-1,width:6,height:6,borderRadius:"50%",background:"#f59e0b"}}/>}
    </div>
  );
}
function Av({med}){return <div style={{...S.av,background:med.color}}>{med.init}</div>;}
function Chp({bg,c,children}){return <span style={{fontSize:9,background:bg,color:c,padding:"1px 4px",borderRadius:3,fontWeight:700}}>{children}</span>;}
function Ov({children,onClose}){return <div style={S.ov} onClick={e=>{if(e.target===e.currentTarget)onClose();}}><div style={S.mb}>{children}</div></div>;}
function FF({l,v,c}){return <div><label style={S.fl}>{l}</label><input value={v} onChange={e=>c(e.target.value)} style={{...S.fi,width:"100%"}}/></div>;}
function MBar({year,month,prevM,nextM,extra,right}){
  const {sy:_sy,sm:_sm}=perStart(year,month);
  const _em=(_sm+PCFG.len-1)%12;
  const _pLabel=MOIS[_sm]+" — "+MOIS[_em]+" "+_sy;
  return(
    <div style={S.bar}>
      <div style={{display:"flex",alignItems:"center",gap:8}}>
        <button onClick={prevM} style={S.arr}>‹</button>
        <h2 style={S.mTit}>{extra?<>{extra} — {_pLabel}</>:<>{_pLabel}</>}</h2>
        <button onClick={nextM} style={S.arr}>›</button>
      </div>
      {right&&right}
    </div>
  );
}
function MedBtn({med,avail,onClick,extra}){
  const blocked=avail==="blocked", warn=avail==="warning";
  return(
    <button disabled={blocked} onClick={onClick}
      style={{display:"flex",alignItems:"center",gap:7,padding:"6px 9px",borderRadius:7,border:`1px solid ${warn?"#f59e0b44":"var(--border)"}`,
        cursor:blocked?"default":"pointer",background:warn?"#1a1000":"var(--bg2)",opacity:blocked?.35:1,width:"100%"}}>
      <div style={{...S.av,background:med.color,width:24,height:24}}>{med.init}</div>
      <div style={{textAlign:"left",flex:1}}>
        <div style={{fontSize:11,fontWeight:700,color:"var(--txt)"}}>{med.prenom} {med.nom}</div>
        <div style={{fontSize:9,color:blocked?"#ef4444":warn?"#f59e0b":"var(--txt3)"}}>{blocked?"Absent/repos":warn?"⚠ Déjà occupé":"Disponible"}</div>
      </div>
      {extra&&extra}
    </button>
  );
}

/* ════ GRID H ════ */
function GridH({allDays,year,month,meds,getEntries,acteById,onCell,isEdit,notes={},isVac,applyGarde,allMeds,viewPeriod,allDays4,showFull,showGarde=true,getAstreinteForDay}){ 
  const today=new Date();
  const ghEffDays=useMemo(()=>{
    if(viewPeriod){
      const {sy,sm}=perStart(year,month);
      const days=[];
      for(let mi=0;mi<PCFG.len;mi++){
        const m2=(sm+mi)%12,y2=sm+mi>11?sy+1:sy;
        const dim=new Date(y2,m2+1,0).getDate();
        for(let d=1;d<=dim;d++) days.push({y:y2,m:m2,d});
      }
      if(!showFull){const tod=new Date();tod.setHours(0,0,0,0);return days.filter(({y:ey,m:em,d})=>new Date(ey,em,d)>=tod);}
      return days;
    }
    const base=allDays.map(d=>({y:year,m:month,d}));
    if(!showFull){const tod=new Date();tod.setHours(0,0,0,0);return base.filter(({y:ey,m:em,d})=>new Date(ey,em,d)>=tod);}
    return base;
  },[year,month,viewPeriod,allDays,showFull]);
  return(
    <div style={{overflowX:"auto",overflowY:"auto",maxHeight:"calc(100vh - 110px)",borderRadius:8,border:"1px solid var(--border)"}}>
      <table style={{borderCollapse:"collapse",tableLayout:"fixed"}}>
        <thead>
          <tr>
            <th style={{...S.thFix,position:"sticky",top:0,left:0,zIndex:40,minWidth:58}} rowSpan={2}>Méd.</th>
            {ghEffDays.map(({y:ghY,m:ghM,d})=>{
              const we=isWE(ghY,ghM,d),isT=d===today.getDate()&&ghM===today.getMonth()&&ghY===today.getFullYear();
              const cols=showGarde?3:2;
              return <th key={d+ghM+ghY} colSpan={we?1:cols} style={{...S.th,...(we?S.thWE:{}),...(isT?S.thTD:{}),minWidth:we?32:cols*28,position:"sticky",top:0,zIndex:20}}>
                <div style={S.thN}>{d}</div>{viewPeriod&&<div style={{fontSize:10,color:"var(--txt2)",fontWeight:700}}>{MOIS[ghM]}</div>}<div style={S.thJ}>{["D","L","Ma","Me","J","V","S"][dow(ghY,ghM,d)]}</div>
              </th>;
            })}
          </tr>
          <tr>
            {ghEffDays.map(({y:ghY,m:ghM,d})=>{
              if(isWE(ghY,ghM,d))return null;
              const slots=showGarde?["M","AM","N"]:["M","AM"];
              return slots.map(sl=><th key={d+sl+ghM+ghY} style={{...S.th,fontSize:8,padding:"2px 1px",background:sl==="N"?"var(--bg-n)":"var(--th)",color:"var(--txt3)",position:"sticky",top:"24px",zIndex:19}}>{SLOTS[sl]}</th>);
            })}
          </tr>
        </thead>
        <tbody>
          {meds.map(med=>(
            <tr key={med.id} style={{borderBottom:"1px solid var(--border2)",height:32}}>
              <td style={{...S.tdFix,position:"sticky",left:0,zIndex:10}} title={`Dr. ${med.prenom} ${med.nom}`}>
                <div style={{display:"flex",alignItems:"center",gap:5}}><Av med={med}/><span style={{fontSize:10,fontWeight:800,color:"var(--txt)",fontFamily:"'JetBrains Mono',monospace"}}>{med.init}</span></div>
              </td>
              {ghEffDays.map(({y:ghY,m:ghM,d})=>{
                const we=isWE(ghY,ghM,d);
                if(we){
                  const es=getEntries(med.id,year,month,d,"JOUR");
                  const noteT=notes[nk(med.id,year,month,d,"JOUR")];
                  return <td key={d} title={noteT||undefined} style={{...S.td,...S.tdWE,cursor:isEdit?"pointer":"default"}} onClick={()=>onCell(med.id,year,month,d,"JOUR")}>
                    {es.map((e,i)=>{const a=e.acteId?acteById(e.acteId):null;return a?<Badge key={i} a={a} salle={e.salle} hideSalle={true} hasNote={!!noteT}/>:null;})}
                  </td>;
                }
                return["M","AM","N"].map(sl=>{
                  const es=getEntries(med.id,year,month,d,sl);
                  const bl=es[0]&&es[0]._blocked;
                  const noteT=notes[nk(med.id,ghY,ghM,d,sl)];
                  const astIdH=getAstreinteForDay?getAstreinteForDay(ghY,ghM,d):null;
                  const isAstH=astIdH!==null&&String(astIdH)===String(med.id);
                  return <td key={d+sl+ghM+ghY} title={noteT||undefined}
                    style={{...S.td,...(sl==="N"?S.tdN:{}),...(isAstH?{background:"var(--ast-bg)",boxShadow:"inset 0 0 0 1px var(--ast-bord)"}:{}),...(isTgh?{background:"var(--bg-td)"}:{}),...(bl?{background:"var(--bg)",opacity:.4,cursor:"default"}:{cursor:isEdit?"pointer":"default"}),display:"table-cell",verticalAlign:"middle"}}
                    onClick={bl||!isEdit?undefined:()=>onCell(med.id,ghY,ghM,d,sl)}>
                    {!bl&&<div style={{display:"flex",flexWrap:"wrap",justifyContent:"center",alignItems:"center",gap:1}}>
                      {es.map((e,i)=>{const a=e.acteId?acteById(e.acteId):null;return a?<Badge key={i} a={a} salle={e.salle} hideSalle={true} hasNote={!!noteT}/>:null;})}
                    </div>}
                  </td>;
                });
              })}
            </tr>
          ))}
        </tbody>
      </table>
    </div>
  );
}

/* ════ GRID V ════ */
function GridV({allDays,year,month,meds,getEntries,acteById,onCell,isEdit,notes={},isVac,applyGarde,allMeds,viewPeriod,allDays4,showFull,showGarde=true,getAstreinteForDay}){
  const today=new Date();
  const C0=42,C1=24,CG=44;
  // Find garde med for a given day (slot N)
  const [pickGardeDayFull,setPickGardeDayFull]=useState(null);
  const pickGardeDay=pickGardeDayFull?pickGardeDayFull.d:null;
  const setPickGardeDay=(v)=>setPickGardeDayFull(v?{d:v,y:year,m:month}:null);
  const [gardeSearch,setGardeSearch]=useState("");
  const gardePickMeds=(allMeds||meds).filter(m=>m.garde===true);
  // 4-month view: flatten allDays4 by month groups
  const today2=new Date();
  const effectiveDays=useMemo(()=>{
    if(!viewPeriod){
      const base=allDays.map(d=>({y:year,m:month,d,label:null}));
      if(!showFull){const tod=new Date();tod.setHours(0,0,0,0);return base.filter(({y:ey,m:em,d})=>new Date(ey,em,d)>=tod);}
      return base;
    }
    // Mode période
    const {sy,sm}=perStart(year,month);
    const days=[];
    for(let mi=0;mi<PCFG.len;mi++){
      const m2=(sm+mi)%12,y2=sm+mi>11?sy+1:sy;
      const dim=new Date(y2,m2+1,0).getDate();
      for(let d=1;d<=dim;d++) days.push({y:y2,m:m2,d,label:null});
    }
    if(!showFull){const tod=new Date();tod.setHours(0,0,0,0);return days.filter(({y:ey,m:em,d})=>new Date(ey,em,d)>=tod);}
    return days;
  },[viewPeriod,allDays,year,month,showFull,PCFG.len,PCFG.startM]);
  const getGardeMed=(d)=>getGardeMed2(year,month,d);
  const getGardeMed2=(y2,m2,d2)=>{
    const dw2=dow(y2,m2,d2);
    const gardeSlot=(dw2===6||dw2===0)?"JOUR":"N";
    for(const m of (allMeds||meds)){
      const es=getEntries(m.id,y2,m2,d2,gardeSlot);
      if(es.some(e=>e.acteId==="GARDE")) return m;
    }
    return null;
  };
  const [gardeSwapOpen,setGardeSwapOpen]=React.useState(false);
  const gSlotOf=(y2,m2,d2)=>{const dw2=dow(y2,m2,d2);return (dw2===6||dw2===0)?"JOUR":"N";};
  const isAbsOn=(mid,y2,m2,d2)=>{
    const sls=isWE(y2,m2,d2)?["JOUR"]:["M","AM"];
    return sls.some(sl=>getEntries(mid,y2,m2,d2,sl).some(e=>["ABSENCE","FORM","FORMATION"].includes(e.acteId)));
  };
  const runGardeSwap=(A,B)=>{
    // applyGarde retire la garde existante du jour + son repos, puis pose garde + repos du nouveau titulaire
    applyGarde(B.medId,A.y,A.m,A.d);
    setTimeout(()=>applyGarde(A.medId,B.y,B.m,B.d),40);
  };
  const gardeActe={id:"GARDE",label:"Garde nuit",short:"G",color:"#93c47d"};
  return(
    <>
    {pickGardeDay&&<Ov onClose={()=>setPickGardeDay(null)}>
      <div style={{minWidth:280}}>
        <div style={S.mHd}><div style={S.mTit2}>🌙 Garde — {(()=>{const pgf=pickGardeDayFull||{d:pickGardeDay,y:year,m:month};const dw=dow(pgf.y,pgf.m,pgf.d);return ["Dim","Lun","Mar","Mer","Jeu","Ven","Sam"][dw]+" "+pgf.d+" "+MOIS[pgf.m]+" "+pgf.y;})()}</div><button onClick={()=>setPickGardeDay(null)} style={S.xBtn}>×</button></div>
        {(()=>{const pgf2=pickGardeDayFull||{d:pickGardeDay,y:year,m:month};const cgm=getGardeMed2(pgf2.y,pgf2.m,pgf2.d);return cgm?(<div style={{marginBottom:10,display:"flex",alignItems:"center",gap:6,padding:"6px 10px",background:"var(--garde-bg)",borderRadius:7,border:"1px solid #86efac"}}>
          <div style={{width:22,height:22,borderRadius:"50%",background:cgm.color,display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:9,fontWeight:800}}>{cgm.init}</div>
          <span style={{fontSize:12,fontWeight:600}}>Garde actuelle : {cgm.prenom} {cgm.nom}</span>
          <button onClick={()=>setGardeSwapOpen(v=>!v)} style={{marginLeft:"auto",fontSize:11,padding:"3px 8px",borderRadius:6,border:"1.5px solid #388bfd",background:"rgba(56,139,253,.10)",color:"#388bfd",fontWeight:800,cursor:"pointer"}}>⇄ Échanger</button>
          <button onClick={()=>{const pgf3=pickGardeDayFull||{d:pickGardeDay,y:year,m:month};const dwB=dow(pgf3.y,pgf3.m,pgf3.d);onCell(cgm.id,pgf3.y,pgf3.m,pgf3.d,(dwB===6||dwB===0)?"JOUR":"N");setPickGardeDay(null);}} style={{...S.btnP,fontSize:11,padding:"3px 8px"}}>Modifier</button>
        </div>):null;})()}
        {gardeSwapOpen&&(()=>{
          const pgf=pickGardeDayFull||{d:pickGardeDay,y:year,m:month};
          const medA=getGardeMed2(pgf.y,pgf.m,pgf.d);
          if(!medA)return null;
          const A={y:pgf.y,m:pgf.m,d:pgf.d,medId:medA.id};
          const JG=["Dim","Lun","Mar","Mer","Jeu","Ven","Sam"];
          const others=effectiveDays.map(({y:gy,m:gm,d:gd})=>{
            if(gy===pgf.y&&gm===pgf.m&&gd===pgf.d)return null;
            const mB=getGardeMed2(gy,gm,gd);
            if(!mB||mB.id===medA.id)return null;
            const blockA=isAbsOn(medA.id,gy,gm,gd);      // A absent le jour de B
            const blockB=isAbsOn(mB.id,pgf.y,pgf.m,pgf.d); // B absent le jour de A
            const reason=blockA?(medA.init+" absent ce jour"):blockB?(mB.init+" absent le "+pgf.d):null;
            return {y:gy,m:gm,d:gd,mB,reason};
          }).filter(Boolean);
          return(
          <div style={{marginBottom:10,padding:"8px 10px",borderRadius:8,border:"1.5px solid #388bfd",background:"rgba(56,139,253,.05)"}}>
            <div style={{fontSize:11,fontWeight:800,color:"#388bfd",marginBottom:6}}>⇄ Échanger la garde de {medA.init} ({JG[dow(pgf.y,pgf.m,pgf.d)]} {pgf.d} {MOIS[pgf.m].slice(0,4)}) avec :</div>
            <div style={{maxHeight:"38vh",overflowY:"auto"}}>
              {others.map((o,i2)=>(
                <div key={i2} onClick={()=>{
                    if(o.reason)return;
                    runGardeSwap(A,{y:o.y,m:o.m,d:o.d,medId:o.mB.id});
                    setGardeSwapOpen(false);setPickGardeDay(null);setPickGardeDayFull(null);
                  }}
                  style={{display:"flex",alignItems:"center",gap:7,padding:"6px 9px",borderRadius:7,marginBottom:4,cursor:o.reason?"not-allowed":"pointer",opacity:o.reason?.45:1,border:"1px solid var(--border2)",background:"var(--bg2)"}}>
                  <span style={{fontSize:11,fontWeight:700,color:"var(--txt)",width:92}}>{JG[dow(o.y,o.m,o.d)]} {o.d} {MOIS[o.m].slice(0,4)}</span>
                  <span style={{width:20,height:20,borderRadius:"50%",background:o.mB.color,color:"#fff",fontSize:8,fontWeight:800,display:"inline-flex",alignItems:"center",justifyContent:"center"}}>{o.mB.init}</span>
                  <span style={{fontSize:11,fontWeight:600,color:"var(--txt)",flex:1}}>{o.mB.nom}</span>
                  {o.reason?<span style={{fontSize:9,color:"#f85149",fontWeight:600}}>{o.reason}</span>:<span style={{fontSize:11,color:"#388bfd",fontWeight:800}}>⇄</span>}
                </div>
              ))}
              {others.length===0&&<div style={{fontSize:11,color:"var(--txt3)"}}>Aucune autre garde attribuée sur la période affichée.</div>}
            </div>
            <button onClick={()=>setGardeSwapOpen(false)} style={{marginTop:6,fontSize:11,padding:"4px 10px",borderRadius:6,border:"1px solid var(--border)",background:"var(--bg2)",color:"var(--txt2)",cursor:"pointer",fontWeight:600}}>Annuler l'échange</button>
          </div>);
        })()}
        {(()=>{
          const filteredGM=gardePickMeds.filter(m=>!gardeSearch||m.init.toUpperCase().startsWith(gardeSearch));
          const onEnter=e=>{if(e.key==="Enter"&&filteredGM.length===1){const pgf=pickGardeDayFull||{d:pickGardeDay,y:year,m:month};applyGarde(filteredGM[0].id,pgf.y,pgf.m,pgf.d);setPickGardeDayFull(null);}};
          return(<>
        <input
          autoFocus
          value={gardeSearch}
          onChange={e=>setGardeSearch(e.target.value.toUpperCase())}
          onKeyDown={onEnter}
          placeholder="Initiales ou nom..."
          style={{width:"100%",padding:"8px 10px",borderRadius:7,border:"1px solid var(--border)",background:"var(--bg2)",color:"var(--txt)",fontSize:14,fontFamily:"'JetBrains Mono',monospace",fontWeight:700,letterSpacing:2,marginBottom:8,boxSizing:"border-box"}}
        />
        {filteredGM.length===1&&<div style={{fontSize:10,color:"var(--txt3)",marginBottom:4,textAlign:"center"}}>↵ Entrée pour confirmer</div>}
        <div style={{display:"flex",flexDirection:"column",gap:5,maxHeight:320,overflowY:"auto"}}>
          {filteredGM.map(m=>{
            const pgfCur=pickGardeDayFull||{d:pickGardeDay,y:year,m:month};
            const gm=getGardeMed2(pgfCur.y,pgfCur.m,pgfCur.d);
            const isOn=gm&&gm.id===m.id;
            return <button key={m.id}
              style={{display:"flex",alignItems:"center",gap:8,padding:"8px 10px",borderRadius:8,border:`1px solid ${isOn?"#16a34a":"var(--border)"}`,background:isOn?"#f0fdf4":"var(--bg2)",cursor:"pointer"}}
              onClick={()=>{const pgf=pickGardeDayFull||{d:pickGardeDay,y:year,m:month};applyGarde(m.id,pgf.y,pgf.m,pgf.d);setPickGardeDayFull(null);}}>
              <div style={{width:24,height:24,borderRadius:"50%",background:m.color,display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:9,fontWeight:800}}>{m.init}</div>
              <span style={{fontSize:12,fontWeight:600,color:"var(--txt)"}}>{m.prenom} {m.nom}</span>
              {isOn&&<span style={{marginLeft:"auto",color:"#16a34a",fontSize:12}}>✓ De garde</span>}
            </button>;
          })}
        </div>
        </>);})()}
      </div>
    </Ov>}
    <div style={{overflowX:"auto",overflowY:"auto",maxHeight:"calc(100vh - 110px)",borderRadius:8,border:"1px solid var(--border)"}}>
      <table style={{borderCollapse:"collapse",tableLayout:"fixed"}}>
        <thead>
          <tr>
            <th style={{...S.thFix,position:"sticky",top:0,left:0,zIndex:40,minWidth:C0}}>Jour</th>
            <th style={{...S.thFix,position:"sticky",top:0,left:C0,zIndex:40,minWidth:C1}}>Sl</th>
            {showGarde&&<th style={{...S.thFix,position:"sticky",top:0,zIndex:20,minWidth:CG,borderRight:"2px solid var(--border)",fontSize:9,color:"#93c47d"}}>Garde</th>}
            {meds.map(m=><th key={m.id} style={{...S.th,minWidth:46,position:"sticky",top:0,zIndex:20}} title={`Dr. ${m.prenom} ${m.nom}`}>
              <div style={{...S.avT,background:m.color,margin:"0 auto"}}>{m.init}</div>
            </th>)}
          </tr>
        </thead>
        <tbody>
          {effectiveDays.map(({y:ey,m:em,d},di)=>{
            const prevDay=di>0?effectiveDays[di-1]:null;
            const isNewMonth=viewPeriod&&(!prevDay||prevDay.m!==em||prevDay.y!==ey);
            const we=isWE(ey,em,d),isT=d===today.getDate()&&em===today.getMonth()&&ey===today.getFullYear();
            const slots=we?["JOUR"]:["M","AM"];
            const isMonGV=!we&&dow(ey,em,d)===1;
            const gardeMed=getGardeMed2(ey,em,d);
            return slots.map((sl,si)=>(
              <tr key={ey+"-"+em+"-"+d+sl} style={{height:28,borderBottom:si===slots.length-1?"1px solid var(--border)":"1px solid var(--border2)",...(we?{background:"var(--bg-we)"}:{}),...(isT?{background:"var(--bg-td)"}:{}),...(si===0&&isMonGV?{boxShadow:"0 -2px 0 0 var(--border)"}:{})}}>
                {si===0&&<td style={{...S.tdFix,position:"sticky",left:0,zIndex:10,verticalAlign:"middle",minWidth:C0,background:isVac&&isVac(ey,em,d)?"var(--vac-bg)":"var(--td-fix)"}} rowSpan={slots.length}>
                  <div style={{fontWeight:800,color:isT?"var(--today-c)":we?"#92400e":"var(--txt)",fontSize:12,fontFamily:"'JetBrains Mono',monospace",textAlign:"center"}}>{d}{viewPeriod&&<div style={{fontSize:10,color:"var(--txt2)",fontWeight:700,fontFamily:"sans-serif",lineHeight:1.2}}>{MOIS[em]}</div>}</div>
                  <div style={{fontSize:8,color:"var(--txt3)",textTransform:"uppercase",textAlign:"center"}}>{JOURSC[dow(ey,em,d)]}</div>
                </td>}
                <td style={{...S.tdFix,position:"sticky",left:C0,zIndex:9,fontSize:9,color:"var(--txt3)",fontWeight:700,textAlign:"center",background:we?"var(--bg-we)":"var(--td-fix)",minWidth:C1,padding:"2px"}}>{SLOTS[sl]}</td>
                {si===0&&showGarde&&<td rowSpan={slots.length} style={{...S.tdFix,
                  borderRight:"2px solid var(--border)",
                  minWidth:CG,padding:"2px",verticalAlign:"middle",
                  cursor:isEdit?"pointer":"default",
                  background:we?"var(--bg-we)":gardeMed?"var(--garde-bg)":"var(--td-fix)"}}
                  onClick={()=>{ if(!isEdit)return; setGardeSearch(""); setPickGardeDayFull({d,y:ey,m:em}); }}>
                  {gardeMed&&<div style={{display:"flex",flexDirection:"column",alignItems:"center",gap:2}}>
                    <div style={{width:20,height:20,borderRadius:"50%",background:gardeMed.color,display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:8,fontWeight:800}}>{gardeMed.init}</div>
                  </div>}
                </td>}
                {meds.map(med=>{
                  const es=getEntries(med.id,ey,em,d,sl);
                  const bl=es[0]&&es[0]._blocked;
                  const noteT=notes[nk(med.id,ey,em,d,sl)];
                  const astId=getAstreinteForDay?getAstreinteForDay(ey,em,d):null;
                  const isAst=astId!==null&&String(astId)===String(med.id);
                  return <td key={med.id} title={noteT||undefined}
                    style={{...S.td,...(we?S.tdWE:{}),...(isAst?{background:"var(--ast-bg)",boxShadow:"inset 0 0 0 1px var(--ast-bord)"}:{}),...(bl?{background:"var(--bg)",opacity:.4,cursor:"default"}:{cursor:isEdit?"pointer":"default"}),display:"table-cell",verticalAlign:"middle"}}
                    onClick={bl||!isEdit?undefined:()=>onCell(med.id,ey,em,d,sl)}>
                    {!bl&&<div style={{display:"flex",flexWrap:"wrap",justifyContent:"center",alignItems:"center",gap:1}}>
                      {es.map((e,i)=>{const a=e.acteId?acteById(e.acteId):null;return a?<Badge key={i} a={a} salle={e.salle} hideSalle={true} hasNote={!!noteT}/>:null;})}
                    </div>}
                  </td>;
                })}
              </tr>
            ))
          })}
        </tbody>
      </table>
    </div>
    </>
  );
}

/* ════ SITE VIEW (CHL/CHB) ════ */
function SiteView({site,year,month,prevM,nextM,actes,medecins,getEntries,salleOcc,allDays,isEdit,orient,setOrient,onPickSite,notes={},salleReg=[],darkMode,setDarkMode,showFull,setShowFull,viewPeriod,allDays4,setViewPeriod}){
  const today=new Date();
  const ANGIO_SALLES_ALL=["Angio-1","Angio-2","Angio-3"];
  const EXCL_SALLES=site==="CHL"?[S_STIM,S_EEP,S_EE_CHB,...ANGIO_SALLES_ALL]:site==="ANGIO"?[]:[S_STIM,S_EEP,S_EE_CHL,...ANGIO_SALLES_ALL];
  const ANGIO_SALLES=["Angio-1","Angio-2","Angio-3"];
  const FOP_SALLES=["Angio-FOP"];
  const EXCL_IDS=site==="CHL"?["BIP"]:[];
  const siteActes=actes.filter(a=>{
    if(site==="ANGIO") return ["CORO","TAVI","FOP"].includes(a.id)||(a.salles||[]).some(s=>String(s).startsWith("Angio"));
    return (a.site===site||a.site==="tous")&&a.hasSalle&&!a.isSystem
    &&!a.salles.every(s=>EXCL_SALLES.includes(s))&&!EXCL_IDS.includes(a.id);});
  // Effective days for 4M mode
  const sv_today=new Date();
  const svEffDays=useMemo(()=>{
    const p=perStart(year,month);
    const base=perDaysList(p.sy,p.sm);
    if(!showFull){const tod=new Date();tod.setHours(0,0,0,0);return base.filter(({y:ey3,m:em3,d})=>new Date(ey3,em3,d)>=tod);}
    return base;
  },[year,month,showFull,PCFG.len,PCFG.startM]);

  const _chlSalles=["CHL-1","CHL-2","CHL-3","CHL-4","CHL-5","CHL-6","CHL-7","Holter","HC-Exam"];
  const _chbSalles=["CHB-1","CHB-2","CHB-3","CHB-VASC","EE-CHB","Rythmo-CHB","CHB-BIP"];
  const _robustSalles=site==="CHL"?_chlSalles:site==="CHB"?_chbSalles:null;
  const _regS=(salleReg||[]).filter(x=>Array.isArray(x.s)?x.s.indexOf(site)>=0:x.s===site).map(x=>x.n);
  const _uniq=(arr)=>arr.filter((s,i2,a2)=>s&&a2.indexOf(s)===i2);
  const _recapCols=actes.filter(a=>acteRecapIn(a,site)).map(a=>a.id==="BIP"?"CHB-BIP":"RECAP:"+a.id);
  const _legacy=site==="ANGIO"?siteActes.flatMap(a=>a.salles||[]).filter(s=>String(s).startsWith("Angio")):(_robustSalles||[...new Set(siteActes.filter(a=>a.id!=="BIP").flatMap(a=>a.salles||[]))]);
  const _allSallesBase=_uniq(_regS.concat(_legacy).filter(s=>s!=="CHB-BIP"));
  const allSalles=_allSallesBase.concat(_recapCols);
  const wdays=svEffDays; // keep full {y,m,d} objects
  const siteColor=site==="CHL"?"#388bfd":site==="ANGIO"?"#76a5af":"#3fb950";

  function renderCell(salle,d,sl,ry,rm){
    if(ry===undefined)ry=year;
    if(rm===undefined)rm=month;
    const isTdRC=d===sv_today.getDate()&&rm===sv_today.getMonth()&&ry===sv_today.getFullYear();
    // CHB-BIP pseudo-column: show all BIP entries across CHB-1/2/3
    if(salle==="CHB-BIP"||String(salle).indexOf("RECAP:")===0){
      const _rId=salle==="CHB-BIP"?"BIP":salle.slice(6);
      const bipActe=actes.find(a=>a.id===_rId);
      if(!bipActe)return <td key={"bip"+d+sl} style={{...S.td}}/>;
      const bipOcc2=medecins.flatMap(med=>{
        const es=getEntries(med.id,ry,rm,d,sl);
        return es.filter(e=>e.acteId===_rId).map(e=>({med,acte:bipActe,rs:e.salle}));
      });
      return(
        <td key={"bip"+d+sl} style={{...S.td,borderLeft:"3px solid var(--border)",cursor:isEdit?"pointer":"default",padding:2,verticalAlign:"middle",textAlign:"center"}}
          onClick={()=>isEdit&&onPickSite({salle,siteActes:[bipActe],d,sl,y:year,m:month})}>
          {bipOcc2.map(({med,acte,rs},i)=>(
            <div key={i} style={{display:"flex",alignItems:"center",gap:3,margin:"1px 0"}}>
              <div style={{width:22,height:22,borderRadius:"50%",background:med.color,display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:9,fontWeight:800,flexShrink:0}}>{med.init}</div>
              <span style={{fontSize:10,fontWeight:600,color:"var(--txt)",whiteSpace:"nowrap"}}>{med.nom}</span>
            </div>
          ))}
        </td>
      );
    }
    const salleActes=siteActes.filter(a=>a.salles.includes(salle));
    const occ=[];
    salleActes.forEach(acte=>{
      const o=salleOcc(acte.id,ry,rm,d,sl);
      (o[salle]||[]).forEach(med=>{if(!occ.find(x=>x.med.id===med.id))occ.push({med,acte});});
    });
    const conflict=occ.length>1;
    const noteTips=occ.map(({med})=>notes[nk(med.id,year,month,d,sl)]).filter(Boolean).join(" | ");
    return(
      <td key={`${salle}-${d}-${sl}`} title={noteTips||undefined}
        style={{...S.td,...(conflict?S.tdConfl:{}),...(isTdRC?{background:"var(--bg-td)"}:{}),padding:2,cursor:isEdit?"pointer":"default"}}
        onClick={isEdit?()=>onPickSite({salle,siteActes:salleActes,d,sl,y:year,m:month}):undefined}>
        <div style={{display:"flex",flexWrap:"wrap",justifyContent:"center",alignItems:"center",gap:2}}>
        {occ.map(({med,acte},i)=>(
          <div key={i} style={{display:"flex",alignItems:"center",gap:1}}>
            <div style={{width:18,height:18,borderRadius:"50%",background:med.color,display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:7,fontWeight:800,flexShrink:0}}>{med.init}</div>
            <Badge a={acte} hasNote={!!notes[nk(med.id,year,month,d,sl)]}/>
          </div>
        ))}
        </div>
      </td>
    );
  }

  const hdr=(
    <div style={S.bar}>
      <div style={{display:"flex",alignItems:"center",gap:8}}>
        <button onClick={prevM} style={S.arr}>‹</button>
        <h2 style={S.mTit}><span style={{color:siteColor}}>{site==="ANGIO"?"🔬 PT Angio":site}</span> — {(MOIS[perStart(year,month).sm]+" — "+MOIS[(perStart(year,month).sm+PCFG.len-1)%12]+" "+perStart(year,month).sy)}</h2>
        <button onClick={nextM} style={S.arr}>›</button>
      </div>
      <div style={{display:"flex",gap:4,alignItems:"center",marginLeft:"auto"}}>
        
        <button onClick={()=>setDarkMode(d=>!d)} style={{...S.arr,fontSize:13,width:30}}>{darkMode?"☀️":"🌓"}</button>
        <button onClick={()=>setShowFull(f=>!f)} title={showFull?"Depuis aujourd'hui":"Mois complet"} style={{...S.arr,fontSize:16,width:32,color:showFull?"var(--today-c)":"var(--txt2)",border:`1px solid ${showFull?"var(--today-c)":"var(--border)"}`}}>{showFull?"📅":"🗓️"}</button>
      </div>
    </div>
  );

  if(orient==="H")return(
    <div>{hdr}
      <div style={{overflowX:"auto",overflowY:"auto",maxHeight:"calc(100vh - 110px)",borderRadius:8,border:"1px solid var(--border)"}}>
        <table style={{borderCollapse:"collapse"}}>
          <thead>
            <tr>
              <th style={{...S.thFix,position:"sticky",top:0,left:0,zIndex:40,minWidth:110}}>Salle</th>
              {wdays.map(({y:wY,m:wM,d})=>{const isT=d===today.getDate()&&wM===today.getMonth()&&wY===today.getFullYear();const we=isWE(wY,wM,d);return <th key={d+wM+wY} colSpan={we?1:2} style={{...S.th,...(we?S.thWE:{}),...(isT?S.thTD:{}),minWidth:we?22:58,position:"sticky",top:0,zIndex:20}}><div style={S.thN}>{d}</div>{viewPeriod&&<div style={{fontSize:7,color:"var(--txt3)",fontWeight:600}}>{MOIS[wM]}</div>}<div style={S.thJ}>{["D","L","Ma","Me","J","V","S"][dow(wY,wM,d)]}</div></th>;})}
            </tr>
            <tr>
              <th style={{...S.thFix,position:"sticky",top:"24px",left:0,zIndex:39}}></th>
              {wdays.map(({y:wY,m:wM,d})=>isWE(wY,wM,d)?<th key={d+wM+wY} style={{...S.th,...S.thWE,fontSize:8,padding:"2px 1px",position:"sticky",top:"24px",zIndex:19}}></th>:["M","AM"].map(sl=><th key={wY+"-"+wM+"-"+d+sl} style={{...S.th,fontSize:8,color:"var(--txt3)",padding:"2px 1px",position:"sticky",top:"24px",zIndex:19}}>{SLOTS[sl]}</th>))}
            </tr>
          </thead>
          <tbody>
            {allSalles.map(salle=>(
              <tr key={salle} style={{borderBottom:"1px solid var(--border2)"}}>
                <td style={{...S.tdFix,position:"sticky",left:0,zIndex:5}}>
                  <div style={{fontWeight:700,fontSize:11,fontFamily:"'JetBrains Mono',monospace",color:"var(--txt)"}}>{salle==="CHB-BIP"?"BIP":String(salle).indexOf("RECAP:")===0?((actes.find(a2=>a2.id===salle.slice(6))||{}).short||salle.slice(6)):salle}</div>
                  <div style={{fontSize:8,color:"var(--txt3)"}}>{(salle==="CHB-BIP"||String(salle).indexOf("RECAP:")===0)?"↩ reprise activité":siteActes.filter(a=>a.id!=="BIP"&&a.salles.includes(salle)).map(a=>a.short).join(", ")}</div>
                </td>
                {wdays.map(({y:wY,m:wM,d})=>isWE(wY,wM,d)?<td key={d+wM+wY} style={{...S.td,...S.tdWE,padding:2}}/>:["M","AM"].map(sl=>renderCell(salle,d,sl,wY,wM)))}
              </tr>
            ))}
          </tbody>
        </table>
      </div>
    </div>
  );

  return(
    <div>{hdr}
      <div style={{overflowX:"auto",overflowY:"auto",maxHeight:"calc(100vh - 110px)",borderRadius:8,border:"1px solid var(--border)"}}>
        <table style={{borderCollapse:"collapse"}}>
          <thead>
            <tr>
              <th style={{...S.thFix,position:"sticky",top:0,left:0,zIndex:40,minWidth:42}}>Jour</th>
              <th style={{...S.thFix,position:"sticky",top:0,left:42,zIndex:40,minWidth:24,borderRight:"2px solid var(--border)"}}>Sl</th>
              {allSalles.map(salle=><th key={salle} style={{...S.th,minWidth:80,position:"sticky",top:0,zIndex:20}}><div style={{fontWeight:800,fontSize:10,color:"var(--txt)",fontFamily:"'JetBrains Mono',monospace"}}>{salle==="CHB-BIP"?"BIP":String(salle).indexOf("RECAP:")===0?((actes.find(a2=>a2.id===salle.slice(6))||{}).short||salle.slice(6)):salle}</div></th>)}
            </tr>
          </thead>
          <tbody>
            {wdays.map(({y:wY,m:wM,d})=>{
              const isT=d===today.getDate()&&wM===today.getMonth()&&wY===today.getFullYear();
              const dSV=dow(wY,wM,d), weSV=isWE(wY,wM,d), isMonSV=dSV===1&&!weSV;
              if(weSV) return(
                <tr key={wY+"-"+wM+"-"+d+"we"} style={{background:"var(--bg-we)",borderBottom:"1px solid var(--border)",height:28}}>
                  <td colSpan={2} style={{...S.tdFix,position:"sticky",left:0,zIndex:10,background:"var(--bg-we)"}}>
                    <div style={{fontWeight:800,color:"#92400e",fontSize:11,fontFamily:"'JetBrains Mono',monospace",textAlign:"center"}}>{d}{viewPeriod&&<span style={{fontSize:7,color:"#92400e",fontWeight:600,marginLeft:2}}>{MOIS[wM].slice(0,4)}</span>} {JOURSC[dSV]}</div>
                  </td>
                  {allSalles.map(s=><td key={s} style={{...S.td,...S.tdWE}}/>)}
                </tr>
              );
              return["M","AM"].map((sl,si)=>(
                <tr key={wY+"-"+wM+"-"+d+sl} style={{borderBottom:si===1?"1px solid var(--border)":"1px solid var(--border2)",...(isT?{background:"var(--bg-td)"}:{}),...(isMonSV&&si===0?{borderTop:"3px solid var(--border)"}:{})}}>
                  {si===0&&<td style={{...S.tdFix,position:"sticky",left:0,zIndex:10,verticalAlign:"middle",minWidth:42}} rowSpan={2}>
                    <div style={{fontWeight:800,color:isT?"var(--today-c)":"var(--txt)",fontSize:12,fontFamily:"'JetBrains Mono',monospace",textAlign:"center"}}>{d}{viewPeriod&&<div style={{fontSize:8,color:"var(--txt3)",fontWeight:600}}>{MOIS[wM]}</div>}</div>
                    <div style={{fontSize:8,color:"var(--txt3)",textTransform:"uppercase",textAlign:"center"}}>{JOURSC[dSV]}</div>
                  </td>}
                  <td style={{...S.tdFix,position:"sticky",left:42,zIndex:9,fontSize:9,color:"var(--txt3)",fontWeight:700,textAlign:"center",background:"var(--td-fix)",borderRight:"2px solid var(--border)",minWidth:24,padding:"2px"}}>{SLOTS[sl]}</td>
                  {allSalles.map(salle=>renderCell(salle,d,sl,wY,wM))}
                </tr>
              ));
            })}
          </tbody>
        </table>
      </div>
    </div>
  );
}

/* ════ ACT TAB VIEW (PT Cardio / PT Angio) ════ */
function ActTabView({title,titleColor,rows,year,month,prevM,nextM,medecins,actes,getEntries,allDays,isEdit,orient,setOrient,onPickAct,darkMode,setDarkMode,showFull,setShowFull,viewPeriod,allDays4,setViewPeriod}){
  const today=new Date();
  const atvEffDays2=useMemo(()=>{
    const p=perStart(year,month);
    const base=perDaysList(p.sy,p.sm);
    if(!showFull){const tod=new Date();tod.setHours(0,0,0,0);return base.filter(({y:ey3,m:em3,d})=>new Date(ey3,em3,d)>=tod);}
    return base;
  },[year,month,showFull,PCFG.len,PCFG.startM]);
  const wdays=atvEffDays2; // keep full objects

  function getOcc(row,d,sl,ry,rm){
    if(!ry)ry=year; if(!rm&&rm!==0)rm=month;
    const occ=[];
    row.ids.forEach(acteId=>{
      medecins.forEach(med=>{
        getEntries(med.id,ry,rm,d,sl).forEach(e=>{
          const match=row.salle?(e.acteId===acteId&&e.salle===row.salle):e.acteId===acteId;
          if(match&&!occ.find(x=>x.med.id===med.id&&x.acteId===acteId)){
            const acte=actes.find(a=>a.id===acteId)||{short:acteId,color:row.color,bg:"#111"};
            occ.push({med,acte,salle:e.salle||null});
          }
        });
      });
    });
    return occ;
  }

  function renderActCell(row,d,sl,ry,rm){
    if(!ry)ry=year;
    if(!rm&&rm!==0)rm=month;
    const isTd=d===today.getDate()&&rm===today.getMonth()&&ry===today.getFullYear();
    if(isWE(ry,rm,d)) return <td key={`${row.label}-${d}-${sl}`} style={{...S.td,...S.tdWE,padding:2}}/>;
    const occ=getOcc(row,d,sl,ry,rm);
    return(
      <td key={`${row.label}-${d}-${sl}`} style={{...S.td,...(isTd?{background:"var(--bg-td)"}:{}),padding:2,cursor:isEdit?"pointer":"default"}}
        onClick={isEdit?()=>onPickAct({row,d,sl,y:ry,m:rm}):undefined}>
        <div style={{display:"flex",flexWrap:"wrap",justifyContent:"center",alignItems:"center",gap:2}}
          onClick={e=>{e.stopPropagation();if(isEdit)onPickAct({row,d,sl,y:ry,m:rm});}}>
        {occ.map(({med,acte,salle},i)=>{
          const monoActe=(row.ids||[]).length===1&&!row.multiActe;
          return(
          <div key={i} style={{display:"flex",alignItems:"center",gap:2}}>
            <div style={{width:18,height:18,borderRadius:"50%",background:med.color,display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:7,fontWeight:800,flexShrink:0}}>{med.init}</div>
            {monoActe
              ?<span style={{fontSize:9,fontWeight:600,color:"var(--txt)",whiteSpace:"nowrap"}}>{med.nom}</span>
              :<Badge a={acte}/>}
          </div>
        );})}
        </div>
        {occ.length===0&&<div style={{color:"var(--border)",textAlign:"center",fontSize:13}}>·</div>}
      </td>
    );
  }

  const hdr=(
    <div style={S.bar}>
      <div style={{display:"flex",alignItems:"center",gap:8}}>
        <button onClick={prevM} style={S.arr}>‹</button>
        <h2 style={S.mTit}><span style={{color:titleColor}}>{title}</span> — {(MOIS[perStart(year,month).sm]+" — "+MOIS[(perStart(year,month).sm+PCFG.len-1)%12]+" "+perStart(year,month).sy)}</h2>
        <button onClick={nextM} style={S.arr}>›</button>
      </div>
      <div style={{display:"flex",gap:4,alignItems:"center",marginLeft:"auto"}}>
        
        <button onClick={()=>setDarkMode(d=>!d)} style={{...S.arr,fontSize:13,width:30}}>{darkMode?"☀️":"🌓"}</button>
        <button onClick={()=>setShowFull(f=>!f)} title={showFull?"Depuis aujourd'hui":"Mois complet"} style={{...S.arr,fontSize:16,width:32,color:showFull?"var(--today-c)":"var(--txt2)",border:`1px solid ${showFull?"var(--today-c)":"var(--border)"}`}}>{showFull?"📅":"🗓️"}</button>
      </div>
    </div>
  );

  if(orient==="H")return(
    <div>{hdr}
      <div style={{overflowX:"auto",overflowY:"auto",maxHeight:"calc(100vh - 110px)",borderRadius:8,border:"1px solid var(--border)"}}>
        <table style={{borderCollapse:"collapse"}}>
          <thead>
            <tr>
              <th style={{...S.thFix,position:"sticky",top:0,left:0,zIndex:40,minWidth:120}}>Activité</th>
              {wdays.map(({y:wY,m:wM,d})=>{const isT=d===today.getDate()&&wM===today.getMonth()&&wY===today.getFullYear();const we=isWE(wY,wM,d);return <th key={d+wM+wY} colSpan={we?1:2} style={{...S.th,...(we?S.thWE:{}),...(isT?S.thTD:{}),minWidth:we?22:68,position:"sticky",top:0,zIndex:20}}><div style={S.thN}>{d}</div>{viewPeriod&&<div style={{fontSize:7,color:"var(--txt3)",fontWeight:600}}>{MOIS[wM]}</div>}<div style={S.thJ}>{["D","L","Ma","Me","J","V","S"][dow(wY,wM,d)]}</div></th>;})}
            </tr>
            <tr>
              <th style={{...S.thFix,position:"sticky",top:"24px",left:0,zIndex:39}}></th>
              {wdays.map(({y:wY,m:wM,d})=>isWE(wY,wM,d)?<th key={d+wM+wY} style={{...S.th,...S.thWE,padding:"2px 1px",position:"sticky",top:"24px",zIndex:19}}></th>:["M","AM"].map(sl=><th key={wY+"-"+wM+"-"+d+sl} style={{...S.th,fontSize:8,color:"var(--txt3)",padding:"2px 1px",position:"sticky",top:"24px",zIndex:19}}>{SLOTS[sl]}</th>))}
            </tr>
          </thead>
          <tbody>
            {rows.map(row=>(
              <tr key={row.label} style={{borderBottom:"1px solid var(--border2)"}}>
                <td style={{...S.tdFix,position:"sticky",left:0,zIndex:5}}>
                  <div style={{fontWeight:700,fontSize:11,fontFamily:"'JetBrains Mono',monospace",color:darkMode?lightenHex(row.color,.55):row.color}}>{row.label}</div>
                </td>
                {wdays.map(({y:wY,m:wM,d})=>isWE(wY,wM,d)?<td key={d+wM+wY} style={{...S.td,...S.tdWE,padding:2}}/>:["M","AM"].map(sl=>renderActCell(row,d,sl,wY,wM)))}
              </tr>
            ))}
          </tbody>
        </table>
      </div>
    </div>
  );

  return(
    <div>{hdr}
      <div style={{overflowX:"auto",overflowY:"auto",maxHeight:"calc(100vh - 110px)",borderRadius:8,border:"1px solid var(--border)"}}>
        <table style={{borderCollapse:"collapse"}}>
          <thead>
            <tr>
              <th style={{...S.thFix,position:"sticky",top:0,left:0,zIndex:40,minWidth:42}}>Jour</th>
              <th style={{...S.thFix,position:"sticky",top:0,left:42,zIndex:40,minWidth:24,borderRight:"2px solid var(--border)"}}>Sl</th>
              {rows.map(row=><th key={row.label} style={{...S.th,minWidth:95,position:"sticky",top:0,zIndex:20}}><div style={{fontWeight:800,fontSize:10,color:darkMode?lightenHex(row.color,.55):row.color,fontFamily:"'JetBrains Mono',monospace"}}>{row.label}</div></th>)}
            </tr>
          </thead>
          <tbody>
            {wdays.map(({y:wY,m:wM,d})=>{
              const isT=d===today.getDate()&&wM===today.getMonth()&&wY===today.getFullYear();
              const dAT=dow(wY,wM,d), weAT=isWE(wY,wM,d), isMonAT=dAT===1&&!weAT;
                if(weAT) return(
                  <tr key={wY+"-"+wM+"-"+d+"we"} style={{background:"var(--bg-we)",borderBottom:"1px solid var(--border)",height:28}}>
                    <td colSpan={2} style={{...S.tdFix,position:"sticky",left:0,zIndex:10,background:"var(--bg-we)"}}>
                      <div style={{fontWeight:800,color:"#92400e",fontSize:11,fontFamily:"'JetBrains Mono',monospace",textAlign:"center"}}>{d}{viewPeriod&&<span style={{fontSize:7,color:"#92400e",fontWeight:600,marginLeft:2}}>{MOIS[wM].slice(0,4)}</span>} {JOURSC[dAT]}</div>
                    </td>
                    {rows.map(r=><td key={r.label} style={{...S.td,...S.tdWE}}/>)}
                  </tr>
                );
                return["M","AM"].map((sl,si)=>(
                <tr key={wY+"-"+wM+"-"+d+sl} style={{borderBottom:si===1?"1px solid var(--border)":"1px solid var(--border2)",...(isT?{background:"var(--bg-td)"}:{}),...(isMonAT&&si===0?{borderTop:"3px solid var(--border)"}:{})}}>
                  {si===0&&<td style={{...S.tdFix,position:"sticky",left:0,zIndex:10,verticalAlign:"middle",minWidth:42}} rowSpan={2}>
                    <div style={{fontWeight:800,color:isT?"var(--today-c)":"var(--txt)",fontSize:12,fontFamily:"'JetBrains Mono',monospace",textAlign:"center"}}>{d}{viewPeriod&&<div style={{fontSize:7,color:"var(--txt3)",fontWeight:600,lineHeight:1}}>{MOIS[wM]}</div>}</div>
                    <div style={{fontSize:8,color:"var(--txt3)",textTransform:"uppercase",textAlign:"center"}}>{JOURSC[dAT]}</div>
                  </td>}
                  <td style={{...S.tdFix,position:"sticky",left:42,zIndex:9,fontSize:9,color:"var(--txt3)",fontWeight:700,textAlign:"center",background:"var(--td-fix)",borderRight:"2px solid var(--border)",minWidth:24,padding:"2px"}}>{SLOTS[sl]}</td>
                  {rows.map(row=>renderActCell(row,d,sl,wY,wM))}
                </tr>
              ));
            })}
          </tbody>
        </table>
      </div>
    </div>
  );
}

/* ════ GARDE VIEW ════ */
function GardeView({year,month,prevM,nextM,medecins,getEntry,allDays,isEdit,orient,setOrient,applyGarde,isMedAvailable,plan,setPlan,darkMode,setDarkMode,showFull,setShowFull,viewPeriod,allDays4,setViewPeriod,tourMed,gardeAvoid,gardeWish,toast}){
  const today=new Date();
  // Période globale pour les gardes
  const {sy:gvSy,sm:gvSm}=perStart(year,month);
  const gvEffDays=useMemo(()=>{
    const days=perDaysList(gvSy,gvSm);
    if(!showFull){const tod=new Date();tod.setHours(0,0,0,0);return days.filter(({y:ey3,m:em3,d})=>new Date(ey3,em3,d)>=tod);}
    return days;
  },[gvSm,gvSy,showFull,PCFG.len]);

  const [gvSwapOpen,setGvSwapOpen]=React.useState(false);
  const exportGardesCSV=()=>{
    const rows=[["Date","Jour","Garde"]];
    const JX=["Dim","Lun","Mar","Mer","Jeu","Ven","Sam"];
    gvEffDays.forEach(({y:gy,m:gm,d:gd})=>{
      const gm2=getGardeMed2(gy,gm,gd);
      rows.push([gd+"/"+(gm+1)+"/"+gy,JX[dow(gy,gm,gd)],gm2?(gm2.prenom+" "+gm2.nom):""]);
    });
    const csv=rows.map(r=>r.map(v=>'"'+String(v).replace(/"/g,'""')+'"').join(";")).join("\n");
    const blob=new Blob(["\ufeff"+csv],{type:"text/csv;charset=utf-8"});
    const a=document.createElement("a");
    a.href=URL.createObjectURL(blob);
    a.download="gardes.csv";
    a.click();
  };
  const gvIsAbs=(mid,y2,m2,d2)=>{
    const sls=isWE(y2,m2,d2)?["JOUR"]:["M","AM"];
    return sls.some(sl=>{
      const e=getEntry(mid,y2,m2,d2,sl);
      const a=e&&(Array.isArray(e)?(e[0]&&e[0].acteId):e.acteId);
      return ["ABSENCE","FORM","FORMATION"].includes(a);
    });
  };
  const [pickerDay,setPickerDay]=React.useState(null);

  /* ═══ Répartition automatique des gardes ═══ */
  const [gardeModal,setGardeModal]=React.useState(false);
  const [lastGReport,setLastGReport]=React.useState(null);
  const [gMax,setGMax]=React.useState({}); // {medId: maxGardes} optionnel
  const gardeMeds=medecins.filter(m=>m.garde);
  const FACT={less:0.75,normal:1,more:1.25};
  // Tous les jours de la période (complets, indépendants de showFull)
  const gvAllDays=React.useMemo(()=>perDaysList(gvSy,gvSm),[gvSy,gvSm,PCFG.len]);
  const catOf=(y2,m2,d2)=>{
    if(isFerie(y2,m2,d2))return "dim";
    const dw=dow(y2,m2,d2);
    if(dw===6)return "sam";
    if(dw===0)return "dim";
    const nx=new Date(y2,m2,d2+1);
    if(isFerie(nx.getFullYear(),nx.getMonth(),nx.getDate()))return "ven";
    return dw===5?"ven":dw===4?"jeu":"sem";
  };
  const GCATS=["sem","jeu","ven","sam","dim"];
  const hasGardeAlready=(y2,m2,d2)=>{
    const dw=dow(y2,m2,d2);const slot=(dw===6||dw===0)?"JOUR":"N";
    const dm=plan[sk(y2,m2,d2,slot)]||{};
    return Object.keys(dm).some(mid=>{const e=Array.isArray(dm[mid])?dm[mid][0]:dm[mid];return e&&e.acteId==="GARDE";});
  };
  const isAbsFor=(medId,y2,m2,d2)=>{
    const es=[...(getEntry?[]:[]),];
    const check=(sl)=>{const dm=plan[sk(y2,m2,d2,sl)]||{};const e=dm[medId];const a=Array.isArray(e)?(e[0]&&e[0].acteId):(e&&e.acteId);return ["ABSENCE","FORM","FORMATION"].includes(a);};
    return check("M")||check("AM")||check("JOUR");
  };
  const inTourWeek=(medId,y2,m2,d2)=>{
    const wk=wKey(y2,m2,d2);const wm=(tourMed||{})[wk]||{HC:[],USIC:[]};
    return [...(wm.HC||[]),...(wm.USIC||[])].map(String).includes(String(medId));
  };
  const runGardeAuto=()=>{
    const tod=new Date();tod.setHours(0,0,0,0);
    // Jours à attribuer : période complète, futurs (>= aujourd'hui), sans garde existante
    const days=gvAllDays.filter(({y:y2,m:m2,d:d2})=>new Date(y2,m2,d2)>=tod&&!hasGardeAlready(y2,m2,d2));
    if(days.length===0){toast("Aucun jour à attribuer (gardes déjà posées ou période passée)","info");return;}
    // Cibles pondérées par catégorie
    const weights={};let wSum=0;
    gardeMeds.forEach(m=>{weights[m.id]=FACT[m.gardeFactor||"normal"]||1;wSum+=weights[m.id];});
    const catCount={sem:0,jeu:0,ven:0,sam:0,dim:0};
    days.forEach(({y:y2,m:m2,d:d2})=>{catCount[catOf(y2,m2,d2)]++;});
    const maxOf=(mid)=>{const v=parseInt(gMax[mid]);return isNaN(v)?Infinity:v;};
    const target={};
    gardeMeds.forEach(m=>{target[m.id]={};GCATS.forEach(c=>{target[m.id][c]=catCount[c]*weights[m.id]/wSum;});});
    // Si un maximum est fixé sous la cible : réduire les cibles par catégorie au prorata,
    // et redistribuer le surplus sur les autres (proportionnellement à leur poids)
    let surplus=0,openW=0;
    gardeMeds.forEach(m=>{
      const tot=GCATS.reduce((s,c)=>s+target[m.id][c],0);
      const mx=maxOf(m.id);
      if(mx<tot){const f2=tot>0?mx/tot:0;GCATS.forEach(c=>{target[m.id][c]*=f2;});surplus+=tot-mx;}
      else openW+=weights[m.id];
    });
    if(surplus>0&&openW>0){
      gardeMeds.forEach(m=>{
        const tot=GCATS.reduce((s,c)=>s+target[m.id][c],0);
        if(maxOf(m.id)>=tot+0.001){
          const share=surplus*weights[m.id]/openW;
          const f3=tot>0?(tot+share)/tot:1;
          GCATS.forEach(c=>{target[m.id][c]*=f3;});
        }
      });
    }
    const canTake=(m,y2,m2,d2)=>{
      const dw=dow(y2,m2,d2);
      if((m.gardeDays||{})[String(dw)]===false)return false;
      if(isAbsFor(m.id,y2,m2,d2))return false;
      if(inTourWeek(m.id,y2,m2,d2))return false;
      const nx=new Date(y2,m2,d2+1);
      if(isAbsFor(m.id,nx.getFullYear(),nx.getMonth(),nx.getDate()))return false; // repos de garde impossible
      if(((gardeAvoid||{})[dKey(y2,m2,d2)]||{})[m.id])return false;
      return true;
    };
    // Toutes les gardes existantes par médecin (pour l'écart minimal de 3 jours)
    const exG={}; // {medId:Set("y-m-d")}
    gvAllDays.forEach(({y:y2,m:m2,d:d2})=>{
      const dw=dow(y2,m2,d2);
      const slot=(dw===6||dw===0)?"JOUR":"N";
      const dm=plan[sk(y2,m2,d2,slot)]||{};
      Object.keys(dm).forEach(mid=>{
        const e=Array.isArray(dm[mid])?dm[mid][0]:dm[mid];
        if(!e||e.acteId!=="GARDE")return;
        if(!exG[mid])exG[mid]=new Set();
        exG[mid].add(y2+"-"+m2+"-"+d2);
      });
    });
    // Gardes existantes (posées manuellement) par médecin/semaine : jeudi et week-end
    const exJeu={},exWE={};
    gvAllDays.forEach(({y:y2,m:m2,d:d2})=>{
      const dw=dow(y2,m2,d2);
      if(dw!==4&&dw!==6&&dw!==0)return;
      const slot=(dw===6||dw===0)?"JOUR":"N";
      const dm=plan[sk(y2,m2,d2,slot)]||{};
      Object.keys(dm).forEach(mid=>{
        const e=Array.isArray(dm[mid])?dm[mid][0]:dm[mid];
        if(!e||e.acteId!=="GARDE")return;
        const wk=wKey(y2,m2,d2);
        if(dw===4){if(!exJeu[mid])exJeu[mid]={};exJeu[mid][wk]=true;}
        else{if(!exWE[mid])exWE[mid]={};exWE[mid][wk]=true;}
      });
    });
    const N_TRIES_G=40;
    let best=null;
    for(let t=0;t<N_TRIES_G;t++){
      const cnt={},catCnt={},lastG={};
      const asJeu={},asWE={};
      const jeuOf=(mid,wk)=>((exJeu[mid]||{})[wk])||((asJeu[mid]||{})[wk]);
      const weOf=(mid,wk)=>((exWE[mid]||{})[wk])||((asWE[mid]||{})[wk]);
      const asG={}; // {medId:Set("y-m-d")} gardes assignées cet essai
      const gapOK=(mid,y3,m3,d3)=>{
        for(let k=-1;k<=1;k+=2){
          const dd=new Date(y3,m3,d3+k);
          const key=dd.getFullYear()+"-"+dd.getMonth()+"-"+dd.getDate();
          if((exG[mid]&&exG[mid].has(key))||(asG[mid]&&asG[mid].has(key)))return false;
        }
        return true;
      };
      const markG=(mid,y3,m3,d3)=>{if(!asG[mid])asG[mid]=new Set();asG[mid].add(y3+"-"+m3+"-"+d3);};
      gardeMeds.forEach(m=>{cnt[m.id]=0;catCnt[m.id]={sem:0,jeu:0,ven:0,sam:0,dim:0};});
      const assign={}; // dateKey -> medId
      let wishMiss=0;
      // 1. Vœux d'abord
      days.forEach(({y:y2,m:m2,d:d2})=>{
        const dk4=dKey(y2,m2,d2);
        const dwW=dow(y2,m2,d2),wkW=wKey(y2,m2,d2);
        const jweOK=(mid)=>{if(dwW===6||dwW===0)return !jeuOf(mid,wkW);if(dwW===4)return !weOf(mid,wkW);return true;};
        const wishers=gardeMeds.filter(m=>((gardeWish||{})[dk4]||{})[m.id]&&canTake(m,y2,m2,d2)&&cnt[m.id]<maxOf(m.id)&&jweOK(m.id)&&gapOK(m.id,y2,m2,d2));
        if(wishers.length>0){
          const m=wishers[Math.floor(Math.random()*wishers.length)];
          assign[dk4]=m.id;cnt[m.id]++;catCnt[m.id][catOf(y2,m2,d2)]++;lastG[m.id]=new Date(y2,m2,d2).getTime();
          if(dwW===4){if(!asJeu[m.id])asJeu[m.id]={};asJeu[m.id][wkW]=true;}
          if(dwW===6||dwW===0){if(!asWE[m.id])asWE[m.id]={};asWE[m.id][wkW]=true;}
          markG(m.id,y2,m2,d2);
        }else if(Object.keys((gardeWish||{})[dk4]||{}).length>0)wishMiss++;
      });
      // 2. Jours les plus contraints d'abord
      const rest=days.filter(({y:y2,m:m2,d:d2})=>!assign[dKey(y2,m2,d2)]);
      const jweOK2=(mid,y3,m3,d3)=>{const dw3=dow(y3,m3,d3),wk3=wKey(y3,m3,d3);if(dw3===6||dw3===0)return !jeuOf(mid,wk3);if(dw3===4)return !weOf(mid,wk3);return true;};
      const nCand=(dd)=>gardeMeds.filter(m=>canTake(m,dd.y,dd.m,dd.d)&&cnt[m.id]<maxOf(m.id)&&jweOK2(m.id,dd.y,dd.m,dd.d)&&gapOK(m.id,dd.y,dd.m,dd.d)).length;
      const sorted=[...rest].sort((a,b)=>nCand(a)-nCand(b));
      let unfilled=0;const unfilledList=[];
      sorted.forEach(({y:y2,m:m2,d:d2})=>{
        const dk4=dKey(y2,m2,d2);const c=catOf(y2,m2,d2);
        let cands=gardeMeds.filter(m=>canTake(m,y2,m2,d2)&&cnt[m.id]<maxOf(m.id)&&jweOK2(m.id,y2,m2,d2)&&gapOK(m.id,y2,m2,d2));
        if(cands.length===0)cands=gardeMeds.filter(m=>canTake(m,y2,m2,d2)&&cnt[m.id]<maxOf(m.id)&&gapOK(m.id,y2,m2,d2)); // dernier recours : accepter jeudi+WE, mais JAMAIS deux jours consécutifs
        if(cands.length===0){unfilled++;unfilledList.push(d2+" "+MOIS[m2].slice(0,4));return;}
        const ts2=new Date(y2,m2,d2).getTime();
        cands.sort((a,b)=>{
          const defA=(target[a.id][c]-catCnt[a.id][c]),defB=(target[b.id][c]-catCnt[b.id][c]);
          if(Math.abs(defB-defA)>0.01)return defB-defA;
          const gapA=lastG[a.id]?ts2-lastG[a.id]:1e12,gapB=lastG[b.id]?ts2-lastG[b.id]:1e12;
          if(gapA!==gapB)return gapB-gapA;
          return Math.random()-0.5;
        });
        const m=cands[0];
        assign[dk4]=m.id;cnt[m.id]++;catCnt[m.id][c]++;lastG[m.id]=ts2;
        const dwA=dow(y2,m2,d2),wkA=wKey(y2,m2,d2);
        if(dwA===4){if(!asJeu[m.id])asJeu[m.id]={};asJeu[m.id][wkA]=true;}
        if(dwA===6||dwA===0){if(!asWE[m.id])asWE[m.id]={};asWE[m.id][wkA]=true;}
        markG(m.id,y2,m2,d2);
      });
      // Score : jours non attribués, écart aux cibles, vœux manqués, gardes rapprochées (<3j)
      let dev=0;gardeMeds.forEach(m=>{GCATS.forEach(c=>{dev+=Math.abs(catCnt[m.id][c]-target[m.id][c]);});});
      const score=unfilled*1000+wishMiss*50+dev*10;
      if(!best||score<best.score)best={assign,score,unfilled,cnt,wishMiss,unfilledList};
      if(best.score===0)break;
    }
    // Application en un seul setPlan (garde + repos de garde le lendemain)
    setPlan(p=>{
      let next={...p};
      Object.keys(best.assign).forEach(dk4=>{
        const[y2,m2,d2]=dk4.split("-").map(Number);
        const my=m2-1;
        const dw=dow(y2,my,d2);
        const gslot=(dw===6||dw===0)?"JOUR":"N";
        const gk=sk(y2,my,d2,gslot);
        next[gk]={...(next[gk]||{}),[best.assign[dk4]]:{acteId:"GARDE",salle:null}};
        const nx=new Date(y2,my,d2+1);
        const ny=nx.getFullYear(),nm=nx.getMonth(),nd=nx.getDate();
        const rSlots=isWE(ny,nm,nd)?["JOUR"]:["M","AM"];
        rSlots.forEach(sl=>{
          const rk=sk(ny,nm,nd,sl);
          const dm={...(next[rk]||{})};
          const ex=dm[best.assign[dk4]];
          const exA=Array.isArray(ex)?(ex[0]&&ex[0].acteId):(ex&&ex.acteId);
          if(!["ABSENCE","GARDE"].includes(exA))dm[best.assign[dk4]]={acteId:"REPOS_GARDE",salle:null};
          next[rk]=dm;
        });
      });
      return next;
    });
    const nA=Object.keys(best.assign).length;
    setLastGReport({
      nA,total:days.length,
      unfilled:best.unfilled,unfilledList:best.unfilledList||[],
      wishMiss:best.wishMiss||0,
      tots:gardeMeds.map(m=>({init:m.init,n:best.cnt[m.id]||0}))
    });
    toast("Gardes attribuées: "+nA+"/"+days.length,"info");
    setGardeModal(false);
  };

  function getGardeMed2(gvY,gvM,d){
    var gy2=gvY||year, gm2=(gvM!==undefined)?gvM:month;
    var dw2=dow(gy2,gm2,d), gardeSlot=(dw2===6||dw2===0)?"JOUR":"N";
    return medecins.find(function(m){var e=getEntry(m.id,gy2,gm2,d,gardeSlot);return e&&e.acteId==="GARDE";});
  }

  function renderGardeCell(d,gy,gm){
    var rgy=gy||year, rgm=(gm!==undefined)?gm:month;
    var we=isWE(rgy,rgm,d);
    var gMed=getGardeMed2(rgy,rgm,d);
    return(
      <td key={"g"+d+rgy+rgm} style={{...S.td,...(we?S.tdWE:{}),padding:2,cursor:isEdit?"pointer":"default"}}
        onClick={isEdit?()=>setPickerDay({d,y:rgy,m:rgm}):undefined}>
        {gMed?(<div style={{display:"flex",alignItems:"center",gap:3,margin:"1px",padding:"1px 3px",borderRadius:4,background:"#1a0000",border:"1px solid #f8514944"}}>
          <div style={{width:18,height:18,borderRadius:"50%",background:gMed.color,display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:8,fontWeight:800}}>{gMed.init}</div>
          <span style={{fontSize:9,fontWeight:700,color:gMed.color}}>{gMed.prenom} {gMed.nom}</span>
        </div>):null}
      </td>
    );
  }

  const wdays=gvEffDays; // keep full objects

  const viewV=(
    <div style={{overflowX:"auto",overflowY:"auto",maxHeight:"calc(100vh - 110px)",borderRadius:8,border:"1px solid var(--border)"}}>
      <table key={showFull?"gvfull":"gvpart"} style={{borderCollapse:"collapse",tableLayout:"fixed"}}>
        <thead>
          <tr>
            <th style={{...S.thFix,position:"sticky",top:0,left:0,zIndex:40,minWidth:80}}>Date</th>
            <th style={{...S.thFix,position:"sticky",top:0,zIndex:20,minWidth:150}}>Garde</th>
          </tr>
        </thead>
        <tbody>
          {gvEffDays.map(({y:gvY,m:gvM,d})=>{
            const isT=d===today.getDate()&&gvM===today.getMonth()&&gvY===today.getFullYear();
            const dw2=dow(gvY,gvM,d),we=isWE(gvY,gvM,d);
            const gMed=getGardeMed2(gvY,gvM,d);
            return(
              <tr key={d+gvM+gvY} style={{height:36,borderBottom:"1px solid var(--border2)",...(we?{background:"var(--bg-we)"}:{}),...(isT?{background:"var(--bg-td)"}:{})}}>
                <td style={{...S.tdFix,position:"sticky",left:0,zIndex:5,textAlign:"center",background:isT?"var(--bg-td)":we?"var(--bg-we)":"var(--td-fix)"}}>
                  <div style={{fontWeight:800,color:isT?"var(--today-c)":we?"#92400e":"var(--txt)",fontSize:13,fontFamily:"'JetBrains Mono',monospace"}}>{d} <span style={{fontSize:9,fontWeight:600}}>{MOIS[gvM].slice(0,4)}</span></div>
                  <div style={{fontSize:9,color:we?"#92400e":isT?"var(--today-c)":"var(--txt3)",fontWeight:600}}>{["Dim","Lun","Mar","Mer","Jeu","Ven","Sam"][dw2]}</div>
                </td>
                <td style={{...S.td,padding:4,cursor:isEdit?"pointer":"default"}} onClick={isEdit?()=>setPickerDay({d,y:gvY,m:gvM}):undefined}>
                  {gMed?(<div style={{display:"flex",alignItems:"center",gap:6,padding:"4px 8px",borderRadius:6,background:gMed.color+"22"}}>
                    <div style={{width:22,height:22,borderRadius:"50%",background:gMed.color,display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:9,fontWeight:800}}>{gMed.init}</div>
                    <span style={{fontSize:12,fontWeight:600,color:"var(--txt)"}}>{gMed.prenom} {gMed.nom}</span>
                  </div>):(<span style={{color:"var(--txt3)",fontSize:11}}>—</span>)}
                </td>
              </tr>
            );
          })}
        </tbody>
      </table>
    </div>
  );

  const viewH=(
    <div style={{overflowX:"auto",overflowY:"auto",maxHeight:"calc(100vh - 110px)",borderRadius:8,border:"1px solid var(--border)"}}>
      <table style={{borderCollapse:"collapse"}}>
        <thead>
          <tr>
            <th style={{...S.thFix,position:"sticky",top:0,left:0,zIndex:40,minWidth:58}}>Garde</th>
            {wdays.map(({y:wY,m:wM,d})=>{
              const isT=d===today.getDate()&&wM===today.getMonth()&&wY===today.getFullYear();
              const we=isWE(wY,wM,d);
              return <th key={d+wM+wY} style={{...S.th,...(we?S.thWE:{}),...(isT?S.thTD:{}),minWidth:we?22:50,position:"sticky",top:0,zIndex:20}}>
                <div style={S.thN}>{d}</div>{viewPeriod&&<div style={{fontSize:7,color:"var(--txt3)",fontWeight:600}}>{MOIS[wM]}</div>}<div style={S.thJ}>{["D","L","Ma","Me","J","V","S"][dow(year,month,d)]}</div>
              </th>;
            })}
          </tr>
        </thead>
        <tbody>
          <tr>
            <td style={{...S.tdFix,position:"sticky",left:0,zIndex:5}}>
              <div style={{fontWeight:800,fontSize:11,color:"#f85149",fontFamily:"'JetBrains Mono',monospace"}}>🌙 Garde</div>
            </td>
            {wdays.map(({y:wY,m:wM,d})=>renderGardeCell(d,wY,wM))}
          </tr>
        </tbody>
      </table>
    </div>
  );

  return(
    <div>
      <div style={S.bar}>
        <div style={{display:"flex",alignItems:"center",gap:8}}>
          <button onClick={prevM} style={S.arr}>‹</button>
          <h2 style={S.mTit}><span style={{color:"#f85149"}}>🌙 Gardes</span> — {MOIS[gvSm]+" — "+MOIS[(gvSm+PCFG.len-1)%12]+" "+gvSy}</h2>
          <button onClick={nextM} style={S.arr}>›</button>
        </div>
        <div style={{display:"flex",gap:4,alignItems:"center",marginLeft:"auto"}}>
          <button onClick={()=>setDarkMode(d=>!d)} style={{...S.arr,fontSize:13,width:30}}>{darkMode?"☀️":"🌓"}</button>
          <button onClick={()=>setShowFull(f=>!f)} title={showFull?"Depuis aujourd'hui":"Mois complet"} style={{...S.arr,fontSize:16,width:32,color:showFull?"var(--today-c)":"var(--txt2)",border:`1px solid ${showFull?"var(--today-c)":"var(--border)"}`}}>{showFull?"📅":"🗓️"}</button>
        </div>
      </div>
      <div style={{display:"flex",gap:6,alignItems:"center",marginBottom:10}}>
          {isEdit&&<button style={{fontSize:11,padding:"3px 12px",borderRadius:6,border:"1.5px solid #7c3aed",background:"rgba(124,58,237,.10)",color:"#7c3aed",fontWeight:800,cursor:"pointer"}} onClick={()=>{setGMax({});setGardeModal(true);}}>⚙️ Répartition auto</button>}
          {isEdit&&<button style={{fontSize:11,padding:"3px 12px",borderRadius:6,border:"1px solid #dc2626",background:"var(--bg2)",color:"#dc2626",fontWeight:700,cursor:"pointer"}} onClick={()=>{
            const lbl=MOIS[gvSm]+" — "+MOIS[(gvSm+PCFG.len-1)%12]+" "+gvSy;
            if(!window.confirm("Retirer TOUTES les gardes et repos de garde de la période "+lbl+" ?"))return;
            if(!window.confirm("Confirmer définitivement ? Cette action retire les gardes posées manuellement comme automatiquement."))return;
            setPlan(p=>{
              let next={...p};
              gvAllDays.forEach(({y:y2,m:m2,d:d2})=>{
                ["M","AM","JOUR","N"].forEach(sl=>{
                  const k=sk(y2,m2,d2,sl);
                  if(!next[k])return;
                  const dm={...next[k]};let changed=false;
                  Object.keys(dm).forEach(mid=>{
                    const e=Array.isArray(dm[mid])?dm[mid][0]:dm[mid];
                    const a=e&&e.acteId;
                    if(a==="GARDE"||a==="REPOS_GARDE"){delete dm[mid];changed=true;}
                  });
                  if(changed)next[k]=dm;
                });
              });
              return next;
            });
            toast("Gardes et repos retirés sur la période","info");
          }}>🗑 Retirer</button>}
          <button onClick={exportGardesCSV} style={{...S.btnP,fontSize:11,padding:"3px 10px"}}>🖨️ Export</button>
      </div>
      {gardeModal&&(
        <Ov onClose={()=>setGardeModal(false)}>
          <div style={{...S.modal,maxWidth:460,maxHeight:"85vh",overflowY:"auto"}} onClick={e=>e.stopPropagation()}>
            <div style={{display:"flex",justifyContent:"space-between",alignItems:"center",marginBottom:8}}>
              <div style={S.mTit2}>⚙️ Répartition automatique des gardes</div>
              <button onClick={()=>setGardeModal(false)} style={S.xBtn}>×</button>
            </div>
            <div style={{fontSize:11,color:"var(--txt3)",marginBottom:10}}>
              Attribue les jours <b>sans garde existante</b>, à partir d'aujourd'hui, sur la période affichée. Respecte : absences/formations, semaines de tour, absence le lendemain (repos de garde), jours autorisés et volume de gardes (réglés dans l'Équipe), et les préférences ⭐/🚫 posées jour par jour.
            </div>
            <table style={{borderCollapse:"collapse",width:"100%",marginBottom:12}}>
              <thead><tr>
                <th style={{textAlign:"left",padding:"3px 6px",fontSize:10,color:"var(--txt3)"}}>Médecin</th>
                <th style={{padding:"3px 6px",fontSize:10,color:"var(--txt3)"}}>Volume</th>
                <th style={{padding:"3px 6px",fontSize:10,color:"var(--txt3)"}}>Max (opt.)</th>
              </tr></thead>
              <tbody>
                {gardeMeds.map(m=>(
                  <tr key={m.id} style={{borderBottom:"1px solid var(--border2)"}}>
                    <td style={{padding:"4px 6px",fontSize:12,color:"var(--txt)",fontWeight:600}}>{m.init} <span style={{color:"var(--txt3)",fontWeight:400}}>{m.nom}</span></td>
                    <td style={{padding:"4px 6px",fontSize:11,textAlign:"center",color:{less:"#f59e0b",normal:"var(--txt2)",more:"#16a34a"}[m.gardeFactor||"normal"]}}>{{less:"Moins",normal:"Moyen",more:"Plus"}[m.gardeFactor||"normal"]}</td>
                    <td style={{padding:"4px 6px",textAlign:"center"}}>
                      <input type="number" min={0} placeholder="—" value={gMax[m.id]!==undefined?gMax[m.id]:""}
                        onChange={e=>setGMax(p=>({...p,[m.id]:e.target.value}))}
                        style={{width:52,padding:"3px 5px",borderRadius:6,border:"1px solid var(--border)",background:"var(--inp)",color:"var(--txt)",fontSize:12,textAlign:"center"}}/>
                    </td>
                  </tr>
                ))}
              </tbody>
            </table>
            <div style={{fontSize:10,color:"var(--txt3)",marginBottom:12}}>Le tableau "Répartition idéale" au-dessus de la liste des gardes reste votre référence : laissez Max vide pour une répartition purement pondérée.</div>
            <div style={{display:"flex",gap:8,justifyContent:"flex-end"}}>
              <button onClick={()=>setGardeModal(false)}
                style={{padding:"9px 16px",borderRadius:8,border:"1px solid var(--border)",background:"var(--bg2)",color:"var(--txt2)",fontWeight:700,fontSize:13,cursor:"pointer"}}>Annuler</button>
              <button onClick={runGardeAuto} style={{...S.btnP,background:"#f85149",padding:"9px 18px"}}>🌙 Lancer la répartition</button>
            </div>
          </div>
        </Ov>
      )}
      {lastGReport&&(
        <div style={{margin:"8px 12px",padding:"9px 12px",borderRadius:9,border:"1px solid "+(lastGReport.unfilled>0?"#f59e0b":"#16a34a"),background:lastGReport.unfilled>0?"rgba(245,158,11,.08)":"rgba(22,163,74,.08)",fontSize:11,color:"var(--txt)",display:"flex",gap:8,alignItems:"flex-start"}}>
          <span style={{fontSize:13}}>ℹ️</span>
          <div style={{flex:1,lineHeight:1.5}}>
            <b>Répartition effectuée : {lastGReport.nA}/{lastGReport.total} jours attribués.</b>
            {lastGReport.unfilled===0&&lastGReport.wishMiss===0&&" ✓ Toutes les contraintes et préférences ont été respectées."}
            {lastGReport.unfilled>0&&<span> ⚠ {lastGReport.unfilled} jour(s) sans candidat possible : {lastGReport.unfilledList.join(", ")}. Vérifiez absences, jours autorisés, semaines de tour et maximums.</span>}
            {lastGReport.wishMiss>0&&<span> ⚠ {lastGReport.wishMiss} vœu(x) ⭐ non satisfait(s) (contraintes incompatibles).</span>}
            <span style={{color:"var(--txt3)"}}> Totaux : {lastGReport.tots.map(t=>t.init+" "+t.n).join(" · ")}.</span>
          </div>
          <button onClick={()=>setLastGReport(null)} style={{...S.xBtn,fontSize:14}}>×</button>
        </div>
      )}
      {isEdit&&(()=>{
        // Répartition idéale: count days by type in the 4M period
        const gMeds=medecins.filter(m=>m.garde===true);
        const nMeds=gMeds.length||1;
        let nSem=0,nJeu=0,nVen=0,nSam=0,nDim=0;
        gvEffDays.forEach(({y:cy,m:cm,d:cd})=>{
          const c3=catOf(cy,cm,cd);
          if(c3==="jeu")nJeu++;
          else if(c3==="ven")nVen++;
          else if(c3==="sam")nSam++;
          else if(c3==="dim")nDim++;
          else nSem++;
        });
        const fmt2=(n)=>{const v=n/nMeds;return v%1===0?String(v):v.toFixed(1);};
        return(
          <div style={{marginTop:14,maxWidth:560,borderRadius:8,border:"1px solid var(--border)",padding:12,background:"var(--bg2)"}}>
            <div style={{fontSize:11,color:"var(--txt3)",fontWeight:700,textTransform:"uppercase",marginBottom:8}}>
              Répartition idéale — {gMeds.length} médecin{gMeds.length>1?"s":""} de garde
            </div>
            <table style={{borderCollapse:"collapse",width:"100%"}}>
              <thead>
                <tr style={{borderBottom:"2px solid var(--border)"}}>
                  <th style={{textAlign:"left",padding:"4px 8px",fontSize:10,color:"var(--txt3)",fontWeight:700}}>Type de jour</th>
                  <th style={{textAlign:"center",padding:"4px 8px",fontSize:10,color:"var(--txt3)",fontWeight:700}}>Total période</th>
                  <th style={{textAlign:"center",padding:"4px 8px",fontSize:10,color:"var(--txt3)",fontWeight:700}}>Par médecin</th>
                </tr>
              </thead>
              <tbody>
                <tr style={{borderBottom:"2px solid var(--border)",background:"var(--bg3)"}}>
                  <td style={{padding:"5px 8px",fontSize:12,fontWeight:800,color:"var(--txt)"}}>🌙 Toutes gardes</td>
                  <td style={{textAlign:"center",padding:"5px 8px",fontSize:13,fontWeight:800,color:"var(--txt)"}}>{nSem+nJeu+nVen+nSam+nDim}</td>
                  <td style={{textAlign:"center",padding:"5px 8px",fontSize:13,fontWeight:800,color:"#f85149"}}>{fmt2(nSem+nJeu+nVen+nSam+nDim)}</td>
                </tr>
                <tr style={{borderBottom:"1px solid var(--border2)"}}>
                  <td style={{padding:"5px 8px",fontSize:12,fontWeight:600,color:"var(--txt)"}}>Semaine (lun→mer)</td>
                  <td style={{textAlign:"center",padding:"5px 8px",fontSize:12,color:"var(--txt)"}}>{nSem}</td>
                  <td style={{textAlign:"center",padding:"5px 8px",fontSize:13,fontWeight:800,color:"var(--txt)"}}>{fmt2(nSem)}</td>
                </tr>
                <tr style={{borderBottom:"1px solid var(--border2)"}}>
                  <td style={{padding:"5px 8px",fontSize:12,fontWeight:600,color:"var(--txt)"}}>Jeudi <span style={{fontSize:9,color:"var(--txt3)"}}>(WE prolongé)</span></td>
                  <td style={{textAlign:"center",padding:"5px 8px",fontSize:12,color:"var(--txt)"}}>{nJeu}</td>
                  <td style={{textAlign:"center",padding:"5px 8px",fontSize:13,fontWeight:800,color:"var(--txt)"}}>{fmt2(nJeu)}</td>
                </tr>
                <tr style={{borderBottom:"1px solid var(--border2)"}}>
                  <td style={{padding:"5px 8px",fontSize:12,fontWeight:600,color:"var(--txt)"}}>Vendredi et veilles de fériés</td>
                  <td style={{textAlign:"center",padding:"5px 8px",fontSize:12,color:"var(--txt)"}}>{nVen}</td>
                  <td style={{textAlign:"center",padding:"5px 8px",fontSize:13,fontWeight:800,color:"var(--txt)"}}>{fmt2(nVen)}</td>
                </tr>
                <tr style={{borderBottom:"1px solid var(--border2)"}}>
                  <td style={{padding:"5px 8px",fontSize:12,fontWeight:600,color:"var(--txt)"}}>Samedi</td>
                  <td style={{textAlign:"center",padding:"5px 8px",fontSize:12,color:"var(--txt)"}}>{nSam}</td>
                  <td style={{textAlign:"center",padding:"5px 8px",fontSize:13,fontWeight:800,color:"var(--txt)"}}>{fmt2(nSam)}</td>
                </tr>
                <tr style={{borderBottom:"1px solid var(--border2)"}}>
                  <td style={{padding:"5px 8px",fontSize:12,fontWeight:600,color:"var(--txt)"}}>Dimanche et jours fériés</td>
                  <td style={{textAlign:"center",padding:"5px 8px",fontSize:12,color:"var(--txt)"}}>{nDim}</td>
                  <td style={{textAlign:"center",padding:"5px 8px",fontSize:13,fontWeight:800,color:"var(--txt)"}}>{fmt2(nDim)}</td>
                </tr>
                <tr style={{background:"var(--bg-we)"}}>
                  <td style={{padding:"5px 8px",fontSize:12,fontWeight:800,color:"#92400e"}}>Week-end (ven+sam+dim)</td>
                  <td style={{textAlign:"center",padding:"5px 8px",fontSize:12,fontWeight:700,color:"#92400e"}}>{nVen+nSam+nDim}</td>
                  <td style={{textAlign:"center",padding:"5px 8px",fontSize:13,fontWeight:800,color:"#92400e"}}>{fmt2(nVen+nSam+nDim)}</td>
                </tr>
              </tbody>
            </table>
            <table style={{borderCollapse:"collapse",width:"100%",marginTop:10}}>
              <thead><tr>
                <th style={{textAlign:"left",padding:"3px 8px",fontSize:10,color:"var(--txt3)"}}>Gardes posées</th>
                <th style={{padding:"3px 6px",fontSize:10,color:"var(--txt3)"}}>Total</th>
                <th style={{padding:"3px 6px",fontSize:10,color:"var(--txt3)"}}>Sem</th>
                <th style={{padding:"3px 6px",fontSize:10,color:"var(--txt3)"}}>Jeu</th>
                <th style={{padding:"3px 6px",fontSize:10,color:"var(--txt3)"}}>Ven*</th>
                <th style={{padding:"3px 6px",fontSize:10,color:"var(--txt3)"}}>Sam</th>
                <th style={{padding:"3px 6px",fontSize:10,color:"var(--txt3)"}}>Dim*</th>
              </tr></thead>
              <tbody>
                {medecins.filter(m2=>m2.garde).map(m2=>{
                  const cn={sem:0,jeu:0,ven:0,sam:0,dim:0};
                  gvEffDays.forEach(({y:ry,m:rm,d:rd})=>{
                    const dwR=dow(ry,rm,rd);
                    const slotR=(dwR===6||dwR===0)?"JOUR":"N";
                    const dmR=plan[sk(ry,rm,rd,slotR)]||{};
                    const eR=Array.isArray(dmR[m2.id])?dmR[m2.id][0]:dmR[m2.id];
                    if(eR&&eR.acteId==="GARDE")cn[catOf(ry,rm,rd)]++;
                  });
                  const totR=cn.sem+cn.jeu+cn.ven+cn.sam+cn.dim;
                  return(
                  <tr key={m2.id} style={{borderBottom:"1px solid var(--border2)"}}>
                    <td style={{padding:"3px 8px",fontSize:11,fontWeight:700,color:"var(--txt)"}}>
                      <span style={{display:"inline-flex",width:16,height:16,borderRadius:"50%",background:m2.color,color:"#fff",fontSize:7,fontWeight:800,alignItems:"center",justifyContent:"center",marginRight:5,verticalAlign:"middle"}}>{m2.init}</span>
                      {m2.nom}
                    </td>
                    <td style={{textAlign:"center",padding:"3px 6px",fontSize:12,fontWeight:800,color:"#f85149"}}>{totR}</td>
                    <td style={{textAlign:"center",padding:"3px 6px",fontSize:11,color:"var(--txt)"}}>{cn.sem}</td>
                    <td style={{textAlign:"center",padding:"3px 6px",fontSize:11,color:"var(--txt)"}}>{cn.jeu}</td>
                    <td style={{textAlign:"center",padding:"3px 6px",fontSize:11,color:"var(--txt)"}}>{cn.ven}</td>
                    <td style={{textAlign:"center",padding:"3px 6px",fontSize:11,color:"var(--txt)"}}>{cn.sam}</td>
                    <td style={{textAlign:"center",padding:"3px 6px",fontSize:11,color:"var(--txt)"}}>{cn.dim}</td>
                  </tr>);
                })}
              </tbody>
            </table>
            <div style={{fontSize:9,color:"var(--txt3)",marginTop:3}}>* Ven inclut les veilles de fériés · Dim inclut les jours fériés · période affichée</div>
          </div>
        );
      })()}

      {orient==="V"?viewV:viewH}

      {/* Picker modal */}
      {pickerDay!==null&&isEdit&&(()=>{
        const pd=pickerDay&&typeof pickerDay==="object"?pickerDay:{d:pickerDay,y:year,m:month};
        const dw2=dow(pd.y,pd.m,pd.d), gardeSlot=(dw2===6||dw2===0)?"JOUR":"N";
        const gMed=getGardeMed2(pd.y,pd.m,pd.d);
        return(
          <Ov onClose={()=>setPickerDay(null)}>
            <div style={S.mHd}>
              <div>
                <div style={S.mTit2}>🌙 Garde — {JOURSC[dw2]} {pd.d} {MOIS[pd.m]}</div>
                <div style={{color:"var(--txt2)",fontSize:12,marginTop:2}}>Le repos post-garde est posé automatiquement.</div>
              </div>
              <button onClick={()=>setPickerDay(null)} style={S.xBtn}>×</button>
            </div>
            {gMed&&(
              <div style={{marginBottom:12,padding:"8px 10px",background:"var(--bg-td)",borderRadius:7,border:"1px solid var(--today-c)44"}}>
                <div style={{fontSize:10,color:"var(--today-c)",fontWeight:700,marginBottom:5}}>✓ Garde assignée</div>
                <div style={{display:"flex",alignItems:"center",gap:7,marginBottom:8}}>
                  <div style={{width:24,height:24,borderRadius:"50%",background:gMed.color,display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:9,fontWeight:800}}>{gMed.init}</div>
                  <span style={{color:"var(--txt)",fontSize:13,fontWeight:700}}>{gMed.prenom} {gMed.nom}</span>
                </div>
                <button onClick={()=>setGvSwapOpen(v=>!v)} style={{width:"100%",padding:"6px",borderRadius:6,border:"1.5px solid #388bfd",background:"rgba(56,139,253,.10)",color:"#388bfd",fontWeight:800,fontSize:12,cursor:"pointer",marginBottom:6}}>⇄ Échanger cette garde…</button>
                {gvSwapOpen&&(()=>{
                  const A={y:pd.y,m:pd.m,d:pd.d,medId:gMed.id};
                  const others=gvEffDays.map(({y:gy,m:gm,d:gd})=>{
                    if(gy===pd.y&&gm===pd.m&&gd===pd.d)return null;
                    const mB=getGardeMed2(gy,gm,gd);
                    if(!mB||mB.id===gMed.id)return null;
                    const blockA=gvIsAbs(gMed.id,gy,gm,gd);
                    const blockB=gvIsAbs(mB.id,pd.y,pd.m,pd.d);
                    const reason=blockA?(gMed.init+" absent ce jour"):blockB?(mB.init+" absent le "+pd.d):null;
                    return {y:gy,m:gm,d:gd,mB,reason};
                  }).filter(Boolean);
                  return(
                  <div style={{marginBottom:8,padding:"7px 8px",borderRadius:7,border:"1px solid #388bfd55",background:"rgba(56,139,253,.05)"}}>
                    <div style={{fontSize:10,fontWeight:800,color:"#388bfd",marginBottom:5}}>Choisissez la garde à échanger (repos déplacés automatiquement) :</div>
                    <div style={{maxHeight:"32vh",overflowY:"auto"}}>
                      {others.map((o,i2)=>(
                        <div key={i2} onClick={()=>{
                            if(o.reason)return;
                            applyGarde(o.mB.id,pd.y,pd.m,pd.d);
                            setTimeout(()=>applyGarde(gMed.id,o.y,o.m,o.d),40);
                            toast(gMed.init+" ⇄ "+o.mB.init+" : gardes des "+pd.d+" "+MOIS[pd.m].slice(0,4)+" et "+o.d+" "+MOIS[o.m].slice(0,4)+" échangées","info");
                            setGvSwapOpen(false);setPickerDay(null);
                          }}
                          style={{display:"flex",alignItems:"center",gap:6,padding:"5px 8px",borderRadius:6,marginBottom:3,cursor:o.reason?"not-allowed":"pointer",opacity:o.reason?.45:1,border:"1px solid var(--border2)",background:"var(--bg2)"}}>
                          <span style={{fontSize:10,fontWeight:700,color:"var(--txt)",width:86}}>{JOURSC[dow(o.y,o.m,o.d)]} {o.d} {MOIS[o.m].slice(0,4)}</span>
                          <span style={{width:18,height:18,borderRadius:"50%",background:o.mB.color,color:"#fff",fontSize:7,fontWeight:800,display:"inline-flex",alignItems:"center",justifyContent:"center"}}>{o.mB.init}</span>
                          <span style={{fontSize:10,fontWeight:600,color:"var(--txt)",flex:1}}>{o.mB.nom}</span>
                          {o.reason?<span style={{fontSize:8,color:"#f85149",fontWeight:600}}>{o.reason}</span>:<span style={{fontSize:10,color:"#388bfd",fontWeight:800}}>⇄</span>}
                        </div>
                      ))}
                      {others.length===0&&<div style={{fontSize:10,color:"var(--txt3)"}}>Aucune autre garde attribuée sur la période affichée.</div>}
                    </div>
                  </div>);
                })()}
                <button style={{width:"100%",padding:"6px",borderRadius:6,border:"none",background:"#fef2f2",color:"#dc2626",cursor:"pointer",fontSize:11,fontWeight:700}}
                  onClick={()=>{ removeGarde(typeof pickerDay==="object"?pickerDay.d:pickerDay,pd&&pd.y,pd&&pd.m); setPickerDay(null); }}>
                  Retirer la garde + repos
                </button>
              </div>
            )}
            <div style={{fontSize:10,color:"var(--txt3)",fontWeight:700,textTransform:"uppercase",marginBottom:8}}>{gMed?"Changer :":"Assigner :"}</div>
            <div style={{display:"flex",flexDirection:"column",gap:4,maxHeight:360,overflowY:"auto"}}>
              {medecins.filter(m=>m.garde===true).map(m=>{
                const avail=isMedAvailable(m,pd.y,pd.m,pd.d,gardeSlot);
                const isG=gMed&&m.id===gMed.id;
                return(
                  <button key={m.id} disabled={avail==="blocked"}
                    style={{display:"flex",alignItems:"center",gap:8,padding:"7px 10px",borderRadius:7,
                      border:`1px solid ${isG?"var(--today-c)":"var(--border)"}`,
                      cursor:avail!=="blocked"?"pointer":"not-allowed",
                      background:isG?"var(--bg-td)":avail==="blocked"?"var(--bg)":"var(--bg2)",
                      opacity:avail==="blocked"?.3:1}}
                    onClick={()=>{ if(avail==="blocked")return; applyGarde(m.id,pd.y,pd.m,pd.d); setPickerDay(null); }}>
                    <div style={{width:24,height:24,borderRadius:"50%",background:m.color,display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:9,fontWeight:800}}>{m.init}</div>
                    <div style={{textAlign:"left",flex:1}}>
                      <div style={{fontSize:12,fontWeight:700,color:isG?"var(--today-c)":"var(--txt)"}}>{m.prenom} {m.nom}</div>
                      <div style={{fontSize:9,color:avail==="blocked"?"#ef4444":"var(--txt3)"}}>{avail==="blocked"?"Absent / repos":"Disponible"}</div>
                    </div>
                    {isG&&<span style={{fontSize:10,color:"var(--today-c)"}}>✓</span>}
                  </button>
                );
              })}
            </div>
          </Ov>
        );
      })()}
    </div>
  );
}


/* ════ BIP TAB ════ */
function BipTab({year,month,prevM,nextM,medecins,allDays,isEdit,actes,getEntries,salleOcc,addEntry,removeEntry,isMedAvailable,orient,setOrient,darkMode,setDarkMode,showFull,setShowFull}){
  const bipActe=actes.find(a=>a.id==="BIP");
  const bipSalles=(bipActe&&bipActe.salles)||["CHB-1","CHB-2","CHB-3"];
  const wdays=allDays.map(d=>({y:year,m:month,d}));
  // Filter medecins allowed for BIP
  const bipMeds=bipActe&&(bipActe.medecinsAutorise&&bipActe.medecinsAutorise.length)
    ? medecins.filter(m=>bipActe.medecinsAutorise.includes(m.init))
    : medecins;

  if(!bipActe)return <div style={{color:"var(--txt2)",padding:20}}>Activité BIP non configurée.</div>;

  const today=new Date();

  function getOccBip(d,sl){
    const occ=[];
    bipSalles.forEach(salle=>{
      const o=salleOcc("BIP",year,month,d,sl);
      (o[salle]||[]).forEach(med=>{
        if(!occ.find(x=>x.med.id===med.id)) occ.push({med,acte:bipActe,salle});
      });
    });
    return occ;
  }

  function renderBipCell(d,sl){
    if(isWE(year,month,d)) return <td key={"bip-"+d+sl} style={{...S.td,...S.tdWE,padding:2}}/>;
    const occ=getOccBip(d,sl);
    return(
      <td key={"bip-"+d+sl} style={{...S.td,padding:2,cursor:isEdit?"pointer":"default"}}
        onClick={isEdit?()=>openBipPicker({d,sl}):undefined}>
        {occ.map(({med,salle},i)=>(
          <div key={i} style={{display:"flex",alignItems:"center",gap:2,margin:"1px 0"}}>
            <div style={{width:22,height:22,borderRadius:"50%",background:med.color,display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:9,fontWeight:800,flexShrink:0}}>{med.init}</div>
            <span style={{fontSize:10,color:"#111",fontWeight:700}}>{salle}</span>
          </div>
        ))}
        {occ.length===0&&<div style={{color:"var(--border)",textAlign:"center",fontSize:13}}>·</div>}
      </td>
    );
  }

  const [pickerData,setPickerData]=useState(null);
  const [selMedId,setSelMedId]=useState(null);

  function openBipPicker(data){ setPickerData(data); setSelMedId(null); }

  const hdr=(
    <div style={S.bar}>
      <div style={{display:"flex",alignItems:"center",gap:8}}>
        <button onClick={prevM} style={S.arr}>‹</button>
        <h2 style={S.mTit}><span style={{color:"#fb923c"}}>🔔 BIP</span> — {MOIS[month]} {year}</h2>
        <button onClick={nextM} style={S.arr}>›</button>
      </div>
    </div>
  );

  return(
    <div>
      {hdr}
      <div style={{overflowX:"auto",overflowY:"auto",maxHeight:"calc(100vh - 110px)",borderRadius:8,border:"1px solid var(--border)"}}>
        <table style={{borderCollapse:"collapse"}}>
          <thead>
            <tr>
              <th style={{...S.thFix,position:"sticky",top:0,left:0,zIndex:40,minWidth:42}}>Jour</th>
              <th style={{...S.thFix,position:"sticky",top:0,left:42,zIndex:40,minWidth:24,borderRight:"2px solid var(--border)"}}>Sl</th>
              <th style={{...S.th,minWidth:120,position:"sticky",top:0,zIndex:20}}>
                <div style={{fontWeight:800,fontSize:10,color:"#111",fontFamily:"'JetBrains Mono',monospace"}}>BIP CHB</div>
                <div style={{fontSize:8,color:"var(--txt3)"}}>{bipSalles.join(", ")}</div>
              </th>
            </tr>
          </thead>
          <tbody>
            {wdays.map(({y:wY,m:wM,d})=>{
              const isT=d===today.getDate()&&wM===today.getMonth()&&wY===today.getFullYear();
              const dBip=dow(wY,wM,d), weBip=isWE(wY,wM,d), isMonBip=dBip===1&&!weBip;
              if(weBip) return(
                <tr key={wY+"-"+wM+"-"+d+"we"} style={{background:"var(--bg-we)",borderBottom:"1px solid var(--border)",height:28}}>
                  <td colSpan={2} style={{...S.tdFix,position:"sticky",left:0,zIndex:5,background:"var(--bg-we)"}}>
                    <div style={{fontWeight:800,color:"#92400e",fontSize:11,fontFamily:"'JetBrains Mono',monospace",textAlign:"center"}}>{d} {JOURSC[dBip]}</div>
                  </td>
                  <td style={{...S.td,...S.tdWE}}/>
                </tr>
              );
              return["M","AM"].map((sl,si)=>(
                <tr key={wY+"-"+wM+"-"+d+sl} style={{borderBottom:si===1?"1px solid var(--border)":"1px solid var(--border2)",
                  ...(isT?{background:"var(--bg-td)"}:{}),...(isMonBip&&si===0?{borderTop:"3px solid var(--border)"}:{})}}>
                  {si===0&&<td style={{...S.tdFix,position:"sticky",left:0,zIndex:5,verticalAlign:"middle",minWidth:42}} rowSpan={2}>
                    <div style={{fontWeight:800,color:isT?"var(--today-c)":"var(--txt)",fontSize:12,fontFamily:"'JetBrains Mono',monospace",textAlign:"center"}}>{d}{viewPeriod&&<div style={{fontSize:7,color:"var(--txt3)",fontWeight:600,lineHeight:1}}>{MOIS[wM]}</div>}</div>
                    <div style={{fontSize:8,color:"var(--txt3)",textTransform:"uppercase",textAlign:"center"}}>{JOURSC[dBip]}</div>
                  </td>}
                  <td style={{...S.tdFix,position:"sticky",left:42,zIndex:4,fontSize:9,color:"var(--txt3)",fontWeight:700,textAlign:"center",background:"var(--td-fix)",borderRight:"2px solid var(--border)",minWidth:24,padding:"2px"}}>{SLOTS[sl]}</td>
                  {renderBipCell(d,sl)}
                </tr>
              ));
            })}
          </tbody>
        </table>
      </div>

      {/* Picker modal */}
      {pickerData&&isEdit&&(()=>{
        const {d,sl}=pickerData;
        const selMed=bipMeds.find(m=>m.id===selMedId);
        const existing=getOccBip(d,sl);
        return(
          <Ov onClose={()=>setPickerData(null)}>
            <div style={S.mHd}>
              <div>
                <div style={S.mTit2}>BIP — {JOURSC[dow(year,month,d)]} {d} {MOIS[month]}</div>
                <div style={{color:"var(--txt2)",fontSize:12,marginTop:2}}>{SLOTL[sl]}</div>
              </div>
              <button onClick={()=>setPickerData(null)} style={S.xBtn}>×</button>
            </div>
            {existing.length>0&&(
              <div style={{marginBottom:12}}>
                <div style={{fontSize:10,color:"var(--txt3)",fontWeight:700,textTransform:"uppercase",marginBottom:6}}>Assignés</div>
                {existing.map(({med,salle})=>(
                  <div key={med.id} style={{display:"flex",alignItems:"center",gap:6,padding:"5px 8px",borderRadius:7,background:"#1a0800",border:"1px solid #fb923c44",marginBottom:4}}>
                    <div style={{width:28,height:28,borderRadius:"50%",background:med.color,display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:10,fontWeight:800}}>{med.init}</div>
                    <span style={{flex:1,color:"var(--txt)",fontSize:12,fontWeight:700}}>{med.prenom} {med.nom}</span>
                    <span style={{color:"#fb923c",fontSize:10,fontFamily:"'JetBrains Mono',monospace",fontWeight:800}}>{salle}</span>
                    <button onClick={()=>removeEntry(med.id,year,month,d,sl,"BIP")} style={{background:"none",border:"none",color:"#fb923c",cursor:"pointer",fontSize:13,lineHeight:1}}>×</button>
                  </div>
                ))}
              </div>
            )}
            {!selMedId&&(
              <>
                <div style={{fontSize:10,color:"var(--txt3)",fontWeight:700,textTransform:"uppercase",marginBottom:8}}>Choisir un médecin</div>
                <div style={{display:"flex",flexDirection:"column",gap:3,maxHeight:360,overflowY:"auto"}}>
                  {bipMeds.map(m=>{
                    const avail=isMedAvailable(m,year,month,d,sl);
                    const already=existing.find(e=>e.med.id===m.id);
                    return(
                      <button key={m.id} disabled={avail==="blocked"||!!already}
                        style={{display:"flex",alignItems:"center",gap:7,padding:"6px 9px",borderRadius:7,
                          border:"1px solid var(--border)",cursor:avail!=="blocked"&&!already?"pointer":"default",
                          background:avail==="warning"&&!already?"#1a1000":"var(--bg2)",opacity:avail==="blocked"||already?.35:1}}
                        onClick={()=>{ if(avail==="blocked"||already)return; setSelMedId(m.id); }}>
                        <div style={{width:22,height:22,borderRadius:"50%",background:m.color,display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:8,fontWeight:800}}>{m.init}</div>
                        <div style={{textAlign:"left",flex:1}}>
                          <div style={{fontSize:11,fontWeight:700,color:"var(--txt)"}}>{m.prenom} {m.nom}</div>
                          <div style={{fontSize:9,color:already?"#fb923c":avail==="blocked"?"#ef4444":avail==="warning"?"#f59e0b":"var(--txt3)"}}>
                            {already?"Déjà assigné":avail==="blocked"?"Absent/repos":avail==="warning"?"⚠ Déjà occupé":"Disponible"}
                          </div>
                        </div>
                      </button>
                    );
                  })}
                </div>
              </>
            )}
            {selMedId&&selMed&&(
              <>
                <div style={{display:"flex",alignItems:"center",gap:7,marginBottom:10,padding:"6px 9px",borderRadius:7,background:"var(--bg2)",border:"1px solid var(--border)"}}>
                  <div style={{width:20,height:20,borderRadius:"50%",background:selMed.color,display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:8,fontWeight:800}}>{selMed.init}</div>
                  <span style={{fontSize:12,fontWeight:700,color:"var(--txt)",flex:1}}>{selMed.prenom} {selMed.nom}</span>
                  <button onClick={()=>setSelMedId(null)} style={{background:"none",border:"none",color:"var(--txt3)",cursor:"pointer",fontSize:13}}>←</button>
                </div>
                <div style={{fontSize:10,color:"var(--txt3)",fontWeight:700,textTransform:"uppercase",marginBottom:8}}>Salle</div>
                {bipSalles.map(salle=>{
                  const o=salleOcc("BIP",year,month,d,sl);
                  const isFull=(o[salle]||[]).length>=1;
                  return(
                    <button key={salle} disabled={isFull}
                      style={{width:"100%",display:"flex",alignItems:"center",justifyContent:"space-between",
                        padding:"8px 11px",borderRadius:7,border:"1px solid var(--border)",marginBottom:5,
                        cursor:isFull?"not-allowed":"pointer",background:isFull?"var(--bg)":"var(--bg2)",opacity:isFull?.5:1}}
                      onClick={()=>{ if(isFull)return; addEntry(selMed.id,year,month,d,sl,{acteId:"BIP",salle}); setSelMedId(null); setPickerData(null); }}>
                      <span style={{fontWeight:800,color:"#fb923c",fontFamily:"'JetBrains Mono',monospace"}}>{salle}</span>
                      {isFull?<span style={{fontSize:10,color:"var(--txt3)"}}>Occupée</span>:<span style={{fontSize:10,color:"#fb923c"}}>Libre →</span>}
                    </button>
                  );
                })}
              </>
            )}
          </Ov>
        );
      })()}
    </div>
  );
}


function PlanTypeGrid({medecins,actes,planningType,setPlanningType,isEdit,orient,acteById,setMData,setModal}){
  const jours=["","Lun","Mar","Mer","Jeu","Ven"];

  if(orient==="H") return(
    <div style={{overflowX:"auto",borderRadius:8,border:"1px solid var(--border)"}}>
      <table style={{borderCollapse:"collapse",width:"100%"}}>
        <thead>
          <tr>
            <th style={{...S.thFix,position:"sticky",left:0,zIndex:20,minWidth:130}} rowSpan={2}>Médecin</th>
            {[1,2,3,4,5].map(d=><th key={d} colSpan={2} style={{...S.th,minWidth:100,fontWeight:700,fontSize:11}}>{jours[d]}</th>)}
          </tr>
          <tr>
            {[1,2,3,4,5].map(d=>["M","AM"].map(sl=><th key={d+sl} style={{...S.th,fontSize:9,padding:"2px 1px",color:"var(--txt3)"}}>{sl}</th>))}
          </tr>
        </thead>
        <tbody>
          {medecins.map(med=>{
            const pt=planningType[med.id]||{};
            return(
              <tr key={med.id} style={{borderBottom:"1px solid var(--border2)"}}>
                <td style={{...S.tdFix,position:"sticky",left:0,zIndex:5}}>
                  <div style={{display:"flex",alignItems:"center",gap:7}}>
                    <Av med={med}/>
                    <div>
                      <div style={{fontSize:11,fontWeight:700,color:"var(--txt)"}}>{med.prenom} {med.nom}</div>
                      {med.role==="attache"&&<span style={{fontSize:8,color:"#fb923c"}}>Attaché</span>}
                      {med.role==="ide"&&<span style={{fontSize:8,color:"#a5b4fc"}}>IDE</span>}
                    </div>
                  </div>
                </td>
                {[1,2,3,4,5].map(dw=>["M","AM"].map(sl=>{
                  const [acteId,salle]=(pt[dw]||{})[sl]||[null,null];
                  const acte=acteId?acteById(acteId):null;
                  return(
                    <td key={dw+sl} style={{...S.td,padding:2,cursor:isEdit?"pointer":"default"}}
                      onClick={()=>{ if(!isEdit)return; setMData({medId:med.id,dayOfWeek:dw,slot:sl}); setModal("editPT"); }}>
                      {acte&&<Badge a={acte} salle={salle}/>}
                    </td>
                  );
                }))}
              </tr>
            );
          })}
        </tbody>
      </table>
    </div>
  );

  return(
    <div style={{overflowX:"auto",overflowY:"auto",maxHeight:"calc(100vh - 150px)",borderRadius:8,border:"1px solid var(--border)"}}>
      <table style={{borderCollapse:"collapse"}}>
        <thead>
          <tr>
            <th style={{...S.thFix,position:"sticky",top:0,left:0,zIndex:40,minWidth:48}}>Jour</th>
            <th style={{...S.thFix,position:"sticky",top:0,left:48,zIndex:40,minWidth:26,borderRight:"2px solid var(--border)"}}>Sl</th>
            {medecins.map(med=><th key={med.id} style={{...S.th,minWidth:46,position:"sticky",top:0,zIndex:20}} title={`Dr. ${med.prenom} ${med.nom}`}>
              <div style={{...S.avT,background:med.color,margin:"0 auto"}}>{med.init}</div>
            </th>)}
          </tr>
        </thead>
        <tbody>
          {[1,2,3,4,5].map(dw=>["M","AM"].map((sl,si)=>(
            <tr key={dw+sl} style={{borderBottom:si===1?"1px solid var(--border)":"1px solid var(--border2)"}}>
              {si===0&&<td style={{...S.tdFix,position:"sticky",left:0,zIndex:10,verticalAlign:"middle",minWidth:48}} rowSpan={2}>
                <div style={{fontWeight:800,color:"var(--txt)",fontSize:13,textAlign:"center"}}>{jours[dw]}</div>
              </td>}
              <td style={{...S.tdFix,position:"sticky",left:48,zIndex:9,fontSize:9,color:"var(--txt3)",fontWeight:700,textAlign:"center",background:"var(--th)",borderRight:"2px solid var(--border)",minWidth:26,padding:"2px"}}>{sl}</td>
              {medecins.map(med=>{
                const pt=planningType[med.id]||{};
                const [acteId,salle]=(pt[dw]||{})[sl]||[null,null];
                const acte=acteId?acteById(acteId):null;
                return(
                  <td key={med.id} style={{...S.td,padding:2,cursor:isEdit?"pointer":"default"}}
                    onClick={()=>{ if(!isEdit)return; setMData({medId:med.id,dayOfWeek:dw,slot:sl}); setModal("editPT"); }}>
                    {acte&&<Badge a={acte} salle={salle}/>}
                  </td>
                );
              })}
            </tr>
          )))}
        </tbody>
      </table>
    </div>
  );
}

/* ════ PICK MED ACT MODAL (PT Cardio/Angio) ════ */
function PickMedActModal({mData,setMData,medecins,actes,getEntries,isMedAvailable,addEntry,removeEntry,onClose}){
  const {row,d,sl,y:y2,m:m2}=mData;
  const [selMedId,setSelMedId]=useState(null);
  const selMed=medecins.find(x=>x.id===selMedId);
  const rowActes=row.ids.map(id=>actes.find(a=>a.id===id)).filter(Boolean);
  const allAuth=new Set(rowActes.flatMap(a=>a.medecinsAutorise||[]));
  const eligMeds=medecins.filter(m=>allAuth.size===0||allAuth.has(m.init));
  const eligActesForMed=selMed?rowActes.filter(a=>!(a.medecinsAutorise&&a.medecinsAutorise.length)||a.medecinsAutorise.includes(selMed.init)):[];

  const curOcc=[];
  row.ids.forEach(aid=>{
    medecins.forEach(med=>{
      getEntries(med.id,y2,m2,d,sl).forEach(e=>{
        const match=row.salle?(e.acteId===aid&&e.salle===row.salle):e.acteId===aid;
        if(match&&!curOcc.find(x=>x.med.id===med.id&&x.acteId===aid)){
          const acte=actes.find(a=>a.id===aid);
          curOcc.push({med,acte,acteId:aid});
        }
      });
    });
  });

  return(
    <Ov onClose={onClose}>
      <div style={S.mHd}>
        <div>
          <div style={S.mTit2}>{row.label} — {JOURSL[dow(y2,m2,d)]} {d} {MOIS[m2]}</div>
          <div style={{color:"var(--txt2)",fontSize:12,marginTop:2}}>{SLOTL[sl]}</div>
        </div>
        <button onClick={onClose} style={S.xBtn}>×</button>
      </div>

      {curOcc.length>0&&(
        <div style={{marginBottom:12}}>
          <div style={{fontSize:10,color:"var(--txt3)",fontWeight:700,textTransform:"uppercase",marginBottom:6}}>Assignés</div>
          {curOcc.map(({med,acte,acteId},i)=>(
            <div key={i} style={{display:"flex",alignItems:"center",gap:6,padding:"5px 8px",borderRadius:7,background:"var(--bg2)",border:"1px solid var(--border)",marginBottom:4}}>
              <div style={{width:22,height:22,borderRadius:"50%",background:med.color,display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:8,fontWeight:800}}>{med.init}</div>
              <span style={{flex:1,color:"var(--txt)",fontSize:12,fontWeight:700}}>{med.prenom} {med.nom}</span>
              {acte&&<span style={{padding:"2px 6px",borderRadius:4,background:acte.bg,color:acte.color,fontSize:10,fontWeight:800,fontFamily:"'JetBrains Mono',monospace"}}>{acte.short}</span>}
              <button onClick={()=>removeEntry(med.id,y2,m2,d,sl,acteId)} style={{background:"none",border:"none",color:"var(--txt2)",cursor:"pointer",fontSize:15,lineHeight:1}}>×</button>
            </div>
          ))}
        </div>
      )}

      {!selMedId&&(
        <>
          <div style={{fontSize:10,color:"var(--txt3)",fontWeight:700,textTransform:"uppercase",marginBottom:8}}>Choisir un médecin</div>
          {/* Salle occupancy warning for fixed-salle rows (Stim/EEP) */}
          {row.salle&&curOcc.length>0&&(
            <div style={{display:"flex",alignItems:"center",gap:6,padding:"6px 10px",borderRadius:7,background:"#1a1000",border:"1px solid #f59e0b44",marginBottom:8}}>
              <span>⚠️</span>
              <span style={{fontSize:11,color:"#f59e0b"}}>
                {row.salle} déjà occupée par {curOcc.map(x=>x.med.init).join(", ")} — vous pouvez quand même ajouter un second médecin.
              </span>
            </div>
          )}
          <div style={{display:"flex",flexDirection:"column",gap:4,maxHeight:320,overflowY:"auto"}}>
            {eligMeds.map(med=>{
              const avail=isMedAvailable(med,y2,m2,d,sl);
              // Extra warning if this med would be in an already-occupied fixed salle
              const salleOccupied=row.salle&&curOcc.length>0&&!curOcc.find(x=>x.med.id===med.id);
              const borderCol=avail==="warning"||salleOccupied?"#f59e0b44":"var(--border)";
              const bgCol=avail==="warning"||salleOccupied?"#1a1000":"var(--bg2)";
              const statusTxt=avail==="blocked"?"Absent/repos":salleOccupied?`⚠ ${row.salle} déjà occupée`:avail==="warning"?"⚠ Déjà une activité":"Disponible";
              const statusCol=avail==="blocked"?"#ef4444":salleOccupied||avail==="warning"?"#f59e0b":"var(--txt3)";
              return(
                <button key={med.id} disabled={avail==="blocked"}
                  style={{display:"flex",alignItems:"center",gap:8,padding:"6px 9px",borderRadius:7,border:`1px solid ${borderCol}`,
                    cursor:avail!=="blocked"?"pointer":"default",background:bgCol,opacity:avail==="blocked"?.35:1}}
                  onClick={()=>{
                    if(avail==="blocked")return;
                    // If simple row (no multiActe, no salle choice) with single eligible acte → direct assign
                    const myActes=rowActes.filter(a=>!(a.medecinsAutorise&&a.medecinsAutorise.length)||a.medecinsAutorise.includes(med.init));
                    if(!row.multiActe&&!row.hasSalleChoice&&myActes.length===1){
                      const a=myActes[0];
                      const fs=a.fixedSalle||row.salle||null;
                      addEntry(med.id,y2,m2,d,sl,{acteId:a.id,salle:fs});
                      onClose();
                    } else {
                      setSelMedId(med.id);
                    }
                  }}>
                  <div style={{width:24,height:24,borderRadius:"50%",background:med.color,display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:9,fontWeight:800}}>{med.init}</div>
                  <div style={{textAlign:"left",flex:1}}>
                    <div style={{fontSize:12,fontWeight:700,color:"var(--txt)"}}>{med.prenom} {med.nom}</div>
                    <div style={{fontSize:9,color:statusCol}}>{statusTxt}</div>
                  </div>
                </button>
              );
            })}
          </div>
        </>
      )}

      {selMedId&&selMed&&(()=>{
        // Recompute eligible actes now that selMed is known
        const myEligActes=rowActes.filter(a=>!(a.medecinsAutorise&&a.medecinsAutorise.length)||a.medecinsAutorise.includes(selMed.init));
        const isSimple=!row.multiActe&&!row.hasSalleChoice;
        return(
          <>
            <div style={{display:"flex",alignItems:"center",gap:8,marginBottom:12}}>
              <button onClick={()=>setSelMedId(null)} style={{background:"var(--bg2)",border:"1px solid var(--border)",borderRadius:6,padding:"4px 9px",cursor:"pointer",color:"var(--txt2)",fontSize:12}}>← Retour</button>
              <div style={{display:"flex",alignItems:"center",gap:6}}>
                <div style={{width:22,height:22,borderRadius:"50%",background:selMed.color,display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:8,fontWeight:800}}>{selMed.init}</div>
                <span style={{color:"var(--txt)",fontSize:12,fontWeight:700}}>{selMed.prenom} {selMed.nom}</span>
              </div>
            </div>
            {isSimple&&(
              // Single acte, no salle choice: direct assign buttons
              <div style={S.actGrd}>
                {myEligActes.map(a=>(
                  <button key={a.id} style={{...S.actTog,background:a.color,color:"#111",outline:`1px solid ${a.color}55`}}
                    onClick={()=>{ const fs=a.fixedSalle||row.salle||null; addEntry(selMed.id,y2,m2,d,sl,{acteId:a.id,salle:fs}); onClose(); }}>
                    <span style={{fontWeight:800,fontSize:12,fontFamily:"'JetBrains Mono',monospace"}}>{a.short}</span>
                    <span style={{fontSize:10}}>{a.label}</span>
                  </button>
                ))}
                {myEligActes.length===0&&<div style={{color:"var(--txt3)",fontSize:12,gridColumn:"1/-1"}}>Aucune activité disponible.</div>}
              </div>
            )}
            {row.multiActe&&(
              <>
                <div style={{fontSize:10,color:"var(--txt3)",fontWeight:700,textTransform:"uppercase",marginBottom:8}}>Activité</div>
                <div style={S.actGrd}>
                  {myEligActes.map(a=>(
                    <button key={a.id} style={{...S.actTog,background:a.color,color:"#111",outline:`1px solid ${a.color}55`}}
                      onClick={()=>{ const fs=a.fixedSalle||row.salle||null; addEntry(selMed.id,y2,m2,d,sl,{acteId:a.id,salle:fs}); onClose(); }}>
                      <span style={{fontWeight:800,fontSize:12,fontFamily:"'JetBrains Mono',monospace"}}>{a.short}</span>
                      <span style={{fontSize:10}}>{a.label}</span>
                    </button>
                  ))}
                </div>
              </>
            )}
            {row.hasSalleChoice&&(()=>{
              const acteId=row.ids[0];
              const occ={}; // salle -> [medecins] across ALL actes
              medecins.forEach(m=>{
                getEntries(m.id,y2,m2,d,sl).forEach(e=>{
                  if(e.salle&&(row.sallesDisp||[]).includes(e.salle)){
                    if(!occ[e.salle])occ[e.salle]=[];
                    if(!occ[e.salle].find(x=>x.id===m.id))occ[e.salle].push(m);
                  }
                });
              });
              const libre=(row.sallesDisp||[]).filter(s=>!occ[s]||occ[s].length===0);
              const occupee=(row.sallesDisp||[]).filter(s=>occ[s]&&occ[s].length>0);
              return(
                <>
                  {libre.length>0&&(
                    <>
                      <div style={{fontSize:10,color:"var(--txt3)",fontWeight:700,textTransform:"uppercase",marginBottom:6}}>Salles libres</div>
                      <div style={{display:"flex",flexWrap:"wrap",gap:5,marginBottom:10}}>
                        {libre.map(s=>(
                          <button key={s} style={{padding:"5px 9px",borderRadius:5,border:"1px solid #3fb95088",cursor:"pointer",fontFamily:"'JetBrains Mono',monospace",fontSize:11,fontWeight:700,background:"#052e16",color:"#3fb950"}}
                            onClick={()=>{ addEntry(selMed.id,y2,m2,d,sl,{acteId,salle:s}); onClose(); }}>{s} ✓</button>
                        ))}
                      </div>
                    </>
                  )}
                  {occupee.length>0&&(
                    <>
                      <div style={{fontSize:10,color:"var(--txt3)",fontWeight:700,textTransform:"uppercase",marginBottom:6}}>Salles occupées</div>
                      <div style={{display:"flex",flexWrap:"wrap",gap:5}}>
                        {occupee.map(s=>(
                          <button key={s} style={{padding:"5px 9px",borderRadius:5,border:"1px solid #f59e0b44",cursor:"pointer",fontFamily:"'JetBrains Mono',monospace",fontSize:11,fontWeight:700,background:"#1a1000",color:"#f59e0b"}}
                            title={`Occupée par ${occ[s].map(m=>m.init).join(", ")} — clic pour ajouter quand même`}
                            onClick={()=>{ addEntry(selMed.id,y2,m2,d,sl,{acteId,salle:s}); onClose(); }}>{s} ⚠ {occ[s].map(m=>m.init).join(",")}</button>
                        ))}
                      </div>
                    </>
                  )}
                  {libre.length===0&&occupee.length===0&&<div style={{color:"var(--txt3)",fontSize:12}}>Aucune salle disponible.</div>}
                </>
              );
            })()}
          </>
        );
      })()}
    </Ov>
  );
}

/* ════ PICK MED SITE MODAL (CHL/CHB) ════ */
function PickMedSiteModal({mData,medecins,actes,getEntries,isMedAvailable,addEntry,removeEntry,onClose}){
  const {salle,siteActes,d,sl,y:y2,m:m2}=mData;
  const [step,setStep]=useState("med"); // med | acte | salle
  const [selMedId,setSelMedId]=useState(null);
  const selMed=medecins.find(x=>x.id===selMedId);

  const isBipCol=mData&&(mData.salle==="CHB-BIP"||String(mData.salle||"").indexOf("RECAP:")===0);
  const curOcc=[];
  siteActes.forEach(acte=>{
    medecins.forEach(med=>{
      getEntries(med.id,y2,m2,d,sl).forEach(e=>{
        // For BIP col: match any CHB salle; for regular cols: match exact salle
        const salleMatch=isBipCol?(["CHB-1","CHB-2","CHB-3"].includes(e.salle)):e.salle===salle;
        if(e.acteId===acte.id&&salleMatch&&!curOcc.find(x=>x.med.id===med.id)) curOcc.push({med,acte,rs:e.salle});
      });
    });
  });
  const [selBipSalle,setSelBipSalle]=useState(null);
  const bipActe=isBipCol?actes.find(a=>a.id==="BIP"):null;
  const eligActes=selMed?(isBipCol?[bipActe].filter(Boolean):siteActes.filter(a=>!(a.medecinsAutorise&&a.medecinsAutorise.length)||a.medecinsAutorise.includes(selMed.init))):[];

  return(
    <Ov onClose={onClose}>
      <div style={S.mHd}>
        <div>
          <div style={S.mTit2}>{salle} — {JOURSL[dow(y2,m2,d)]} {d} {MOIS[m2]}</div>
          <div style={{color:"var(--txt2)",fontSize:12,marginTop:2}}>{SLOTL[sl]}</div>
        </div>
        <button onClick={onClose} style={S.xBtn}>×</button>
      </div>
      {curOcc.length>0&&(
        <div style={{marginBottom:12}}>
          <div style={{fontSize:10,color:"var(--txt3)",fontWeight:700,textTransform:"uppercase",marginBottom:6}}>Occupants</div>
          {curOcc.map(({med,acte},i)=>(
            <div key={i} style={{display:"flex",alignItems:"center",gap:6,padding:"5px 8px",borderRadius:7,background:"var(--bg2)",border:"1px solid var(--border)",marginBottom:4}}>
              <div style={{width:22,height:22,borderRadius:"50%",background:med.color,display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:8,fontWeight:800}}>{med.init}</div>
              <span style={{flex:1,color:"var(--txt)",fontSize:12}}>{med.prenom} {med.nom}</span>
              <span style={{fontSize:10,color:acte.color,fontWeight:700,fontFamily:"'JetBrains Mono',monospace"}}>{acte.short}</span>
              <button onClick={()=>removeEntry(med.id,y2,m2,d,sl,acte.id)} style={{background:"none",border:"none",color:"var(--txt2)",cursor:"pointer",fontSize:15,lineHeight:1}}>×</button>
            </div>
          ))}
        </div>
      )}
      {step==="med"&&(
        <>
          <div style={{fontSize:10,color:"var(--txt3)",fontWeight:700,textTransform:"uppercase",marginBottom:8}}>Choisir un médecin</div>
          <div style={{display:"flex",flexDirection:"column",gap:4,maxHeight:320,overflowY:"auto"}}>
            {medecins.filter(med=>{
              // Only show medecins who have at least one eligible acte in this salle
              const elig=siteActes.filter(a=>!a.medecinsAutorise||!a.medecinsAutorise.length||a.medecinsAutorise.includes(med.init));
              return elig.length>0;
            }).map(med=>{
              const avail=isMedAvailable(med,y2,m2,d,sl);
              return(
                <button key={med.id} disabled={avail==="blocked"}
                  style={{display:"flex",alignItems:"center",gap:8,padding:"6px 9px",borderRadius:7,border:`1px solid ${avail==="warning"?"#f59e0b44":"var(--border)"}`,
                    cursor:avail!=="blocked"?"pointer":"default",background:avail==="warning"?"#1a1000":"var(--bg2)",opacity:avail==="blocked"?.35:1}}
                  onClick={()=>{ if(avail==="blocked")return; setSelMedId(med.id); setStep("acte"); }}>
                  <div style={{width:24,height:24,borderRadius:"50%",background:med.color,display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:9,fontWeight:800}}>{med.init}</div>
                  <div style={{textAlign:"left"}}>
                    <div style={{fontSize:12,fontWeight:700,color:"var(--txt)"}}>{med.prenom} {med.nom}</div>
                    <div style={{fontSize:9,color:avail==="blocked"?"#ef4444":avail==="warning"?"#f59e0b":"var(--txt3)"}}>{avail==="blocked"?"Absent/repos":avail==="warning"?"⚠ Déjà une activité":"Disponible"}</div>
                  </div>
                </button>
              );
            })}
          </div>
        </>
      )}
      {step==="acte"&&selMed&&(
        <>
          {eligActes.length===1&&eligActes[0].fixedSalle&&(()=>{ addEntry(selMed.id,y2,m2,d,sl,{acteId:eligActes[0].id,salle:eligActes[0].fixedSalle}); onClose(); return null; })()}
          <div style={{display:"flex",alignItems:"center",gap:8,marginBottom:12}}>
            <button onClick={()=>setStep("med")} style={{background:"var(--bg2)",border:"1px solid var(--border)",borderRadius:6,padding:"4px 9px",cursor:"pointer",color:"var(--txt2)",fontSize:12}}>← Retour</button>
            <div style={{display:"flex",alignItems:"center",gap:6}}>
              <div style={{width:22,height:22,borderRadius:"50%",background:selMed.color,display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:8,fontWeight:800}}>{selMed.init}</div>
              <span style={{color:"var(--txt)",fontSize:12,fontWeight:700}}>{selMed.prenom} {selMed.nom}</span>
            </div>
          </div>
          {curOcc.length>0&&<div style={{display:"flex",alignItems:"center",gap:6,padding:"6px 10px",borderRadius:7,background:"#1a1000",border:"1px solid #f59e0b44",marginBottom:10}}>
            <span>⚠️</span><span style={{fontSize:11,color:"#f59e0b"}}>Cette salle a déjà {curOcc.length} praticien(s) assigné(s). Confirmer quand même ?</span>
          </div>}
          <div style={{fontSize:10,color:"var(--txt3)",fontWeight:700,textTransform:"uppercase",marginBottom:8}}>Activité dans {salle}</div>
          <div style={S.actGrd}>
            {eligActes.map(a=>(
              <button key={a.id} style={{...S.actTog,background:a.color,color:"#111",outline:`1px solid ${a.color}55`}}
                onClick={()=>{
                  if(isBipCol){
                    // For BIP col: need to pick salle first
                    setStep("salle"); return;
                  }
                  const fs=a.fixedSalle||salle;
                  addEntry(selMed.id,y2,m2,d,sl,{acteId:a.id,salle:fs});
                  onClose();
                }}>
                <span style={{fontWeight:800,fontSize:12,fontFamily:"'JetBrains Mono',monospace"}}>{a.short}</span>
                <span style={{fontSize:10}}>{a.label}</span>
              </button>
            ))}
            {eligActes.length===0&&<div style={{color:"var(--txt3)",fontSize:12,gridColumn:"1/-1"}}>Aucune activité disponible pour ce médecin.</div>}
          </div>
        </>
      )}
      {step==="salle"&&selMed&&isBipCol&&(
        <>
          <div style={{display:"flex",alignItems:"center",gap:8,marginBottom:12}}>
            <button onClick={()=>setStep("acte")} style={{background:"var(--bg2)",border:"1px solid var(--border)",borderRadius:6,padding:"4px 9px",cursor:"pointer",color:"var(--txt2)",fontSize:12}}>← Retour</button>
            <div style={{display:"flex",alignItems:"center",gap:6}}>
              <div style={{width:22,height:22,borderRadius:"50%",background:selMed.color,display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:8,fontWeight:800}}>{selMed.init}</div>
              <span style={{color:"var(--txt)",fontSize:12,fontWeight:700}}>{selMed.prenom} {selMed.nom}</span>
            </div>
          </div>
          <div style={{fontSize:10,color:"var(--txt3)",fontWeight:700,textTransform:"uppercase",marginBottom:8}}>Choisir la salle BIP</div>
          <div style={{display:"flex",flexDirection:"column",gap:6}}>
            {["CHB-1","CHB-2","CHB-3"].map(s=>{
              // Check if salle is occupied by ANY activity
              const salleOccs=medecins.filter(m=>{
                const es=getEntries(m.id,y2,m2,d,sl);
                return es.some(e=>e.salle===s);
              });
              const occupied=salleOccs.length>0;
              return(
                <button key={s}
                  style={{...S.actTog,
                    background:occupied?"#fee2e2":"#46bdc6",
                    color:occupied?"#dc2626":"#111",
                    fontWeight:700,fontSize:13,
                    border:occupied?"1px solid #fca5a5":"1px solid #46bdc6"}}
                  onClick={()=>{ addEntry(selMed.id,y2,m2,d,sl,{acteId:"BIP",salle:s}); onClose(); }}>
                  <span>Salle {s.replace("CHB-","")}</span>
                  {occupied&&<span style={{fontSize:10,fontWeight:400,marginLeft:6}}>
                    — {salleOccs.map(m=>m.init).join(", ")} déjà assigné
                  </span>}
                </button>
              );
            })}
          </div>
        </>
      )}
    </Ov>
  );
}

/* ════ EDIT PT MODAL ════ */
function EditPTModal({mData,setMData,medecins,actes,planningType,setPlanningType,onClose}){
  const {medId,dayOfWeek,slot}=mData;
  const med=medecins.find(x=>x.id===medId);
  const pt=planningType[medId]||{};
  const [acteId,curSalle]=((pt[dayOfWeek]||{})[slot])||[null,null];
  const jours=["","Lundi","Mardi","Mercredi","Jeudi","Vendredi"];
  const setPT=(aId,salle)=>setPlanningType(p=>({...p,[medId]:{...p[medId],[dayOfWeek]:{...((p[medId]||{})[dayOfWeek]||{}),[slot]:[aId,salle]}}}));
  const eligActes=actes.filter(a=>!SYS.includes(a.id)&&(!(a.medecinsAutorise&&a.medecinsAutorise.length)||a.medecinsAutorise.includes((med&&med.init))));

  return(
    <Ov onClose={onClose}>
      <div style={S.mHd}>
        <div>
          <div style={S.mTit2}>Planning type — {(med&&med.init)} · {jours[dayOfWeek]} {slot}</div>
        </div>
        <button onClick={onClose} style={S.xBtn}>×</button>
      </div>
      {/* Current activity badge with X to remove */}
      {acteId&&(()=>{const cur=actes.find(x=>x.id===acteId);return cur?(
        <div style={{display:"flex",alignItems:"center",gap:6,marginBottom:10,padding:"6px 10px",background:"var(--bg)",borderRadius:8,border:"1px solid var(--border)"}}>
          <span style={{fontSize:11,color:"var(--txt3)",fontWeight:600}}>Activité actuelle :</span>
          <Badge a={cur}/>
          {curSalle&&<span style={{fontSize:10,color:"var(--txt3)"}}>{curSalle}</span>}
          <button onClick={()=>{setPT(null,null);onClose();}} style={{marginLeft:"auto",background:"#fee2e2",border:"1px solid #fca5a5",borderRadius:4,color:"#dc2626",cursor:"pointer",fontSize:12,fontWeight:900,padding:"1px 6px"}}>×</button>
        </div>
      ):null;})()}
      <div style={S.actGrd}>
{eligActes.map(a=>{
          const on=acteId===a.id;
          return(
            <button key={a.id} style={{...S.actTog,
              background:a.color,color:"#111",
              border:`2px solid ${on?"#1d4ed8":a.color}`,
              fontWeight:900,opacity:on?1:0.8}}
              onClick={()=>{ if(a.hasSalle) setMData(p=>({...p,_ptPickSalle:a.id})); else{ setPT(a.id,null); onClose(); } }}>
              <span style={{fontWeight:800,fontSize:12,fontFamily:"'JetBrains Mono',monospace"}}>{a.short}</span>
              <span style={{fontSize:10}}>{a.label}</span>
            </button>
          );
        })}
      </div>
      {mData&&mData._ptPickSalle&&(()=>{
        const a=actes.find(x=>x.id===mData._ptPickSalle);
        if(!a)return null;
        return(
          <div style={{marginTop:10,padding:10,background:"var(--bg)",borderRadius:8,border:`1px solid ${a.color}33`}}>
            <div style={{fontSize:10,color:a.color,fontWeight:700,marginBottom:7}}>{a.label} — Salle attitrée</div>
            <div style={{display:"flex",flexWrap:"wrap",gap:5}}>
              <button style={{padding:"5px 9px",borderRadius:5,border:"1px solid var(--border)",cursor:"pointer",background:"var(--bg2)",color:"var(--txt2)",fontSize:11,fontWeight:700}}
                onClick={()=>{ setPT(a.id,null); onClose(); }}>Sans salle</button>
              {(a.salles||[]).map(s=>{
                const usedBy=medecins.filter(o=>o.id!==medId).find(o=>{
                  const op=planningType[o.id]||{};
                  const oe=((op[dayOfWeek]||{})[slot])||[];
                  return oe[1]===s; // salle occupée quelle que soit l'activité
                });
                const usedActe=usedBy?(actes.find(x=>x.id===(((planningType[usedBy.id]||{})[dayOfWeek]||{})[slot]||[])[0])||{}).short:null;
                return(
                  <button key={s} title={usedBy?`⚠ Occupée par Dr. ${usedBy.nom}${usedActe?" ("+usedActe+")":""}`:""}
                    style={{padding:"5px 9px",borderRadius:5,border:`1px solid ${usedBy?"#f59e0b":"var(--border)"}`,cursor:"pointer",fontFamily:"'JetBrains Mono',monospace",fontSize:11,fontWeight:700,background:curSalle===s?a.color:usedBy?"#1a1000":"var(--bg2)",color:curSalle===s?"#fff":usedBy?"#f59e0b":"var(--txt2)"}}
                    onClick={()=>{ setPT(a.id,s); onClose(); }}>{s}{usedBy?" ⚠":""}</button>
                );
              })}
            </div>
          </div>
        );
      })()}
    </Ov>
  );
}

/* ════ ABS MODAL ════ */
function ClearPeriodModal({medecins,initMedId,initDate,onApply,onClose}){
  const [medId,setMedId]=useState(initMedId||null);
  const [keepAbs,setKeepAbs]=useState(true);
  const [dateFrom,setDateFrom]=useState(initDate||"");
  const [dateTo,setDateTo]=useState(initDate||"");
  const [slots,setSlots]=useState(["M","AM"]);
  const med=medecins.find(m=>m.id===medId);
  return(
    <div style={{minWidth:320}}>
      <div style={{display:"flex",justifyContent:"space-between",alignItems:"center",marginBottom:14}}>
        <div style={{fontWeight:800,fontSize:16,color:"var(--txt)"}}>🗑 Effacer des activités</div>
        <button onClick={onClose} style={S.xBtn}>×</button>
      </div>
      <div style={{marginBottom:10}}>
        <label style={S.fl}>Médecin</label>
        <select value={medId||""} onChange={e=>setMedId(parseInt(e.target.value))} style={{...S.fi,width:"100%"}}>
          <option value="">-- Choisir --</option>
          {medecins.filter(m=>m.role==="medecin"||m.role==="attache").map(m=>(
            <option key={m.id} value={m.id}>{m.prenom} {m.nom}</option>
          ))}
        </select>
      </div>
      <div style={{display:"grid",gridTemplateColumns:"1fr 1fr",gap:8,marginBottom:10}}>
        <div><label style={S.fl}>Du</label><input type="date" value={dateFrom} onChange={e=>setDateFrom(e.target.value)} style={{...S.fi,width:"100%"}}/></div>
        <div><label style={S.fl}>Au</label><input type="date" value={dateTo} onChange={e=>setDateTo(e.target.value)} style={{...S.fi,width:"100%"}}/></div>
      </div>
      <div style={{marginBottom:14}}>
        <label style={S.fl}>Demi-journées</label>
        <label style={{display:"flex",gap:6,alignItems:"center",fontSize:12,color:"var(--txt)",marginBottom:10,cursor:"pointer"}}>
        <input type="checkbox" checked={keepAbs} onChange={e=>setKeepAbs(e.target.checked)} style={{width:14,height:14}}/>
        Conserver les absences et formations (ne retirer que les activités)
      </label>
      <div style={{display:"flex",gap:6,marginTop:4}}>
          {[["M","Matin"],["AM","Après-midi"],["ALL","Journée"]].map(([v,l])=>{
            const on=v==="ALL"?(slots.includes("M")&&slots.includes("AM")):slots.length===1&&slots[0]===v;
            return <button key={v} onClick={()=>setSlots(v==="ALL"?["M","AM"]:[v])}
              style={{flex:1,padding:"8px 4px",borderRadius:7,border:"1px solid var(--border)",cursor:"pointer",fontWeight:700,fontSize:12,
                background:on?"#1d4ed8":"var(--bg2)",color:on?"#fff":"var(--txt2)"}}>{l}</button>;
          })}
        </div>
      </div>
      <div style={{padding:"8px 10px",background:"#1a0000",borderRadius:7,marginBottom:12,fontSize:11,color:"#ef4444"}}>
        ⚠ Toutes les activités (hors gardes et repos) seront supprimées pour ce médecin sur la période.
      </div>
      <button style={{...S.btnP,width:"100%",background:"#ef4444"}}
        onClick={()=>{ if(!medId||!dateFrom||!dateTo)return; onApply({keepAbs,medId,dateFrom,dateTo,slots}); }}>
        🗑 Effacer les activités
      </button>
    </div>
  );
}

function AbsModal({medecins,onApply,onRemove,onClose,initMedId=null,initDate=null}){
  const today=new Date();
  const fmt=d=>`${d.getFullYear()}-${String(d.getMonth()+1).padStart(2,"0")}-${String(d.getDate()).padStart(2,"0")}`;
  const defMed=initMedId||(medecins[0]&&medecins[0].id)||null;
  const defDate=initDate||fmt(today);
  const [mode,setMode]=useState("add"); // "add" | "remove"
  const [absType,setAbsType]=useState("ABSENCE"); // "ABSENCE" | "FORMATION"
  const [medId,setMedId]=useState(defMed);
  const [df,setDf]=useState(defDate);
  const [dt,setDt]=useState(defDate);
  const [slots,setSlots]=useState(["M","AM"]);
  const tog=sl=>setSlots(p=>p.includes(sl)?p.filter(x=>x!==sl):[...p,sl]);
  const canApply=medId&&df&&dt&&df<=dt;
  return(
    <>
      <div style={S.mHd}>
        <div style={S.mTit2}>{mode==="add"?(absType==="FORMATION"?"📚 Poser une formation":"🚫 Poser une absence"):"↩ Retirer une absence/formation"}</div>
        <button onClick={onClose} style={S.xBtn}>×</button>
      </div>
      {/* Toggle mode */}
      <div style={{display:"flex",gap:5,marginBottom:14,background:"var(--bg)",borderRadius:8,padding:4}}>
        <button onClick={()=>setMode("add")} style={{flex:1,padding:"7px",borderRadius:6,border:"none",cursor:"pointer",fontWeight:700,fontSize:12,background:mode==="add"?"#ef4444":"transparent",color:mode==="add"?"#fff":"var(--txt2)"}}>🚫 Poser</button>
        <button onClick={()=>setMode("remove")} style={{flex:1,padding:"7px",borderRadius:6,border:"none",cursor:"pointer",fontWeight:700,fontSize:12,background:mode==="remove"?"#3fb950":"transparent",color:mode==="remove"?"#fff":"var(--txt2)"}}>↩ Retirer</button>
      </div>
      {mode==="add"&&<div style={{marginBottom:10}}>
        <label style={S.fl}>Type</label>
        <div style={{display:"flex",gap:6,marginTop:4}}>
          {[["ABSENCE","🚫 Absence","#ef4444"],["FORMATION","📚 Formation","#a3e635"]].map(([v,l,c])=>(
            <button key={v} onClick={()=>setAbsType(v)}
              style={{flex:1,padding:"7px",borderRadius:7,border:"1px solid "+c,cursor:"pointer",fontWeight:700,fontSize:12,
                background:absType===v?c:"var(--bg2)",color:absType===v?"#111":"var(--txt2)"}}>
              {l}
            </button>
          ))}
        </div>
      </div>}
      <div style={S.fGrd}>
        <div style={{gridColumn:"1/-1"}}><label style={S.fl}>Médecin</label>
          <select value={medId||""} onChange={e=>setMedId(parseInt(e.target.value))} style={{...S.fi,width:"100%"}}>
            <option value="">— Choisir —</option>
            {medecins.map(m=><option key={m.id} value={m.id}>{m.prenom} {m.nom}</option>)}
          </select>
        </div>
        <div><label style={S.fl}>Du</label><input type="date" value={df} onChange={e=>setDf(e.target.value)} style={{...S.fi,width:"100%"}}/></div>
        <div><label style={S.fl}>Au</label><input type="date" value={dt} onChange={e=>setDt(e.target.value)} style={{...S.fi,width:"100%"}}/></div>
        {mode==="add"&&<div style={{gridColumn:"1/-1"}}>
          <label style={S.fl}>Demi-journées</label>
          <div style={{display:"flex",gap:7,marginTop:5}}>
            {[["M","Matin"],["AM","Après-midi"],["ALL","Journée"]].map(([v,l])=>{
              const on=v==="ALL"?(slots.includes("M")&&slots.includes("AM")):slots.length===1&&slots[0]===v;
              return <button key={v} onClick={()=>setSlots(v==="ALL"?["M","AM"]:[v])}
                style={{flex:1,padding:"9px",borderRadius:8,border:"1px solid var(--border)",cursor:"pointer",fontWeight:700,fontSize:13,
                  background:on?"#1d4ed8":"var(--bg2)",color:on?"#fff":"var(--txt2)"}}>{l}</button>;
            })}
          </div>
        </div>}
        {!canApply&&df&&dt&&df>dt&&<div style={{gridColumn:"1/-1",color:"#ef4444",fontSize:12}}>⚠ La date de fin doit être après la date de début.</div>}
      </div>
      {mode==="add"
        ?<button style={{...S.btnP,width:"100%",marginTop:13,opacity:canApply?1:.5,background:"#ef4444"}} onClick={()=>{ if(!canApply)return; onApply({medId,dateFrom:df,dateTo:dt,slots:slots.length?slots:["M","AM"],absType}); }}>🚫 Poser l'absence</button>
        :<button style={{...S.btnP,width:"100%",marginTop:13,opacity:canApply?1:.5,background:"#3fb950"}} onClick={()=>{ if(!canApply)return; onRemove({medId,dateFrom:df,dateTo:dt}); }}>↩ Retirer l'absence</button>
      }
    </>
  );
}

/* ════════════════════════════════════════════════════════════
   MAIN APP
════════════════════════════════════════════════════════════ */
function TourTab({tourMins,tourMinsHard,tourAvoid,tourWish,applyTPForWeek,cleanTPForWeek,clearWeekActivities,reapplyPTWeek,purgeTourExtras,plan,tourDerog,lastReport,setLastReport,tourCfg,setTourCfg,year:tourYear,month:tourMonth,setYear:setTourYear,setMonth:setTourMonth,tourMed,setTourMed,medecins,getEntries,isEdit,darkMode,setDarkMode,planningType,setPlan,allDays,toast}){
  const _psT=perStart(tourYear,tourMonth);
  const perT={pi:_psT.sm,startY:_psT.sy,startM:_psT.sm};
  const perKeyT=perT.startY+"_"+perT.startM;
  const savedCfg=(tourCfg||{})[perKeyT]||null;
  const perLabelT=MOIS[perT.startM]+" — "+MOIS[(perT.startM+PCFG.len-1)%12];
  const prevPeriodT=()=>{const p=perPrev(perT.startY,perT.startM);setTourMonth(p.sm);setTourYear(p.sy);};
  const nextPeriodT=()=>{const p=perNext(perT.startY,perT.startM);setTourMonth(p.sm);setTourYear(p.sy);};
  const weeksT=[];
  const startDateT=new Date(perT.startY,perT.startM,1);
  const fdT=new Date(startDateT);
  while(fdT.getDay()!==1)fdT.setDate(fdT.getDate()+1);
  const endDateT=new Date(perT.startY,perT.startM+PCFG.len,0);
  const curT=new Date(fdT);
  while(curT<=endDateT){
    weeksT.push({key:curT.getFullYear()+"-"+curT.getMonth()+"-"+curT.getDate(),label:curT.getDate()+" "+MOIS[curT.getMonth()].slice(0,4)});
    curT.setDate(curT.getDate()+7);
  }
  const tmCountPeriod=(medId)=>weeksT.reduce((n,w)=>{const wm2=tourMed[w.key]||{HC:[],USIC:[]};return((wm2.HC||[]).includes(medId)||(wm2.USIC||[]).includes(medId))?n+1:n;},0);
  const isBlockedInWeek=(medId,wk2)=>{
    const[wy2,wm2,wd2]=wk2.split("-").map(Number);
    for(let i=0;i<5;i++){
      const dt=new Date(wy2,wm2,wd2+i);
      const dy=dt.getFullYear(),dm=dt.getMonth(),dd=dt.getDate();
      const es1=getEntries(medId,dy,dm,dd,"M");
      const es2=getEntries(medId,dy,dm,dd,"AM");
      if([...es1,...es2].some(e=>["ABSENCE","FORM","FORMATION"].includes(e.acteId)))return true;
    }
    return false;
  };
  /* ═══ Échange de semaines de tour ═══ */
  const [swapOpen,setSwapOpen]=React.useState(false);
  const [swapSrcKey,setSwapSrcKey]=React.useState(null);
  const [swapSrcMed,setSwapSrcMed]=React.useState(null);
  const [swapDstKey,setSwapDstKey]=React.useState(null);
  const [swapDstMed,setSwapDstMed]=React.useState(null);
  const [swapUpdPlan,setSwapUpdPlan]=React.useState(true);
  const JOURS_SW=["Dim","Lun","Mar","Mer","Jeu","Ven","Sam"];
  const absDaysOf=(medId,wk2)=>{
    if(!medId||!wk2)return [];
    const[wy2,wm2,wd2]=wk2.split("-").map(Number);
    const days=[];
    for(let i=0;i<5;i++){
      const dt=new Date(wy2,wm2,wd2+i);
      const dy=dt.getFullYear(),dm=dt.getMonth(),dd=dt.getDate();
      const es=[...getEntries(medId,dy,dm,dd,"M"),...getEntries(medId,dy,dm,dd,"AM")];
      if(es.some(e=>["ABSENCE","FORM","FORMATION"].includes(e.acteId)))days.push(JOURS_SW[dt.getDay()]+" "+dd);
    }
    return days;
  };
  const unitOf=(medId,wk2)=>{
    const wm2=tourMed[wk2]||{HC:[],USIC:[]};
    if((wm2.HC||[]).includes(medId))return "HC";
    if((wm2.USIC||[]).includes(medId))return "USIC";
    return null;
  };
  const runSwap=()=>{
    const uSrc=unitOf(swapSrcMed,swapSrcKey),uDst=unitOf(swapDstMed,swapDstKey);
    if(!uSrc||!uDst)return;
    // 1. Échange dans tourMed
    setTourMed(p=>{
      const n={...p};
      const src={...(n[swapSrcKey]||{HC:[],USIC:[]})};
      src[uSrc]=(src[uSrc]||[]).filter(id=>id!==swapSrcMed);
      n[swapSrcKey]=src;
      const dst={...(n[swapDstKey]||{HC:[],USIC:[]})};
      dst[uDst]=(dst[uDst]||[]).filter(id=>id!==swapDstMed);
      n[swapDstKey]=dst;
      const src2={...n[swapSrcKey]};src2[uSrc]=[...(src2[uSrc]||[]),swapDstMed];n[swapSrcKey]=src2;
      const dst2={...n[swapDstKey]};dst2[uDst]=[...(dst2[uDst]||[]),swapSrcMed];n[swapDstKey]=dst2;
      return n;
    });
    // 2. Planning : uniquement les 2 personnes, uniquement si semaines différentes
    if(swapUpdPlan&&swapSrcKey!==swapDstKey){
      const weekDays=(wk2)=>{
        const[wy2,wm2,wd2]=wk2.split("-").map(Number);
        return [0,1,2,3,4].map(i=>{const dt=new Date(wy2,wm2,wd2+i);return[dt.getFullYear(),dt.getMonth(),dt.getDate()];});
      };
      const PROT=["ABSENCE","GARDE","REPOS_GARDE","FORM","FORMATION","TOUR_HC","TOUR_USIC"];
      setPlan(p=>{
        let next={...p};
        // Chaque personne : retirer ses activités sur sa semaine d'ARRIVÉE, ré-appliquer son PT sur sa semaine de DÉPART
        [[swapSrcMed,swapDstKey,swapSrcKey],[swapDstMed,swapSrcKey,swapDstKey]].forEach(([mid,arriveKey,leaveKey])=>{
          weekDays(arriveKey).forEach(([dy,dm,dd])=>{
            if(isWE(dy,dm,dd))return;
            ["M","AM"].forEach(sl=>{
              const k=sk(dy,dm,dd,sl);
              if(!next[k]||!next[k][mid])return;
              const e=next[k][mid];
              const a=Array.isArray(e)?(e[0]&&e[0].acteId):(e&&e.acteId);
              if(PROT.includes(a))return;
              const dm3={...next[k]};delete dm3[mid];next[k]=dm3;
            });
          });
          const pt=planningType[mid];
          if(pt)weekDays(leaveKey).forEach(([dy,dm,dd])=>{
            if(isWE(dy,dm,dd))return;
            const dw2=dow(dy,dm,dd);
            if(!pt[dw2])return;
            ["M","AM"].forEach(sl=>{
              const k=sk(dy,dm,dd,sl);
              const ex=(next[k]||{})[mid];
              const exA=Array.isArray(ex)?(ex[0]&&ex[0].acteId):(ex&&ex.acteId);
              if(PROT.includes(exA))return;
              const[acteId,salle]=(pt[dw2][sl])||[null,null];
              if(!acteId)return;
              if(!next[k])next[k]={};
              next[k]={...next[k],[mid]:{acteId,salle:salle||null}};
            });
          });
        });
        return next;
      });
    }
    // Temps partiels : nettoyer les semaines quittées, appliquer sur les semaines d'arrivée (si USIC)
    const mS2=medecins.find(m=>m.id===swapSrcMed),mD2=medecins.find(m=>m.id===swapDstMed);
    if(mS2&&mS2.partTime){
      if(uSrc==="USIC")cleanTPForWeek(swapSrcMed,swapSrcKey);
      if(uDst==="USIC")setTimeout(()=>applyTPForWeek(swapSrcMed,swapDstKey),100);
    }
    if(mD2&&mD2.partTime){
      if(uDst==="USIC")cleanTPForWeek(swapDstMed,swapDstKey);
      if(uSrc==="USIC")setTimeout(()=>applyTPForWeek(swapDstMed,swapSrcKey),100);
    }
    const iS=(medecins.find(m=>m.id===swapSrcMed)||{}).init,iD=(medecins.find(m=>m.id===swapDstMed)||{}).init;
    toast("Échange effectué : "+iS+" ⇄ "+iD,"info");
    setSwapOpen(false);
  };

  // Remplacements TP de la semaine, calculés depuis le plan : ["M8 remplace M1 (Mer 22)"]
  const JOURS_TP=["Dim","Lun","Mar","Mer","Jeu","Ven","Sam"];
  const weekTPInfo=(wk2)=>{
    const[wy2,wm2,wd2]=wk2.split("-").map(Number);
    const infos=[];
    for(let i=0;i<5;i++){
      const dt=new Date(wy2,wm2,wd2+i);
      const dy=dt.getFullYear(),dm3=dt.getMonth(),dd=dt.getDate();
      const dk2=dKey(dy,dm3,dd);
      const dm2=(plan||{})[sk(dy,dm3,dd,"M")]||{};
      const derogMeds=Object.keys((tourDerog||{})[dk2]||{});
      Object.keys(dm2).forEach(mid=>{
        const e=Array.isArray(dm2[mid])?dm2[mid][0]:dm2[mid];
        if(e&&e.acteId==="TOUR_USIC"){
          const jr=medecins.find(m2=>String(m2.id)===String(mid));
          const tp=derogMeds.length>0?medecins.find(m2=>String(m2.id)===String(derogMeds[0])):null;
          infos.push((jr?jr.init:"?")+" remplace "+(tp?tp.init:"?")+" ("+JOURS_TP[dt.getDay()]+" "+dd+" "+MOIS[dm3].slice(0,4)+(MOIS[dm3].length>4?".":"")+")");
        }
      });
    }
    return infos;
  };
  const tourMeds=medecins.filter(m=>m.tourMed);
  const horsTourSpecMeds=medecins.filter(m=>m.role==="medecin"&&!m.tourMed&&m.surSpec);
  const SPEC_COLORS={coro:"#76a5af",pace:"#e3b341",eep:"#f97316",ett:"#ea9999"};
  // ─── Auto-répartition ───
  const [autoModal,setAutoModal]=React.useState(false);
  const [cfgMinEEP,setCfgMinEEP]=React.useState(1);
  const [cfgMinPace,setCfgMinPace]=React.useState(1);
  const [cfgMinETT,setCfgMinETT]=React.useState(1);
  const [cfgMinCoro,setCfgMinCoro]=React.useState(3);
  const [cfgExcl,setCfgExcl]=React.useState({}); // {medId: true = ne participe pas}
  const [cfgWeeks,setCfgWeeks]=React.useState({}); // {medId: nWeeks}
  const [cfgPref2HC,setCfgPref2HC]=React.useState({}); // {medId: bool}
  const [cfgPref2USIC,setCfgPref2USIC]=React.useState({}); // {medId: bool}
  const totalSlots=weeksT.length*4; // 2 HC + 2 USIC per week
  const activeMeds=tourMeds.filter(m=>!cfgExcl[m.id]);
  const nominalW=activeMeds.length>0?Math.ceil(totalSlots/activeMeds.length):0;
  const recalcWeeks=(excl)=>{
    const act=tourMeds.filter(m=>!excl[m.id]);
    const nom=act.length>0?Math.ceil(totalSlots/act.length):0;
    const w={};
    tourMeds.forEach(m=>{w[m.id]=excl[m.id]?0:nom;});
    return w;
  };
  const openAutoModal=()=>{
    if(savedCfg){
      // Restaurer la config précédente de cette période
      setCfgWeeks(savedCfg.weeks||{});
      setCfgExcl(savedCfg.excl||{});
      setCfgPref2HC(savedCfg.p2hc||{});
      setCfgPref2USIC(savedCfg.p2usic||{});
    }else{
      const ph={},pu={};
      tourMeds.forEach(m=>{ph[m.id]=!!m.pref2HC;pu[m.id]=!!m.pref2USIC;});
      const excl={};
      setCfgExcl(excl);
      setCfgWeeks(recalcWeeks(excl));
      setCfgPref2HC(ph);setCfgPref2USIC(pu);
    }
    // Minimums : TOUJOURS repris des réglages (modifiables ponctuellement ensuite)
    if(tourMins){
      setCfgMinCoro(tourMins.coro!==undefined?tourMins.coro:3);
      setCfgMinPace(tourMins.pace!==undefined?tourMins.pace:1);
      setCfgMinEEP(tourMins.eep!==undefined?tourMins.eep:1);
      setCfgMinETT(tourMins.ett!==undefined?tourMins.ett:0);
    }
    setAutoModal(true);
  };
  const persistCfg=(weeks,excl,p2h,p2u)=>{
    setTourCfg(p=>({...(p||{}),[perKeyT]:{
      weeks:weeks!==undefined?weeks:cfgWeeks,
      excl:excl!==undefined?excl:cfgExcl,
      p2hc:p2h!==undefined?p2h:cfgPref2HC,
      p2usic:p2u!==undefined?p2u:cfgPref2USIC
    }}));
  };
  const closeAutoModal=()=>{persistCfg();setAutoModal(false);};
  const toggleExcl=(id)=>{
    const n={...cfgExcl,[id]:!cfgExcl[id]};
    setCfgExcl(n);
    setCfgWeeks(recalcWeeks(n));
  };
  const runAutoRepartition=()=>{
    // ═══ Pré-vérification de faisabilité des contraintes ═══
    const seniors=medecins.filter(m=>m.role==="medecin"&&(m.statut||"senior")!=="junior");
    const totCoro=seniors.filter(m=>m.surSpec==="coro").length;
    const totPace=seniors.filter(m=>m.surSpec==="pace").length;
    const totEEP=seniors.filter(m=>m.surSpec==="eep").length;
    const totETT=seniors.filter(m=>m.surSpec==="ett").length;
    const issues=[];
    const hb=tourMinsHard||{};
    const fl={coro:Math.min(cfgMinCoro,hb.coro!==undefined?hb.coro:2),pace:Math.min(cfgMinPace,hb.pace!==undefined?hb.pace:1),eep:Math.min(cfgMinEEP,hb.eep!==undefined?hb.eep:1),ett:Math.min(cfgMinETT,hb.ett!==undefined?hb.ett:0)};
    if(totCoro<fl.coro)issues.push("Coro: "+totCoro+" sénior(s) pour un minimum (même relâché) de "+fl.coro);
    if(totPace<fl.pace)issues.push("Pace: "+totPace+" pour min "+fl.pace);
    if(totEEP<fl.eep)issues.push("EEP: "+totEEP+" pour min "+fl.eep);
    if(totETT<fl.ett)issues.push("ETT: "+totETT+" pour min "+fl.ett);
    if(issues.length>0){
      toast("Contraintes impossibles — "+issues.join(" · ")+". Ajustez les minimums ou les surspécialités dans l'Équipe.","info");
      return;
    }
    // ═══ Multi-essais : on lance N tentatives et on garde la meilleure ═══
    const N_TRIES=60;
    // Disponibilité statique par semaine (médecins participants non absents)
    const availCount={};
    weeksT.forEach(w=>{
      availCount[w.key]=tourMeds.filter(m=>!cfgExcl[m.id]&&(cfgWeeks[m.id]||0)>0&&!isBlockedInWeek(m.id,w.key)).length;
    });
    // Semaines triées : les plus contraintes d'abord (moins de disponibles)
    const weeksByConstraint=[...weeksT].sort((a,b)=>availCount[a.key]-availCount[b.key]);

    const isAvoid=(medId,wk4)=>!!((tourAvoid||{})[wk4]||{})[medId];
    const attempt=(opts)=>{
      const useBlocks=opts.useBlocks;
      const relaxedWeeks=[];
      const avoidViol=[];
      const quota={};tourMeds.forEach(m=>{quota[m.id]=cfgExcl[m.id]?0:(cfgWeeks[m.id]||0);});
      const hcCount={},usicCount={};tourMeds.forEach(m=>{hcCount[m.id]=0;usicCount[m.id]=0;});
      const assign={};weeksT.forEach(w=>{assign[w.key]={HC:[],USIC:[]};});
      const assignedThisWeek={};weeksT.forEach(w=>{assignedThisWeek[w.key]=[];});
      const specOK=(wKey,extraAssigned,mns)=>{
        const busy=[...assignedThisWeek[wKey],...extraAssigned];
        // Séniors présents (hors absents), indépendamment du tour
        const present=medecins.filter(m=>m.role==="medecin"&&(m.statut||"senior")!=="junior"&&!isBlockedInWeek(m.id,wKey));
        // Séniors restant disponibles une fois le tour assigné
        const avail=present.filter(m=>!busy.includes(m.id));
        const cnt=(list,pred)=>list.filter(pred).length;
        const check=(spec,minV)=>{
          const nAvail=cnt(avail,m=>m.surSpec===spec);
          if(nAvail>=minV)return true;
          // Déficit : acceptable seulement si le tour n'y est pour rien
          // (autant de spécialistes dispo qu'il y en a de présents = aucun pris par le tour)
          return nAvail===cnt(present,m=>m.surSpec===spec);
        };
        return check("eep",mns.eep)&&check("pace",mns.pace)&&check("ett",mns.ett)&&check("coro",mns.coro);
      };
      // Phase 1 : blocs de 2 semaines consécutives (préférences)
      const placeBlock=(m,unit)=>{
        for(let i2=0;i2<weeksT.length-1;i2++){
          const w1=weeksT[i2],w2=weeksT[i2+1];
          if(assignedThisWeek[w1.key].includes(m.id)||assignedThisWeek[w2.key].includes(m.id))continue;
          if(isBlockedInWeek(m.id,w1.key)||isBlockedInWeek(m.id,w2.key))continue;
          if(isAvoid(m.id,w1.key)||isAvoid(m.id,w2.key))continue;
          if(assign[w1.key][unit].length>=2||assign[w2.key][unit].length>=2)continue;
          if(!specOK(w1.key,[m.id],idealMins)||!specOK(w2.key,[m.id],idealMins))continue;
          assign[w1.key][unit].push(m.id);assignedThisWeek[w1.key].push(m.id);
          assign[w2.key][unit].push(m.id);assignedThisWeek[w2.key].push(m.id);
          if(unit==="HC")hcCount[m.id]+=2;else usicCount[m.id]+=2;
          quota[m.id]-=2;
          return true;
        }
        return false;
      };
      if(useBlocks){
        const shuffled=[...tourMeds].sort(()=>Math.random()-0.5);
        shuffled.forEach(m=>{
          if(cfgPref2HC[m.id]&&quota[m.id]>=2)placeBlock(m,"HC");
          if(cfgPref2USIC[m.id]&&quota[m.id]>=2)placeBlock(m,"USIC");
        });
      }
      // Phase 2 : remplissage en commençant par les semaines les plus contraintes
      weeksByConstraint.forEach(w=>{
        const units=Math.random()<0.5?["HC","USIC"]:["USIC","HC"];
        units.forEach(unit=>{
          while(assign[w.key][unit].length<2){
            const baseC=tourMeds.filter(m=>quota[m.id]>0
              &&!assignedThisWeek[w.key].includes(m.id)
              &&!isBlockedInWeek(m.id,w.key));
            const noAv=baseC.filter(m=>!isAvoid(m.id,w.key));
            let usedAvoid=false;
            let cands=noAv.filter(m=>specOK(w.key,[m.id],idealMins));
            if(cands.length===0){
              cands=baseC.filter(m=>specOK(w.key,[m.id],idealMins));
              if(cands.length>0)usedAvoid=true;
            }
            if(cands.length===0){
              cands=noAv.filter(m=>specOK(w.key,[m.id],hardMins));
              if(cands.length>0&&!relaxedWeeks.includes(w.label))relaxedWeeks.push(w.label);
            }
            if(cands.length===0){
              cands=baseC.filter(m=>specOK(w.key,[m.id],hardMins));
              if(cands.length>0){usedAvoid=true;if(!relaxedWeeks.includes(w.label))relaxedWeeks.push(w.label);}
            }
            if(cands.length===0)break;
            cands.sort((a,b)=>{
              const wA=((tourWish||{})[w.key]||{})[a.id]?0:1,wB=((tourWish||{})[w.key]||{})[b.id]?0:1;
              if(wA!==wB)return wA-wB;
              if(quota[b.id]!==quota[a.id])return quota[b.id]-quota[a.id];
              // Surspécialistes d'abord : consommer leur quota tant que la semaine a de la marge
              const spA=a.surSpec&&(idealMins[a.surSpec]||0)>0?0:1;
              const spB=b.surSpec&&(idealMins[b.surSpec]||0)>0?0:1;
              if(spA!==spB)return spA-spB;
              const balA=unit==="HC"?hcCount[a.id]-usicCount[a.id]:usicCount[a.id]-hcCount[a.id];
              const balB=unit==="HC"?hcCount[b.id]-usicCount[b.id]:usicCount[b.id]-hcCount[b.id];
              if(balA!==balB)return balA-balB;
              return Math.random()-0.5;
            });
            const m=cands[0];
            if(usedAvoid&&isAvoid(m.id,w.key))avoidViol.push(m.init+" ("+w.label+")");
            assign[w.key][unit].push(m.id);assignedThisWeek[w.key].push(m.id);
            if(unit==="HC")hcCount[m.id]++;else usicCount[m.id]++;
            quota[m.id]--;
          }
        });
      });
      // Score : semaines incomplètes (poids fort), quota restant, déséquilibre HC/USIC
      const unfilled=weeksT.filter(w=>assign[w.key].HC.length<2||assign[w.key].USIC.length<2).length;
      const leftoverTotal=tourMeds.reduce((s,m)=>s+(quota[m.id]||0),0);
      const imbalance=tourMeds.reduce((s,m)=>s+Math.abs(hcCount[m.id]-usicCount[m.id]),0);
      const score=unfilled*1000+relaxedWeeks.length*100+avoidViol.length*40+leftoverTotal*10+imbalance;
      return{assign,quota,unfilled,score,hcCount,usicCount,assignedThisWeek,specOK,relaxedWeeks,avoidViol};
    };

    // ═══ Paliers de relaxation progressive ═══
    const idealMins={coro:cfgMinCoro,pace:cfgMinPace,eep:cfgMinEEP,ett:cfgMinETT};
    const hardBase=tourMinsHard||{coro:2,pace:1,eep:1,ett:0};
    const hardMins={
      coro:Math.min(idealMins.coro,hardBase.coro!==undefined?hardBase.coro:2),
      pace:Math.min(idealMins.pace,hardBase.pace!==undefined?hardBase.pace:1),
      eep:Math.min(idealMins.eep,hardBase.eep!==undefined?hardBase.eep:1),
      ett:Math.min(idealMins.ett,hardBase.ett!==undefined?hardBase.ett:0)
    };
    const minsLabel=(mn)=>"Coro "+mn.coro+" · Pace "+mn.pace+" · EEP "+mn.eep+" · ETT "+mn.ett;
    const hardDiff=hardMins.coro<idealMins.coro||hardMins.pace<idealMins.pace||hardMins.eep<idealMins.eep||hardMins.ett<idealMins.ett;
    const stages=[
      {useBlocks:true, label:"standard"},
      {useBlocks:false,label:"préférences 2 sem. ignorées"},
    ];

    // Réparation par échanges, appliquée au meilleur essai du palier
    const repairResult=(r)=>{
      const{assign,quota,hcCount,usicCount,assignedThisWeek,specOK,relaxedWeeks}=r;
      for(let pass=0;pass<2;pass++){
        weeksT.forEach(w=>{
          ["HC","USIC"].forEach(unit=>{
            while(assign[w.key][unit].length<2){
              const stuck=tourMeds.filter(c=>quota[c.id]>0
                &&!assignedThisWeek[w.key].includes(c.id)
                &&!isBlockedInWeek(c.id,w.key));
              let repaired=false;
              for(const c of stuck){
                if(repaired)break;
                for(const w2 of weeksT){
                  if(repaired)break;
                  if(w2.key===w.key)continue;
                  for(const unit2 of ["HC","USIC"]){
                    if(repaired)break;
                    for(const m2id of [...assign[w2.key][unit2]]){
                      if(assignedThisWeek[w.key].includes(m2id))continue;
                      if(isBlockedInWeek(m2id,w.key))continue;
                      if(assignedThisWeek[w2.key].includes(c.id))continue;
                      if(isBlockedInWeek(c.id,w2.key))continue;
                      assign[w2.key][unit2]=assign[w2.key][unit2].filter(x=>x!==m2id);
                      assignedThisWeek[w2.key]=assignedThisWeek[w2.key].filter(x=>x!==m2id);
                      assign[w2.key][unit2].push(c.id);assignedThisWeek[w2.key].push(c.id);
                      assign[w.key][unit].push(m2id);assignedThisWeek[w.key].push(m2id);
                      const okIdeal=specOK(w.key,[],idealMins)&&specOK(w2.key,[],idealMins);
                      const okHard=okIdeal||(specOK(w.key,[],hardMins)&&specOK(w2.key,[],hardMins));
                      if(okHard){
                        if(!okIdeal){
                          if(!relaxedWeeks.includes(w.label))relaxedWeeks.push(w.label);
                          if(!relaxedWeeks.includes(w2.label))relaxedWeeks.push(w2.label);
                        }
                        quota[c.id]--;
                        if(unit2==="HC"){hcCount[c.id]++;hcCount[m2id]--;}else{usicCount[c.id]++;usicCount[m2id]--;}
                        if(unit==="HC")hcCount[m2id]++;else usicCount[m2id]++;
                        repaired=true;
                      }else{
                        assign[w.key][unit]=assign[w.key][unit].filter(x=>x!==m2id);
                        assignedThisWeek[w.key]=assignedThisWeek[w.key].filter(x=>x!==m2id);
                        assign[w2.key][unit2]=assign[w2.key][unit2].filter(x=>x!==c.id);
                        assignedThisWeek[w2.key]=assignedThisWeek[w2.key].filter(x=>x!==c.id);
                        assign[w2.key][unit2].push(m2id);assignedThisWeek[w2.key].push(m2id);
                      }
                      if(repaired)break;
                    }
                  }
                }
              }
              if(!repaired)break;
            }
          });
        });
      }
      r.unfilled=weeksT.filter(w=>assign[w.key].HC.length<2||assign[w.key].USIC.length<2).length;
      const leftoverTotal=tourMeds.reduce((s,m)=>s+(quota[m.id]||0),0);
      const imbalance=tourMeds.reduce((s,m)=>s+Math.abs(hcCount[m.id]-usicCount[m.id]),0);
      r.score=r.unfilled*1000+relaxedWeeks.length*100+leftoverTotal*10+imbalance;
      return r;
    };
    let best=null,bestStage=stages[0];
    for(let s=0;s<stages.length;s++){
      const st=stages[s];
      let stageBest=null;
      for(let t=0;t<N_TRIES;t++){
        const r=attempt(st);
        if(!stageBest||r.score<stageBest.score)stageBest=r;
        if(stageBest.unfilled===0&&stageBest.score===0)break;
      }
      if(stageBest.unfilled>0)repairResult(stageBest);
      if(!best||stageBest.score<best.score){best=stageBest;bestStage=st;}
      if(best.unfilled===0)break; // palier suffisant : toutes les semaines pleines
    }

    persistCfg();
    setTourMed(p=>{const n={...p};weeksT.forEach(w=>{n[w.key]=best.assign[w.key];});
      // Purge : dérogations journalières, remplacements Tour et TP de la période — repartir propre
      setTimeout(()=>purgeTourExtras(weeksT.map(w=>w.key)),20);
      // Retirer les activités (PT) de tous les tourneurs affectés
      const clearPairs=[];
      weeksT.forEach(w=>{
        const a2=best.assign[w.key]||{};
        [...(a2.HC||[]),...(a2.USIC||[])].forEach(mid=>clearPairs.push({medId:mid,weekKey:w.key}));
      });
      if(clearPairs.length>0)setTimeout(()=>clearWeekActivities(clearPairs),40);
      // Temps partiels affectés en USIC : dérogation + TP + junior (léger différé pour lire le tourMed à jour)
      setTimeout(()=>{
        const byMed={};
        weeksT.forEach(w=>{
          ((best.assign[w.key]||{}).USIC||[]).forEach(mid=>{
            const md=medecins.find(m2=>m2.id===mid);
            if(md&&md.partTime)(byMed[mid]=byMed[mid]||[]).push(w.key);
          });
        });
        Object.keys(byMed).forEach(mid=>applyTPForWeek(parseInt(mid),byMed[mid]));
      },80);return n;});
    const minBySpec=hardMins;
    const lockedInfo=(m)=>{
      if(!m.surSpec)return"";
      const nSpec=medecins.filter(x=>x.role==="medecin"&&(x.statut||"senior")!=="junior"&&x.surSpec===m.surSpec).length;
      return nSpec<=(minBySpec[m.surSpec]||0)?" [bloqué: seul(s) "+m.surSpec+"]":"";
    };
    const leftover=tourMeds.filter(m=>best.quota[m.id]>0).map(m=>m.init+"("+best.quota[m.id]+")"+lockedInfo(m));
    const minsTxt=" (idéal: "+minsLabel(idealMins)+" — min: "+minsLabel(hardMins)+")";
    let msg=(bestStage.label==="standard"?"Répartition effectuée.":"Répartition effectuée — mode: "+bestStage.label+".")+minsTxt;
    if(best.unfilled>0)msg+=" ⚠ "+best.unfilled+" semaine(s) incomplète(s) malgré toutes les relaxations.";
    else msg+=" ✓ Toutes les semaines sont complètes (2 HC + 2 USIC).";
    // Semaines où il reste moins de coro dispo que le minimum standard
    const lowCoroW=weeksT.filter(w2=>{
      const busyL=[...best.assign[w2.key].HC,...best.assign[w2.key].USIC].map(String);
      const nC=medecins.filter(m=>m.role==="medecin"&&(m.statut||"senior")!=="junior"&&m.surSpec==="coro"&&!busyL.includes(String(m.id))&&!isBlockedInWeek(m.id,w2.key)).length;
      return nC<cfgMinCoro;
    }).map(w2=>w2.label);
    if(best.relaxedWeeks&&best.relaxedWeeks.length>0)msg+=" ⚠ Semaines passées au minimum: "+best.relaxedWeeks.join(", ")+".";
    else msg+=" Idéal de surspécialités respecté chaque semaine.";
    if(best.avoidViol&&best.avoidViol.length>0)msg+=" ⚠ Préférences \"pas de tour\" non respectées: "+best.avoidViol.join(", ")+".";
    if(lowCoroW.length>0)msg+=" (Moins de "+cfgMinCoro+" coro dispo: "+lowCoroW.join(", ")+")";
    if(leftover.length>0)msg+=" Quota restant: "+leftover.join(", ");
    setLastReport(msg);
    toast(msg);
    setAutoModal(false);
  };
  return(
    <div>
      <div style={S.bar}>
        <div style={{display:"flex",alignItems:"center",gap:6}}>
          <button onClick={prevPeriodT} style={S.arr}>‹</button>
          <h2 style={S.mTit}>{"🔄 Tour médical — "+perLabelT+" "+perT.startY}</h2>
          <button onClick={nextPeriodT} style={S.arr}>›</button>
        </div>
        <div style={{display:"flex",gap:4,alignItems:"center",marginLeft:"auto"}}>
          <button onClick={()=>setDarkMode(d=>!d)} style={{...S.arr,fontSize:13,width:30}}>{darkMode?"☀️":"🌓"}</button>
        </div>
      </div>
      <div style={{display:"flex",gap:6,alignItems:"center",marginBottom:10}}>
          {isEdit&&<button onClick={openAutoModal} title="Répartition automatique" style={{fontSize:11,padding:"3px 12px",borderRadius:6,border:"1.5px solid #7c3aed",background:"rgba(124,58,237,.10)",color:"#7c3aed",fontWeight:800,cursor:"pointer"}}>⚙️ Répartition auto</button>}
          {isEdit&&<button onClick={()=>{
            if(!window.confirm("Supprimer TOUTES les attributions du tour sur la période affichée ?"))return;
            if(!window.confirm("Confirmez-vous la suppression définitive ? (récupérable via le bouton Annuler ↶)"))return;
            setTourMed(p=>{const n={...p};weeksT.forEach(w=>{delete n[w.key];});return n;});
            setLastReport(null);
            toast("Attributions de la période supprimées","info");
          }} title="Effacer toutes les attributions de la période" style={{fontSize:11,padding:"3px 12px",borderRadius:6,border:"1px solid #dc2626",background:"var(--bg2)",color:"#dc2626",fontWeight:700,cursor:"pointer"}}>🗑 Retirer</button>}
      </div>
      {isEdit&&lastReport&&<div style={{display:"flex",alignItems:"flex-start",gap:8,padding:"8px 12px",marginBottom:10,borderRadius:8,border:"1px solid var(--border)",background:"var(--bg2)",fontSize:11,color:"var(--txt2)"}}>
        <span style={{flexShrink:0}}>ℹ️</span>
        <span style={{flex:1}}>{lastReport}{(()=>{const all=[];weeksT.forEach(w2=>weekTPInfo(w2.key).forEach(t3=>all.push(t3)));return all.length>0?" ✂ Remplacements TP : "+all.join(" · ")+".":"";})()}</span>
        
      </div>}
      <div style={{display:"flex",gap:6,overflowX:"auto",marginBottom:14,paddingBottom:4,position:"sticky",top:44,zIndex:30,background:"var(--bg)",paddingTop:4}}>
        {tourMeds.map(m=>{
          const hcCount=weeksT.reduce((n,w)=>{const wm2=tourMed[w.key]||{};return (wm2.HC||[]).includes(m.id)?n+1:n;},0);
          const usicCount=weeksT.reduce((n,w)=>{const wm2=tourMed[w.key]||{};return (wm2.USIC||[]).includes(m.id)?n+1:n;},0);
          const total=hcCount+usicCount;
          const isExcl=savedCfg&&savedCfg.excl&&savedCfg.excl[m.id];
          const nActifs=tourMeds.length||1;
          const quotaN=isExcl?0:(savedCfg&&savedCfg.weeks&&savedCfg.weeks[m.id]!==undefined?savedCfg.weeks[m.id]:Math.ceil((weeksT.length*4)/nActifs));
          const quotaOK=total>=quotaN;
          return(
            <div key={m.id} style={{...S.card,textAlign:"center",minWidth:64,flexShrink:0,padding:"7px 9px",opacity:quotaOK?1:.55,filter:quotaOK?"none":"grayscale(.35)"}} title={total+"/"+quotaN+" semaines"}>
              <Av med={m}/>
              <div style={{fontWeight:800,fontSize:14,color:m.color,fontFamily:"'JetBrains Mono',monospace",marginTop:3}}>{total}</div>
              <div style={{display:"flex",gap:4,justifyContent:"center",marginTop:2}}>
                <span style={{fontSize:9,color:"#388bfd",fontWeight:700}}>{hcCount}<span style={{fontWeight:400}}>HC</span></span>
                <span style={{fontSize:9,color:"#a371f7",fontWeight:700}}>{usicCount}<span style={{fontWeight:400}}>US</span></span>
              </div>
            </div>
          );
        })}
      </div>
      {weeksT.map(w=>{
        const wm=tourMed[w.key]||{HC:[],USIC:[]};
        const incomplete=(wm.HC||[]).length<2||(wm.USIC||[]).length<2;
        return(
          <div key={w.key} style={{...S.tmRow,...(incomplete?{background:"rgba(128,134,148,.10)",borderColor:"rgba(128,134,148,.35)"}:{})}}>
            <div style={{fontSize:12,fontWeight:700,color:"var(--txt2)",width:"100%",marginBottom:2,display:"flex",alignItems:"center",gap:8,flexWrap:"wrap"}}>
              <span>Sem. {w.label}</span>
              {weekTPInfo(w.key).map((t3,i3)=><span key={i3} style={{fontSize:10,fontWeight:700,color:"#8b5cf6",padding:"1px 8px",borderRadius:5,background:"rgba(139,92,246,.10)",border:"1px solid rgba(139,92,246,.35)"}}>✂ {t3}</span>)}
              {isEdit&&<button style={{fontSize:11,padding:"3px 10px",borderRadius:6,border:"1.5px solid #388bfd",background:"rgba(56,139,253,.10)",color:"#388bfd",cursor:"pointer",fontWeight:800}}
                onClick={()=>{setSwapSrcKey(w.key);setSwapSrcMed(null);setSwapDstKey(w.key);setSwapDstMed(null);setSwapUpdPlan(true);setSwapOpen(true);}}>⇄ Échanger</button>}
              <span style={{display:"flex",gap:7,alignItems:"center",flexWrap:"wrap",padding:"1px 7px",borderRadius:5,background:"var(--bg2)",border:"1px solid var(--border2)"}}>
                {[["coro","Coro"],["pace","Pace"],["eep","EEP"],["ett","ETT"]].map(([sk2,lb2])=>{
                  const wmS=tourMed[w.key]||{HC:[],USIC:[]};
                  const busyS=[...(wmS.HC||[]),...(wmS.USIC||[])].map(String);
                  const nDispo=medecins.filter(m=>m.role==="medecin"&&(m.statut||"senior")!=="junior"&&m.surSpec===sk2&&!busyS.includes(String(m.id))&&!isBlockedInWeek(m.id,w.key)).length;
                  const minS=(tourMins||{})[sk2]||0;
                  const lowS=nDispo<minS;
                  return <span key={sk2} title={"Séniors "+lb2+" disponibles (hors tour, hors absents) — minimum réglé: "+minS}
                    style={{fontSize:9,fontWeight:800,color:lowS?"#ef4444":(SPEC_COLORS[sk2]||"var(--txt3)")}}>{lb2} {nDispo}{lowS?" ⚠":""}</span>;
                })}
              </span>
              {horsTourSpecMeds.length>0&&<span style={{display:"flex",gap:4,alignItems:"center",flexWrap:"wrap"}}>
                <span style={{fontSize:8,color:"var(--txt3)",fontWeight:600,textTransform:"uppercase"}}>Hors tour:</span>
                {horsTourSpecMeds.map(hm=>{
                  const hBlocked=isBlockedInWeek(hm.id,w.key);
                  return(
                    <span key={hm.id} title={hm.prenom+" "+hm.nom+" ("+hm.surSpec+") — "+(hBlocked?"absent/formation":"présent")}
                      style={{fontSize:9,fontWeight:800,padding:"1px 6px",borderRadius:5,cursor:"default",
                        border:"1.5px solid "+(SPEC_COLORS[hm.surSpec]||"var(--border)"),
                        color:hBlocked?"var(--txt3)":(SPEC_COLORS[hm.surSpec]||"var(--txt2)"),
                        background:"transparent",
                        opacity:hBlocked?.4:1,
                        textDecoration:hBlocked?"line-through":"none"}}>
                      {hm.init}{hBlocked?" ✕":""}
                    </span>
                  );
                })}
              </span>}
            </div>
            {["HC","USIC"].map(unit=>(
              <div key={unit} style={{flex:1,minWidth:170}}>
                <div style={{fontSize:10,fontWeight:700,color:unit==="HC"?"#388bfd":"#a371f7",marginBottom:4}}>{unit}</div>
                <div style={{display:"flex",gap:4,flexWrap:"wrap"}}>
                  {tourMeds.map(m=>{
                    const on=(wm[unit]||[]).includes(m.id);
                    const blocked=isBlockedInWeek(m.id,w.key);
                    const inOther=(wm[unit==="HC"?"USIC":"HC"]||[]).includes(m.id);
                    const dis=blocked||inOther;
                    const avoidW=!!((tourAvoid||{})[w.key]||{})[m.id];
                    const wishW=!!((tourWish||{})[w.key]||{})[m.id];
                    return(
                      <button key={m.id} disabled={dis||!isEdit}
                        style={{padding:"3px 6px",borderRadius:6,border:"none",cursor:dis||!isEdit?"default":"pointer",textAlign:"center",minWidth:44,
                          background:on?m.color:"var(--bg2)",color:on?"#fff":"var(--txt2)",opacity:dis?.3:1,
                          outline:on?"2px solid "+m.color:m.surSpec&&!blocked?"2px solid "+({coro:"#76a5af",pace:"#e3b341",eep:"#f97316",ett:"#ea9999"}[m.surSpec]||"var(--border)"):"1px solid var(--border)"}}
                        onClick={()=>{if(dis||!isEdit)return;
                        const wasOn=on;
                        setTourMed(p=>{const cur={...(p[w.key]||{HC:[],USIC:[]})};const l=cur[unit]||[];if(!wasOn&&l.length>=2){toast("Maximum 2 médecins par unité","info");return p;}cur[unit]=wasOn?l.filter(x=>x!==m.id):[...l,m.id];return{...p,[w.key]:cur};});
                        if(!wasOn){
                          clearWeekActivities([{medId:m.id,weekKey:w.key}]);
                          if(unit==="USIC"&&m.partTime)setTimeout(()=>applyTPForWeek(m.id,w.key),60);
                        }else{
                          if(unit==="USIC"&&m.partTime)cleanTPForWeek(m.id,w.key);
                          setTimeout(()=>reapplyPTWeek(m.id,w.key),60);
                        }}}>
                        <div style={{fontWeight:800,fontSize:10}} title={avoidW?"Préfère ne pas tourner cette semaine":wishW?"Souhaite tourner cette semaine":""}>{m.init}{avoidW?" 🚫":wishW?" ⭐":""}</div>
                        <div style={{fontSize:8,color:blocked?"inherit":m.surSpec&&!on?({coro:"#76a5af",pace:"#e3b341",eep:"#f97316",ett:"#ea9999"}[m.surSpec]):"inherit"}}>
                          {blocked?"indispo":inOther?"≠":""}
                        </div>
                      </button>
                    );
                  })}
                </div>
                <div style={{marginTop:4,display:"flex",alignItems:"center",gap:8}}>
                  <span style={{fontSize:11,fontWeight:800,fontFamily:"'JetBrains Mono',monospace",color:(wm[unit]||[]).length===2?"#3fb950":(wm[unit]||[]).length>2?"#f85149":"#e3b341"}}>{(wm[unit]||[]).length}/2</span>
                  
                </div>
              </div>
            ))}
          </div>
        );
      })}

      {/* Modale d'échange */}
      {swapOpen&&(
        <Ov onClose={()=>setSwapOpen(false)}>
          <div style={{...S.modal,maxWidth:560,maxHeight:"88vh",overflowY:"auto"}} onClick={e=>e.stopPropagation()}>
            <div style={{display:"flex",justifyContent:"space-between",alignItems:"center",marginBottom:8}}>
              <div style={S.mTit2}>⇄ Échanger deux semaines de tour</div>
              <button onClick={()=>setSwapOpen(false)} style={S.xBtn}>×</button>
            </div>
            <div style={{display:"flex",gap:10,alignItems:"stretch"}}>
              <div style={{flex:1,padding:10,borderRadius:9,border:"1px solid var(--border)",background:"var(--bg2)"}}>
                <div style={{fontSize:10,fontWeight:800,color:"var(--txt3)",textTransform:"uppercase",marginBottom:6}}>Praticien A — sem. {(weeksT.find(w2=>w2.key===swapSrcKey)||{}).label}</div>
                {["HC","USIC"].map(u2=>((tourMed[swapSrcKey]||{})[u2]||[]).map(mid=>{
                  const md=medecins.find(m2=>m2.id===mid);if(!md)return null;
                  const sel=swapSrcMed===mid;
                  return(<div key={mid} onClick={()=>setSwapSrcMed(mid)} style={{display:"flex",alignItems:"center",gap:7,padding:"7px 9px",borderRadius:7,marginBottom:5,cursor:"pointer",border:"2px solid "+(sel?"#388bfd":"var(--border2)"),background:sel?"rgba(56,139,253,.14)":"var(--bg)"}}>
                    <span style={{width:20,height:20,borderRadius:"50%",background:md.color,color:"#fff",fontSize:8,fontWeight:800,display:"inline-flex",alignItems:"center",justifyContent:"center"}}>{md.init}</span>
                    <span style={{fontSize:12,fontWeight:700,color:"var(--txt)",flex:1}}>{md.nom}</span>
                    <span style={{fontSize:10,fontWeight:800,color:u2==="HC"?"#388bfd":"#a371f7"}}>{u2}</span>
                  </div>);
                }))}
                {((tourMed[swapSrcKey]||{}).HC||[]).length+((tourMed[swapSrcKey]||{}).USIC||[]).length===0&&<div style={{fontSize:11,color:"var(--txt3)"}}>Aucun tourneur cette semaine.</div>}
              </div>
              <div style={{display:"flex",alignItems:"center",fontSize:26,color:"#388bfd",fontWeight:800}}>⇄</div>
              <div style={{flex:1,padding:10,borderRadius:9,border:"1px solid var(--border)",background:"var(--bg2)"}}>
                <div style={{fontSize:10,fontWeight:800,color:"var(--txt3)",textTransform:"uppercase",marginBottom:6}}>Praticien B — semaine :</div>
                <select value={swapDstKey||""} onChange={e=>{setSwapDstKey(e.target.value);setSwapDstMed(null);}}
                  style={{width:"100%",padding:"6px 8px",borderRadius:7,border:"1px solid var(--border)",background:"var(--inp)",color:"var(--txt)",fontSize:12,marginBottom:8}}>
                  {weeksT.map(w2=><option key={w2.key} value={w2.key}>Sem. {w2.label}{w2.key===swapSrcKey?" (même semaine)":""}</option>)}
                </select>
                {["HC","USIC"].map(u2=>((tourMed[swapDstKey]||{})[u2]||[]).map(mid=>{
                  const md=medecins.find(m2=>m2.id===mid);if(!md)return null;
                  const sel=swapDstMed===mid;
                  const same=mid===swapSrcMed;
                  return(<div key={mid} onClick={()=>{if(!same)setSwapDstMed(mid);}} style={{display:"flex",alignItems:"center",gap:7,padding:"7px 9px",borderRadius:7,marginBottom:5,cursor:same?"not-allowed":"pointer",opacity:same?.35:1,border:"2px solid "+(sel?"#388bfd":"var(--border2)"),background:sel?"rgba(56,139,253,.14)":"var(--bg)"}}>
                    <span style={{width:20,height:20,borderRadius:"50%",background:md.color,color:"#fff",fontSize:8,fontWeight:800,display:"inline-flex",alignItems:"center",justifyContent:"center"}}>{md.init}</span>
                    <span style={{fontSize:12,fontWeight:700,color:"var(--txt)",flex:1}}>{md.nom}</span>
                    <span style={{fontSize:10,fontWeight:800,color:u2==="HC"?"#388bfd":"#a371f7"}}>{u2}</span>
                  </div>);
                }))}
              </div>
            </div>
            {swapSrcMed&&swapDstMed&&(()=>{
              const mS=medecins.find(m2=>m2.id===swapSrcMed)||{},mD=medecins.find(m2=>m2.id===swapDstMed)||{};
              const lS=(weeksT.find(w2=>w2.key===swapSrcKey)||{}).label,lD=(weeksT.find(w2=>w2.key===swapDstKey)||{}).label;
              const uS=unitOf(swapSrcMed,swapSrcKey),uD=unitOf(swapDstMed,swapDstKey);
              const sameWeek=swapSrcKey===swapDstKey;
              // Bloquants
              const blocks=[];
              if(!sameWeek&&unitOf(swapSrcMed,swapDstKey))blocks.push(mS.init+" est déjà de tour la semaine du "+lD+".");
              if(!sameWeek&&unitOf(swapDstMed,swapSrcKey))blocks.push(mD.init+" est déjà de tour la semaine du "+lS+".");
              // Avertissements
              const warns=[];
              if(!sameWeek){
                const aS=absDaysOf(swapSrcMed,swapDstKey);
                if(aS.length>=5)warns.push(mS.init+" est absent TOUTE la semaine du "+lD+".");
                else if(aS.length>0)warns.push(mS.init+" est absent le "+aS.join(", le ")+" (sem. du "+lD+") — un remplacement ponctuel reste possible.");
                const aD=absDaysOf(swapDstMed,swapSrcKey);
                if(aD.length>=5)warns.push(mD.init+" est absent TOUTE la semaine du "+lS+".");
                else if(aD.length>0)warns.push(mD.init+" est absent le "+aD.join(", le ")+" (sem. du "+lS+") — un remplacement ponctuel reste possible.");
                if(((tourAvoid||{})[swapDstKey]||{})[swapSrcMed])warns.push(mS.init+" a une préférence 🚫 \"pas de tour\" sur la semaine du "+lD+".");
                if(((tourAvoid||{})[swapSrcKey]||{})[swapDstMed])warns.push(mD.init+" a une préférence 🚫 \"pas de tour\" sur la semaine du "+lS+".");
              }
              return(
              <div style={{marginTop:12}}>
                <div style={{padding:"10px 12px",borderRadius:9,border:"2px solid #388bfd",background:"rgba(56,139,253,.08)",fontSize:14,fontWeight:800,color:"var(--txt)",textAlign:"center"}}>
                  {mS.init} <span style={{color:uS==="HC"?"#388bfd":"#a371f7"}}>{uS}</span> sem. {lS}
                  <span style={{margin:"0 10px",color:"#388bfd"}}>⇄</span>
                  {mD.init} <span style={{color:uD==="HC"?"#388bfd":"#a371f7"}}>{uD}</span> sem. {lD}
                </div>
                {blocks.map((b,i2)=><div key={i2} style={{marginTop:6,padding:"7px 10px",borderRadius:7,border:"1px solid #dc2626",background:"rgba(220,38,38,.10)",fontSize:12,fontWeight:700,color:"#dc2626"}}>⛔ {b}</div>)}
                {warns.map((wn,i2)=><div key={i2} style={{marginTop:6,padding:"7px 10px",borderRadius:7,border:"1px solid #f59e0b",background:"rgba(245,158,11,.10)",fontSize:12,fontWeight:600,color:"#b45309"}}>⚠ {wn}</div>)}
                {!sameWeek&&<label style={{display:"flex",gap:6,alignItems:"center",fontSize:12,color:"var(--txt)",marginTop:10,cursor:"pointer"}}>
                  <input type="checkbox" checked={swapUpdPlan} onChange={e=>setSwapUpdPlan(e.target.checked)} style={{width:14,height:14}}/>
                  Mettre à jour le planning des 2 praticiens (retirer les activités sur la semaine d'arrivée, ré-appliquer le planning type sur la semaine quittée)
                </label>}
                {sameWeek&&<div style={{fontSize:11,color:"var(--txt3)",marginTop:8}}>Échange HC ⇄ USIC au sein de la même semaine : le planning n'est pas modifié.</div>}
                <div style={{display:"flex",gap:8,justifyContent:"flex-end",marginTop:12}}>
                  <button onClick={()=>setSwapOpen(false)} style={{padding:"9px 16px",borderRadius:8,border:"1px solid var(--border)",background:"var(--bg2)",color:"var(--txt2)",fontWeight:700,fontSize:13,cursor:"pointer"}}>Annuler</button>
                  <button disabled={blocks.length>0} onClick={runSwap}
                    style={{...S.btnP,padding:"9px 20px",opacity:blocks.length>0?.4:1,cursor:blocks.length>0?"not-allowed":"pointer"}}>⇄ Valider l'échange</button>
                </div>
              </div>);
            })()}
            {(!swapSrcMed||!swapDstMed)&&<div style={{fontSize:11,color:"var(--txt3)",marginTop:12,textAlign:"center"}}>Sélectionnez un praticien dans chaque panneau.</div>}
          </div>
        </Ov>
      )}
      {/* Auto-répartition modal */}
      {autoModal&&(
        <Ov onClose={closeAutoModal}>
          <div style={{minWidth:400,maxWidth:520}}>
            <div style={S.mHd}>
              <div style={S.mTit2}>⚙️ Répartition automatique — {perLabelT} {perT.startY}</div>
              <button onClick={closeAutoModal} style={S.xBtn}>×</button>
            </div>
            <div style={{fontSize:11,color:"var(--txt3)",marginBottom:10}}>
              {weeksT.length} semaines × 4 créneaux (2 HC + 2 USIC) = {totalSlots} — {activeMeds.length} participant{activeMeds.length>1?"s":""} — nominal <b style={{color:"var(--txt)"}}>{nominalW} sem/médecin</b> (arrondi sup.)
            </div>
            {/* Contraintes surspécialités */}
            <div style={{marginBottom:12,padding:10,borderRadius:8,background:"var(--bg2)",border:"1px solid var(--border)"}}>
              <div style={{fontSize:10,color:"var(--txt3)",fontWeight:700,textTransform:"uppercase",marginBottom:6}}>Minimum de séniors disponibles / semaine (hors tour, hors absents)</div>
              <div style={{display:"flex",gap:14,flexWrap:"wrap"}}>
                {[["Coro",cfgMinCoro,setCfgMinCoro],["Pace",cfgMinPace,setCfgMinPace],["EEP",cfgMinEEP,setCfgMinEEP],["ETT",cfgMinETT,setCfgMinETT]].map(([lb,v,setV])=>(
                  <label key={lb} style={{display:"flex",alignItems:"center",gap:6,fontSize:12,color:"var(--txt)"}}>
                    {lb}
                    <input type="number" min={0} max={9} value={v} onChange={e=>setV(Math.max(0,parseInt(e.target.value)||0))}
                      style={{width:44,padding:"4px 6px",borderRadius:6,border:"1px solid var(--border)",background:"var(--inp)",color:"var(--txt)",fontSize:13,textAlign:"center"}}/>
                  </label>
                ))}
              </div>
            </div>
            {/* Config par médecin */}
            <div style={{maxHeight:280,overflowY:"auto",borderRadius:8,border:"1px solid var(--border)"}}>
              <table style={{borderCollapse:"collapse",width:"100%"}}>
                <thead>
                  <tr style={{background:"var(--bg2)",borderBottom:"2px solid var(--border)"}}>
                    <th style={{textAlign:"left",padding:"5px 8px",fontSize:10,color:"var(--txt3)"}}>Médecin</th>
                    <th style={{textAlign:"center",padding:"5px 8px",fontSize:10,color:"var(--txt3)"}}>Absent</th>
                    <th style={{textAlign:"center",padding:"5px 8px",fontSize:10,color:"var(--txt3)"}}>Semaines</th>
                    <th style={{textAlign:"center",padding:"5px 8px",fontSize:10,color:"var(--txt3)"}}>2 sem. HC</th>
                    <th style={{textAlign:"center",padding:"5px 8px",fontSize:10,color:"var(--txt3)"}}>2 sem. USIC</th>
                    <th style={{textAlign:"center",padding:"5px 8px",fontSize:10,color:"var(--txt3)"}}>Spéc.</th>
                  </tr>
                </thead>
                <tbody>
                  {tourMeds.map(m=>(
                    <tr key={m.id} style={{borderBottom:"1px solid var(--border2)",opacity:cfgExcl[m.id]?.45:1}}>
                      <td style={{padding:"5px 8px"}}>
                        <div style={{display:"flex",alignItems:"center",gap:6}}>
                          <div style={{width:20,height:20,borderRadius:"50%",background:m.color,display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:8,fontWeight:800}}>{m.init}</div>
                          <span style={{fontSize:11,fontWeight:600,color:"var(--txt)",textDecoration:cfgExcl[m.id]?"line-through":"none"}}>{m.prenom} {m.nom}</span>
                        </div>
                      </td>
                      <td style={{textAlign:"center",padding:"4px"}}>
                        <input type="checkbox" checked={!!cfgExcl[m.id]}
                          onChange={()=>toggleExcl(m.id)}
                          style={{width:15,height:15,cursor:"pointer"}}/>
                      </td>
                      <td style={{textAlign:"center",padding:"4px"}}>
                        <input type="number" min={0} max={weeksT.length} value={cfgWeeks[m.id]||0} disabled={!!cfgExcl[m.id]}
                          onChange={e=>setCfgWeeks(p=>({...p,[m.id]:Math.max(0,parseInt(e.target.value)||0)}))}
                          style={{width:48,padding:"4px 6px",borderRadius:6,border:"1px solid var(--border)",background:"var(--inp)",color:"var(--txt)",fontSize:13,textAlign:"center"}}/>
                      </td>
                      <td style={{textAlign:"center",padding:"4px"}}>
                        <input type="checkbox" checked={!!cfgPref2HC[m.id]}
                          onChange={e=>setCfgPref2HC(p=>({...p,[m.id]:e.target.checked}))}
                          style={{width:15,height:15,cursor:"pointer"}}/>
                      </td>
                      <td style={{textAlign:"center",padding:"4px"}}>
                        <input type="checkbox" checked={!!cfgPref2USIC[m.id]}
                          onChange={e=>setCfgPref2USIC(p=>({...p,[m.id]:e.target.checked}))}
                          style={{width:15,height:15,cursor:"pointer"}}/>
                      </td>
                      <td style={{textAlign:"center",padding:"4px",fontSize:9,color:"var(--txt3)"}}>
                        {(m.statut==="junior")&&<span style={{color:"#f59e0b",fontWeight:700}}>Jr </span>}
                        {({coro:"Coro",pace:"Pace",eep:"EEP",ett:"ETT"})[m.surSpec]||"—"}
                      </td>
                    </tr>
                  ))}
                </tbody>
              </table>
            </div>
            <div style={{marginTop:6,fontSize:11,color:"var(--txt3)"}}>
              Total configuré: <b style={{color:"var(--txt)"}}>{Object.values(cfgWeeks).reduce((a,b)=>a+b,0)}</b> / {totalSlots} créneaux
            </div>
            <div style={{display:"flex",gap:8,marginTop:12}}>
              <button onClick={runAutoRepartition}
                style={{flex:1,padding:"9px",borderRadius:8,border:"none",background:"#1d4ed8",color:"#fff",fontWeight:800,fontSize:13,cursor:"pointer"}}>
                🚀 Lancer la répartition
              </button>
              <button onClick={closeAutoModal}
                style={{padding:"9px 16px",borderRadius:8,border:"1px solid var(--border)",background:"var(--bg2)",color:"var(--txt2)",fontWeight:700,fontSize:13,cursor:"pointer"}}>
                Fermer (enregistre la config)
              </button>
            </div>
            <div style={{marginTop:8,fontSize:10,color:"#ef4444"}}>⚠ La répartition remplace toutes les assignations existantes de la période.</div>
          </div>
        </Ov>
      )}
    </div>
  );
}

function StatsTab({medecins,actes,plan,year,month,darkMode,setDarkMode,tourMed}){
  const [statsYear,setStatsYear]=React.useState(()=>new Date().getFullYear());
  const [statsMonth,setStatsMonth]=React.useState(()=>new Date().getMonth());
  const [statSite,setStatSite]=React.useState("tous");
  const _ps=perStart(statsYear,statsMonth);
  const per={startY:_ps.sy,startM:_ps.sm};
  const perLabelS=MOIS[per.startM]+" — "+MOIS[(per.startM+PCFG.len-1)%12];
  const prevP=()=>{const p=perPrev(per.startY,per.startM);setStatsMonth(p.sm);setStatsYear(p.sy);};
  const nextP=()=>{const p=perNext(per.startY,per.startM);setStatsMonth(p.sm);setStatsYear(p.sy);};

  // Build all days in period
  const days=perDaysList(per.startY,per.startM);

  // Activities to track (exclude system ones)
  const trackActes=actes.filter(a=>!a.isSystem&&a.id!=="ABSENCE"&&a.id!=="REPOS_GARDE").sort((a,b)=>a.label.localeCompare(b.label));
  const GARDE_ACTE={id:"GARDE",label:"Garde",short:"G",color:"#93c47d"};
  const GARDE_SEM={id:"GARDE_SEM",label:"Garde semaine (lun→mer)",short:"G sem",color:"#93c47d"};
  const GARDE_JEU={id:"GARDE_JEU",label:"Garde jeudi",short:"G jeu",color:"#6aa84f"};
  const GARDE_WE={id:"GARDE_WE",label:"Garde WE et fériés",short:"G WE",color:"#f59e0b"};
  const allTrack=[GARDE_ACTE,GARDE_SEM,GARDE_JEU,GARDE_WE,...trackActes];

  // Count per med per acte
  const allStatMeds=medecins.filter(m=>m.role==="medecin");
  const [medFilter,setMedFilter]=React.useState([]);
  const [sortCol,setSortCol]=React.useState(null); // {col,dir:'desc'|'asc'}
  const meds=medFilter.length>0?allStatMeds.filter(m=>medFilter.includes(m.id)):allStatMeds;
  const counts={};
  meds.forEach(m=>{counts[m.id]={};allTrack.forEach(a=>{counts[m.id][a.id]=0;});});

  days.forEach(({y:y2,m:m2,d})=>{
    ["M","AM","JOUR","N"].forEach(sl=>{
      const slotData=plan[y2+"-"+String(m2+1).padStart(2,"0")+"-"+String(d).padStart(2,"0")+"|"+sl]||{};
      // Use sk function equivalent
      Object.keys(slotData).forEach(mid=>{
        const medId=parseInt(mid);
        if(!counts[medId])return;
        const e=slotData[mid];
        const entries=Array.isArray(e)?e:[e];
        entries.forEach(entry=>{
          if(!entry||!entry.acteId)return;
          if(counts[medId][entry.acteId]!==undefined) counts[medId][entry.acteId]++;
          // Garde: split by weekday (ven/sam/dim = weekend)
          if(entry.acteId==="GARDE"){
            const dw4=new Date(y2,m2,d).getDay();
            const nxS=new Date(y2,m2,d+1);
            const veilleF=dw4>=1&&dw4<=5&&isFerie(nxS.getFullYear(),nxS.getMonth(),nxS.getDate());
            const isWEg=isFerie(y2,m2,d)||dw4===5||dw4===6||dw4===0||veilleF;
            const gk=isWEg?"GARDE_WE":dw4===4?"GARDE_JEU":"GARDE_SEM";
            if(counts[medId][gk]!==undefined)counts[medId][gk]++;
          }
        });
      });
    });
  });

  // Column totals
  const colTotals={};
  allTrack.forEach(a=>{colTotals[a.id]=meds.reduce((n,m)=>n+(counts[m.id]?counts[m.id][a.id]||0:0),0);});
  // Only show columns with at least 1 entry
  const usedActes=allTrack.filter(a=>colTotals[a.id]>0);
  const displayMeds=sortCol?[...meds].sort((a,b)=>{
    const va=(counts[a.id]&&counts[a.id][sortCol.col])||0;
    const vb=(counts[b.id]&&counts[b.id][sortCol.col])||0;
    return sortCol.dir==="desc"?vb-va:va-vb;
  }):meds;

  const exportCSV=()=>{
    const header=["Médecin",...usedActes.map(a=>a.short),"Total"].join(";");
    const rows=meds.map(m=>{
      const row=[m.prenom+" "+m.nom,...usedActes.map(a=>counts[m.id][a.id]||0),usedActes.reduce((n,a)=>n+(counts[m.id][a.id]||0),0)];
      return row.join(";");
    });
    const csv=[header,...rows].join("\n");
    const blob=new Blob([csv],{type:"text/csv"});
    const url=URL.createObjectURL(blob);
    const a=document.createElement("a");a.href=url;a.download="stats_cardio.csv";a.click();
  };

  return(
    <div>
      <div style={S.bar}>
        <div style={{display:"flex",alignItems:"center",gap:6}}>
          <button onClick={prevP} style={S.arr}>‹</button>
          <h2 style={S.mTit}>{"📊 Stats — "+perLabelS+" "+per.startY}</h2>
          <button onClick={nextP} style={S.arr}>›</button>
        </div>
        <div style={{display:"flex",gap:4,alignItems:"center",marginLeft:"auto"}}>
          <button onClick={()=>setDarkMode(d=>!d)} style={{...S.arr,fontSize:13,width:30}}>{darkMode?"☀️":"🌓"}</button>
        </div>
      </div>
        <div style={{display:"flex",gap:6,alignItems:"center",marginBottom:10}}>
          <button onClick={exportCSV} style={{...S.btnP,fontSize:11,padding:"3px 10px"}}>🖨️ Export</button>
        </div>
      <div style={{display:"flex",gap:5,flexWrap:"wrap",marginBottom:10}}>
        <button onClick={()=>setMedFilter([])}
          style={{padding:"4px 10px",borderRadius:20,border:"1px solid var(--border)",cursor:"pointer",fontSize:11,fontWeight:700,
            background:medFilter.length===0?"#1d4ed8":"var(--bg2)",color:medFilter.length===0?"#fff":"var(--txt2)"}}>Tous</button>
        {allStatMeds.map(m=>{
          const on=medFilter.includes(m.id);
          return <button key={m.id} onClick={()=>setMedFilter(p=>on?p.filter(x=>x!==m.id):[...p,m.id])}
            style={{padding:"4px 10px",borderRadius:20,border:"1px solid "+(on?m.color:"var(--border)"),cursor:"pointer",fontSize:11,fontWeight:700,
              background:on?m.color:"var(--bg2)",color:on?"#111":"var(--txt2)"}}>{m.init}</button>;
        })}
      </div>
      <div style={{overflowX:"auto",overflowY:"auto",maxHeight:"calc(100vh - 190px)",borderRadius:8,border:"1px solid var(--border)"}}>
        <table style={{borderCollapse:"collapse",fontSize:11}}>
          <thead>
            <tr>
              <th style={{...S.thFix,position:"sticky",top:0,left:0,zIndex:40,minWidth:120,textAlign:"left",padding:"6px 10px"}}>Médecin</th>
              {usedActes.map(a=>{
                const isSorted=sortCol&&sortCol.col===a.id;
                return(
                <th key={a.id} onClick={()=>setSortCol(s=>{
                    if(!s||s.col!==a.id)return{col:a.id,dir:"desc"};
                    if(s.dir==="desc")return{col:a.id,dir:"asc"};
                    return null;
                  })}
                  title={!isSorted?"Trier par "+a.label+" (décroissant)":sortCol.dir==="desc"?"Trier croissant":"Revenir à l'ordre initial"}
                  style={{...S.thFix,position:"sticky",top:0,zIndex:20,minWidth:44,textAlign:"center",padding:"4px 2px",cursor:"pointer"}}>
                  <div style={{background:a.color,color:"#111",borderRadius:4,padding:"2px 4px",fontSize:9,fontWeight:800,fontFamily:"'JetBrains Mono',monospace",outline:isSorted?"2px solid var(--txt)":"none"}}>{a.short}{isSorted?(sortCol.dir==="desc"?" ▼":" ▲"):""}</div>
                </th>
                );
              })}

            </tr>
          </thead>
          <tbody>
            {displayMeds.map((m,ri)=>{
              return(
                <tr key={m.id} style={{background:ri%2===0?"var(--bg2)":"var(--bg)",borderBottom:"1px solid var(--border2)"}}>
                  <td style={{...S.tdFix,position:"sticky",left:0,zIndex:10,padding:"5px 10px",fontWeight:700,color:m.color,minWidth:120}}>
                    <div style={{display:"flex",alignItems:"center",gap:6}}>
                      <div style={{width:20,height:20,borderRadius:"50%",background:m.color,display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:8,fontWeight:800,flexShrink:0}}>{m.init}</div>
                      {m.prenom} {m.nom}
                    </div>
                  </td>
                  {usedActes.map(a=>{
                    const v=counts[m.id]?counts[m.id][a.id]||0:0;
                    return <td key={a.id} style={{textAlign:"center",padding:"4px 2px",color:v>0?"var(--txt)":"var(--txt3)",fontWeight:v>0?700:400,background:v>0?a.color+"22":"transparent"}}>{v||"—"}</td>;
                  })}

                </tr>
              );
            })}

          </tbody>
        </table>
      </div>
    </div>
  );
}

function CardioPlanning(){
  const today=new Date();
  const [accessMode,setAccessMode]=useState("ask");
  const [pinInput,setPinInput]=useState("");
  const [pinError,setPinError]=useState(false);
  const [editPin,setEditPin]=useState(EDIT_PIN_DEFAULT);
  const [editMedId,setEditMedId]=useState(null); // medecin logged in with personal PIN
  const [tab,setTab]=useState("planning");
  const [ym,setYM]=useState(()=>({year:new Date().getFullYear(),month:new Date().getMonth()}));
  const year=ym.year, month=ym.month;
  const setYear=y=>setYM(p=>({...p,year:typeof y==="function"?y(p.year):y}));
  const setMonth=m=>setYM(p=>({...p,month:typeof m==="function"?m(p.month):m}));
  const setYearMonth=(y,m)=>setYM({year:y,month:m});
  const [orient,setOrient]=useState("V"); // H/V toggle removed - V only
  const [darkMode,setDarkModeRaw]=useState(()=>{
    try{const v=localStorage.getItem("cp6_theme");if(v==="dark")return true;if(v==="light")return false;}catch(e){}
    const h=new Date().getHours();return h>=20||h<7; // auto : nuit de 20h à 7h
  });
  const setDarkMode=(fn)=>{setDarkModeRaw(prev=>{const nv=typeof fn==="function"?fn(prev):fn;try{localStorage.setItem("cp6_theme",nv?"dark":"light");}catch(e){}return nv;});};
  const DEFAULT_TABS=[["planning","📅 Planning"],["tourmedical","🔄 Tour"],["chl","🏥 CHL"],["chb","🏥 CHB"],["plateau","❤️ PT Cardio"],["angio","🔬 PT Angio"],["garde","🌙 Gardes"],["astreinte","📞 Astreinte"],["plantype","📋 Type"],["attache","👔 Attachés"],["activites","⚙️ Activités"],["equipe","👥 Équipe"],["partage","⚙️ Paramètres"],["stats","📊 Stats"]];
  const [tabOrder,setTabOrder]=useState(()=>{ try{ const v=localStorage.getItem("cp6_taborder"); if(v){ const saved=JSON.parse(v); const all=DEFAULT_TABS.map(t=>t[0]); const merged=[...saved.filter(id=>all.includes(id)),...all.filter(id=>!saved.includes(id))]; return merged; } return DEFAULT_TABS.map(t=>t[0]); }catch{ return DEFAULT_TABS.map(t=>t[0]); } });
  const [dragTab,setDragTab]=useState(null);
  useEffect(()=>{ try{ localStorage.setItem("cp6_taborder",JSON.stringify(tabOrder)); }catch{} },[tabOrder]);
  const orderedTabs=tabOrder.map(id=>DEFAULT_TABS.find(t=>t[0]===id)).filter(Boolean);

  const [modal,setModal]=useState(null);
  const [mData,setMData]=useState(null);
  const [notif,setNotif]=useState(null);
  const [planFilter,setPlanFilter]=useState([]);
  const [userProfile,setUserProfile]=useState(0);
  const [showFull,setShowFull]=useState(false);
  const viewPeriod=true;const setViewPeriod=()=>{};
  const snapToPeriodStart=React.useCallback((y,m)=>{
    const p=perStart(y,m);
    setYearMonth(p.sy,p.sm);
  },[]);
  const [medecins,setMedecins]=useState(MEDECINS_INIT);
  const [actes,setActes]=useState(DEFAULT_ACTES);
  const [plan,setPlan]=useState({});
  const [tourMed,setTourMed]=useState({});
  const [planningType,setPlanningType]=useState({});
  const [notes,setNotes]=useState({});
  const [medPins,setMedPins]=useState({}); // {medId: "pin"}
  const [tourMins,setTourMins]=useState({coro:3,pace:1,eep:1,ett:1});
  const [tourMinsHard,setTourMinsHard]=useState({coro:2,pace:1,eep:1,ett:0});
  const [tourCfg,setTourCfg]=useState({});
  const [tourAvoid,setTourAvoid]=useState({}); // {weekKey:{medId:true}} préférences "ne pas tourner"
  const [tourWish,setTourWish]=useState({});   // {weekKey:{medId:true}} souhaite tourner
  const [gardeAvoid,setGardeAvoid]=useState({}); // {dateKey:{medId:true}} préfère pas de garde ce jour
  const [gardeWish,setGardeWish]=useState({});   // {dateKey:{medId:true}} souhaite la garde ce jour
  const [tourDerog,setTourDerog]=useState({});   // {dateKey:{medId:true}} affecté au tour cette semaine mais ne tourne PAS ce jour
  const [tourReport,setTourReport]=useState(null); // rapport persistant de la dernière répartition auto du tour
  const [astReport,setAstReport]=useState(null);
  const [salleReg,setSalleReg]=useState([]); // registre central des salles [{n:"Angio-1",s:"ANGIO"},...]
  const [salleEdit,setSalleEdit]=useState(null); // salle en cours d'édition (activités associées)
  const [archPlan,setArchPlan]=useState({});   // cases archivées chargées pour consultation (lecture)
  const archFetched=useRef({});                // mois d'archives déjà demandés   // rapport persistant de la dernière répartition auto des astreintes
  const [periodCfg,setPeriodCfg]=useState({len:4,startM:6});
  PCFG.len=periodCfg.len;PCFG.startM=periodCfg.startM; // config répartition par période {perKey:{weeks,excl,p2hc,p2usic,mins}}
  const [astreinte,setAstreinte]=useState({}); // {wKey: medId}
  const [astDayModal,setAstDayModal]=useState(null); // legacy
  const [astPickModal,setAstPickModal]=useState(null); // {dayKey,wKey,isWeek,label}
  const [astSearch,setAstSearch]=useState("");
  const [ast4M,setAst4M]=useState(false);
  // Get astreinte medId for a given day
  const getAstreinteForDay=React.useCallback((y,m,d)=>{
    const dayKey=y+"-"+m+"-"+d;
    const v=astreinte[dayKey]!==undefined?astreinte[dayKey]:(()=>{
      const dt=new Date(y,m,d);const day=dt.getDay();const diff=day===0?-6:1-day;
      const mon=new Date(dt);mon.setDate(dt.getDate()+diff);
      const wk=mon.getFullYear()+"-"+mon.getMonth()+"-"+mon.getDate();
      return astreinte[wk];
    })();
    return(v!==undefined&&v!==null)?String(v):null;
  },[astreinte]);
  // ASTREINTE_MEDS is now dynamic from medecins.astreinte flag
  const [astYear,setAstYear]=useState(()=>new Date().getFullYear());
  const [astMonth,setAstMonth]=useState(()=>new Date().getMonth());
  const [tourYear,setTourYear]=useState(()=>new Date().getFullYear());
  const [tourMonth,setTourMonth]=useState(()=>new Date().getMonth());
  const [fbStatus,setFbStatus]=useState("connecting");
  const [vacZone,setVacZone]=useState(()=>{try{return localStorage.getItem("cp6_vaczone")||"B";}catch{return"B";}});
  const [vacDates,setVacDates]=useState(new Set()); // Set of "YYYY-MM-DD" strings
  const [vacSource,setVacSource]=useState(null); // provenance des données vacances

  // Vacances scolaires : fichier iCal officiel du ministère (l'ancienne API records a été retirée)
  // + calendrier officiel 2025-2027 embarqué en secours (arrêté du 22/10/2025, JO 23/10/2025)
  const VAC_FALLBACK={
    A:[["2025-10-18","2025-11-03"],["2025-12-20","2026-01-05"],["2026-02-07","2026-02-23"],["2026-04-04","2026-04-20"],["2026-05-14","2026-05-18"],["2026-07-04","2026-09-01"],["2026-10-17","2026-11-02"],["2026-12-19","2027-01-04"],["2027-02-13","2027-03-01"],["2027-04-10","2027-04-26"],["2027-05-06","2027-05-10"],["2027-07-03","2027-09-01"]],
    B:[["2025-10-18","2025-11-03"],["2025-12-20","2026-01-05"],["2026-02-14","2026-03-02"],["2026-04-11","2026-04-27"],["2026-05-14","2026-05-18"],["2026-07-04","2026-09-01"],["2026-10-17","2026-11-02"],["2026-12-19","2027-01-04"],["2027-02-20","2027-03-08"],["2027-04-17","2027-05-03"],["2027-05-06","2027-05-10"],["2027-07-03","2027-09-01"]],
    C:[["2025-10-18","2025-11-03"],["2025-12-20","2026-01-05"],["2026-02-21","2026-03-09"],["2026-04-18","2026-05-04"],["2026-05-14","2026-05-18"],["2026-07-04","2026-09-01"],["2026-10-17","2026-11-02"],["2026-12-19","2027-01-04"],["2027-02-06","2027-02-22"],["2027-04-03","2027-04-19"],["2027-05-06","2027-05-10"],["2027-07-03","2027-09-01"]]
  };
  const vacFromFallback=(zone)=>{
    const dates=new Set();
    const fmt=(y,m,d)=>y+"-"+String(m).padStart(2,"0")+"-"+String(d).padStart(2,"0");
    (VAC_FALLBACK[zone]||VAC_FALLBACK.B).forEach(([s,e])=>{
      const[sy2,sm2,sd2]=s.split("-").map(Number);
      const[ey2,em2,ed2]=e.split("-").map(Number);
      const cur=new Date(sy2,sm2-1,sd2),end=new Date(ey2,em2-1,ed2);
      while(cur<end){dates.add(fmt(cur.getFullYear(),cur.getMonth()+1,cur.getDate()));cur.setDate(cur.getDate()+1);}
    });
    return dates;
  };
  useEffect(()=>{
    const yr=new Date().getFullYear();
    const icsUrl="https://fr.ftp.opendatasoft.com/openscol/fr-en-calendrier-scolaire/Zone-"+vacZone+".ics";
    const proxies=[
      icsUrl,
      "https://api.allorigins.win/raw?url="+encodeURIComponent(icsUrl),
      "https://api.codetabs.com/v1/proxy?quest="+encodeURIComponent(icsUrl),
      "https://corsproxy.io/?url="+encodeURIComponent(icsUrl)
    ];
    const parseIcs=(txt)=>{
      const dates=new Set();
      const fmt=(y,m,d)=>y+"-"+String(m).padStart(2,"0")+"-"+String(d).padStart(2,"0");
      const events=txt.split("BEGIN:VEVENT").slice(1);
      events.forEach(ev=>{
        const ms=ev.match(/DTSTART[^:]*:(\d{4})(\d{2})(\d{2})/);
        const me=ev.match(/DTEND[^:]*:(\d{4})(\d{2})(\d{2})/);
        if(!ms||!me)return;
        const sy2=+ms[1];
        if(sy2<yr-1||sy2>yr+1)return;
        const cur=new Date(+ms[1],+ms[2]-1,+ms[3]);
        const end=new Date(+me[1],+me[2]-1,+me[3]); // DTEND exclusif (norme iCal)
        while(cur<end){
          dates.add(fmt(cur.getFullYear(),cur.getMonth()+1,cur.getDate()));
          cur.setDate(cur.getDate()+1);
        }
      });
      return dates;
    };
    const srcLabels=["iCal officiel (direct)","iCal officiel (via proxy AllOrigins)","iCal officiel (via proxy CodeTabs)","iCal officiel (via proxy CorsProxy)"];
    const tryFetch=(i)=>{
      if(i>=proxies.length){
        // Toutes les sources réseau ont échoué : calendrier officiel embarqué
        setVacDates(vacFromFallback(vacZone));
        setVacSource("calendrier intégré à l'application (hors ligne)");
        return;
      }
      fetch(proxies[i])
        .then(r=>{if(!r.ok)throw new Error("http "+r.status);return r.text();})
        .then(txt=>{
          const dates=parseIcs(txt||"");
          if(dates.size>0){setVacDates(dates);setVacSource(srcLabels[i]);}
          else tryFetch(i+1);
        })
        .catch(()=>tryFetch(i+1));
    };
    tryFetch(0);
  },[vacZone]);

  const isVac=(y,m,d)=>vacDates.has(`${y}-${String(m+1).padStart(2,"0")}-${String(d).padStart(2,"0")}`);
  const isFirstLoad=useRef(true);
  const localChange=useRef(false);

  useEffect(()=>{
    if(!PLANNING_DOC||!onSnapshot){setFbStatus("offline");return;}
    setFbStatus("connecting");
    const unsub=onSnapshot(PLANNING_DOC,
      (snap)=>{
        if(snap.exists){
          const data=snap.data();
          if(isFirstLoad.current||!localChange.current){
            if(data.plan)setPlan(JSON.parse(data.plan));
            if(data.tourMed)setTourMed(JSON.parse(data.tourMed));
            if(data.planningType)setPlanningType(JSON.parse(data.planningType));
            if(data.notes)setNotes(JSON.parse(data.notes));
            if(data.medecins)setMedecins(JSON.parse(data.medecins));
            if(data.actes){
            const arrA=JSON.parse(data.actes);
            arrA.forEach(a=>{if(a&&a.id==="BIP"&&a.recapSite===undefined&&!(a.recapSites&&a.recapSites.length))a.recapSites=["CHB"];});
            if(!arrA.some(a=>a&&a.id==="TP"))arrA.push({id:"TP",label:"Temps partiel",short:"TP",color:"#8b949e",bg:"#8b949e",hasSalle:false,salles:[]});
            setActes(arrA);
          }
            if(data.editPin)setEditPin(data.editPin);
          if(data.astreinte){
            const raw=JSON.parse(data.astreinte);
            // Convert all values to strings (medecin IDs may be numeric)
            const cleaned={};
            Object.entries(raw).forEach(([k,v])=>{if(v!==null&&v!==undefined&&v!=="")cleaned[k]=String(v);});
            setAstreinte(cleaned);
          }
          if(data.tourMins)setTourMins(JSON.parse(data.tourMins));
          if(data.tourMinsHard)setTourMinsHard(JSON.parse(data.tourMinsHard));
          if(data.tourCfg)setTourCfg(JSON.parse(data.tourCfg));
          if(data.tourAvoid)setTourAvoid(JSON.parse(data.tourAvoid));
          if(data.tourWish)setTourWish(JSON.parse(data.tourWish));
          if(data.gardeAvoid)setGardeAvoid(JSON.parse(data.gardeAvoid));
          if(data.gardeWish)setGardeWish(JSON.parse(data.gardeWish));
          if(data.tourDerog)setTourDerog(JSON.parse(data.tourDerog));
          if(data.tourReport!==undefined&&data.tourReport!=="")setTourReport(data.tourReport);
          if(data.astReport!==undefined&&data.astReport!=="")setAstReport(data.astReport);
          if(data.salleReg&&JSON.parse(data.salleReg).length>0){setSalleReg(JSON.parse(data.salleReg));}
          else{
            const acts=data.actes?JSON.parse(data.actes):[];
            const found=acts.flatMap(a=>a.salles||[]).filter((s,i2,arr)=>arr.indexOf(s)===i2);
            const guess=(s)=>s.indexOf("Angio")===0?"ANGIO":(s.indexOf("CHB")===0||/B[eé]thune/i.test(s))?"CHB":(/Stim|EEP|Echo|ETO|Dobu/i.test(s)&&s.indexOf("CHL")!==0)?"PLATEAU":"CHL";
            if(found.length>0)setSalleReg(found.map(s=>({n:s,s:guess(s)})));
          }
          if(data.periodCfg)setPeriodCfg(JSON.parse(data.periodCfg));
          if(data.medPins)setMedPins(JSON.parse(data.medPins));
          }
          isFirstLoad.current=false;
          localChange.current=false;
        }else{isFirstLoad.current=false;}
        setFbStatus("ok");
      },
      (err)=>{console.error("Firebase:",err);setFbStatus("error");}
    );
    return()=>unsub();
  },[]);

  /* ── Sauvegardes automatiques (72h, 10 conservées) ── */
  const [backupList,setBackupList]=useState([]); // [{id,ts}]
  const refreshBackupList=useCallback(async()=>{
    try{
      const snap=await window.firebaseDB.collection("backups").get();
      const items=[];snap.forEach(d=>items.push({id:d.id,ts:(d.data()||{})._ts||0}));
      items.sort((a,b)=>b.ts-a.ts);
      setBackupList(items);
      return items;
    }catch(e){console.log("backup list:",e);return [];}
  },[]);
  const makeBackup=useCallback(async(manual)=>{
    try{
      const cur=(await window.firebaseDB.collection("planning").doc("main").get()).data()||{};
      const ts=Date.now();
      const payload={...cur,_ts:ts};
      await window.firebaseDB.collection("backups").doc("b"+ts).set(payload);
      await window.firebaseDB.collection("planning").doc("main").set({_lastBackupAt:ts},{merge:true});
      // Purge au-delà de 10
      const items=await refreshBackupList();
      for(const it of items.slice(10)){
        await window.firebaseDB.collection("backups").doc(it.id).delete();
      }
      await refreshBackupList();
      if(manual)toast("Sauvegarde créée","info");
      return true;
    }catch(e){console.log("backup:",e);if(manual)toast("Échec de la sauvegarde","warn");return false;}
  },[refreshBackupList]);
  const [bkPreview,setBkPreview]=useState(null); // {ts, stats}
  const statsOf=(planObj,tourObj,medsArr)=>{
    let nEntries=0,nGardes=0;const byMonth={};
    Object.keys(planObj||{}).forEach(k=>{
      const dm2=planObj[k]||{};
      const n=Object.keys(dm2).length;
      nEntries+=n;
      const mKey=k.slice(0,7); // "2026-07"
      byMonth[mKey]=(byMonth[mKey]||0)+n;
      Object.keys(dm2).forEach(mid=>{
        const e=Array.isArray(dm2[mid])?dm2[mid][0]:dm2[mid];
        if(e&&e.acteId==="GARDE")nGardes++;
      });
    });
    const nTourW=Object.keys(tourObj||{}).filter(k=>{
      const w=tourObj[k]||{};return ((w.HC||[]).length+(w.USIC||[]).length)>0;
    }).length;
    return {nEntries,nGardes,nTourW,nMeds:(medsArr||[]).length,byMonth};
  };
  const previewBackup=useCallback(async(id,ts)=>{
    try{
      const snap=await window.firebaseDB.collection("backups").doc(id).get();
      const d=snap.data()||{};
      const bPlan=d.plan?JSON.parse(d.plan):{};
      const bTour=d.tourMed?JSON.parse(d.tourMed):{};
      const bMeds=d.medecins?JSON.parse(d.medecins):[];
      const sB=statsOf(bPlan,bTour,bMeds);
      const sC=statsOf(plan,tourMed,medecins);
      // diff cellule à cellule
      let added=0,removed=0,changed=0;
      const allK=new Set([...Object.keys(bPlan),...Object.keys(plan)]);
      allK.forEach(k=>{
        const a=bPlan[k]||{},c2=plan[k]||{};
        const mids=new Set([...Object.keys(a),...Object.keys(c2)]);
        mids.forEach(mid=>{
          const ja=JSON.stringify(a[mid]||null),jc=JSON.stringify(c2[mid]||null);
          if(ja===jc)return;
          if(a[mid]&&!c2[mid])removed++;      // présent dans la sauvegarde, absent aujourd'hui (serait ré-ajouté)
          else if(!a[mid]&&c2[mid])added++;   // ajouté depuis (serait perdu)
          else changed++;
        });
      });
      setBkPreview({id,ts,b:sB,c:sC,added,removed,changed});
    }catch(e){toast("Impossible de charger l'aperçu","warn");}
  },[plan,tourMed,medecins]);
  const [docSize,setDocSize]=useState(null);
  const [archivedList,setArchivedList]=useState([]);
  const refreshArchList=useCallback(async()=>{
    try{
      const snap=await window.firebaseDB.collection("archives").get();
      const ids=[];snap.forEach(d2=>{if(d2.id&&d2.id.indexOf("arch-")===0)ids.push(d2.id.slice(5));});
      ids.sort();setArchivedList(ids);return ids;
    }catch(e){return [];}
  },[]);
  useEffect(()=>{
    if(tab!=="partage")return;
    refreshBackupList();
    refreshArchList();
    (async()=>{
      try{
        const d=(await window.firebaseDB.collection("planning").doc("main").get()).data()||{};
        let bytes=0;
        Object.keys(d).forEach(k=>{
          const v=d[k];
          const s=typeof v==="string"?v:JSON.stringify(v);
          bytes+=new Blob([k]).size+new Blob([s||""]).size+2;
        });
        setDocSize(bytes);
      }catch(e){setDocSize(null);}
    })();
  },[tab]);
  const restoreBackup=useCallback(async(id)=>{
    try{
      const d=await window.firebaseDB.collection("backups").doc(id).get();
      const data=d.data();
      if(!data){toast("Sauvegarde introuvable","warn");return;}
      const{_ts,...rest}=data;
      await window.firebaseDB.collection("planning").doc("main").set(rest,{merge:true});
      toast("Sauvegarde restaurée — rechargez la page si besoin","info");
    }catch(e){console.log("restore:",e);toast("Échec de la restauration","warn");}
  },[]);
  useEffect(()=>{
    // Au chargement : backup auto si la dernière date de plus de 72 h
    const t=setTimeout(async()=>{
      try{
        const d=await window.firebaseDB.collection("planning").doc("main").get();
        const last=(d.data()||{})._lastBackupAt||0;
        if(Date.now()-last>72*3600*1000)await makeBackup(false);
        else refreshBackupList();
      }catch(e){console.log("backup check:",e);}
    },6000);
    return ()=>clearTimeout(t);
  },[]);

/* ── Purge des dérogations et remplacements Tour d'une liste de semaines ── */
  const purgeTourExtras=useCallback((weekKeys)=>{
    const allDates=[];
    weekKeys.forEach(wk2=>{
      const[py,pm,pd]=wk2.split("-").map(Number);
      for(let i2=0;i2<5;i2++){
        const dt=new Date(py,pm,pd+i2);
        allDates.push([dt.getFullYear(),dt.getMonth(),dt.getDate()]);
      }
    });
    setTourDerog(p=>{
      const n={...p};
      allDates.forEach(([dy,dm3,dd])=>{delete n[dKey(dy,dm3,dd)];});
      return n;
    });
    setPlan(p=>{
      let next={...p};
      allDates.forEach(([dy,dm3,dd])=>{
        ["M","AM"].forEach(sl=>{
          const k=sk(dy,dm3,dd,sl);
          if(!next[k])return;
          const dm2={...next[k]};let ch=false;
          Object.keys(dm2).forEach(mid=>{
            const e=Array.isArray(dm2[mid])?dm2[mid][0]:dm2[mid];
            if(e&&(e.acteId==="TOUR_HC"||e.acteId==="TOUR_USIC")){delete dm2[mid];ch=true;}
          });
          if(ch)next[k]=dm2;
        });
      });
      return next;
    });
  },[]);

  /* ── Cohérence planning ↔ tour : retrait/réapplication à l'assignation ── */
  const clearWeekActivities=useCallback((pairs)=>{
    // pairs: [{medId,weekKey}] — retire les activités (dont TP) des nouveaux tourneurs, garde abs/gardes/formations
    const PROT2=["ABSENCE","GARDE","REPOS_GARDE","FORM","FORMATION"];
    setPlan(p=>{
      let next={...p};
      pairs.forEach(({medId,weekKey})=>{
        const[wy2,wm2,wd2]=weekKey.split("-").map(Number);
        for(let i=0;i<5;i++){
          const dt=new Date(wy2,wm2,wd2+i);
          const dy=dt.getFullYear(),dm3=dt.getMonth(),dd=dt.getDate();
          if(isWE(dy,dm3,dd))continue;
          ["M","AM"].forEach(sl=>{
            const k=sk(dy,dm3,dd,sl);
            if(!next[k]||!next[k][medId])return;
            const e=next[k][medId];
            const a=Array.isArray(e)?(e[0]&&e[0].acteId):(e&&e.acteId);
            if(PROT2.includes(a))return;
            const dm2={...next[k]};delete dm2[medId];next[k]=dm2;
          });
        }
      });
      return next;
    });
  },[]);
  const reapplyPTWeek=useCallback((medId,weekKey)=>{
    const med=medecins.find(m=>m.id===medId);if(!med)return;
    const pt=planningType[medId];
    const PROT2=["ABSENCE","GARDE","REPOS_GARDE","FORM","FORMATION","TOUR_HC","TOUR_USIC"];
    const[wy2,wm2,wd2]=weekKey.split("-").map(Number);
    setPlan(p=>{
      let next={...p};
      for(let i=0;i<5;i++){
        const dt=new Date(wy2,wm2,wd2+i);
        const dy=dt.getFullYear(),dm3=dt.getMonth(),dd=dt.getDate();
        if(isWE(dy,dm3,dd))continue;
        const dw2=dow(dy,dm3,dd);
        const isOff=med.partTime&&(med.workDays||{})[String(dw2)]===false;
        ["M","AM"].forEach(sl=>{
          const k=sk(dy,dm3,dd,sl);
          const ex=(next[k]||{})[medId];
          const exA=Array.isArray(ex)?(ex[0]&&ex[0].acteId):(ex&&ex.acteId);
          if(PROT2.includes(exA))return;
          if(isOff){
            if(!next[k])next[k]={};
            next[k]={...next[k],[medId]:{acteId:"TP",salle:null}};
            return;
          }
          if(!pt||!pt[dw2])return;
          const[acteId,salle]=(pt[dw2][sl])||[null,null];
          if(!acteId)return;
          if(!next[k])next[k]={};
          next[k]={...next[k],[medId]:{acteId,salle:salle||null}};
        });
      }
      return next;
    });
  },[medecins,planningType]);

  /* ── Temps partiel & USIC : dérogation + TP + junior remplaçant ── */
  const applyTPForWeek=useCallback((medId,weekKeyOrList)=>{
    const med=medecins.find(m=>m.id===medId);
    if(!med||!med.partTime)return;
    const offDows=[1,2,3,4,5].filter(dw2=>(med.workDays||{})[String(dw2)]===false);
    if(offDows.length===0)return;
    const weekList=Array.isArray(weekKeyOrList)?weekKeyOrList:[weekKeyOrList];
    const juniors=medecins.filter(m=>m.statut==="junior"&&m.tourMed&&m.id!==medId);
    // compteur de remplacements existants (entrées plan TOUR_USIC réelles) par junior — partagé entre toutes les semaines traitées
    const replCount={};juniors.forEach(j=>{replCount[j.id]=0;});
    Object.keys(plan).forEach(k=>{
      const dm2=plan[k]||{};
      juniors.forEach(j=>{
        const e=Array.isArray(dm2[j.id])?dm2[j.id][0]:dm2[j.id];
        if(e&&e.acteId==="TOUR_USIC")replCount[j.id]++;
      });
    });
    const newDerog={},planPatch={},choices=[];
    weekList.forEach(weekKey=>{
    const[wy2,wm2,wd2]=weekKey.split("-").map(Number);
    offDows.forEach(dw2=>{
      const dt=new Date(wy2,wm2,wd2+(dw2-1));
      const dy=dt.getFullYear(),dm3=dt.getMonth(),dd=dt.getDate();
      const dk2=dKey(dy,dm3,dd);
      newDerog[dk2]=medId;
      ["M","AM"].forEach(sl=>{planPatch[sk(dy,dm3,dd,sl)]=planPatch[sk(dy,dm3,dd,sl)]||{};planPatch[sk(dy,dm3,dd,sl)][medId]={acteId:"TP",salle:null};});
      // junior dispo ce jour : pas absent, pas déjà tourneur cette semaine
      const wmW=tourMed[weekKey]||{HC:[],USIC:[]};
      const busyIds=[...(wmW.HC||[]),...(wmW.USIC||[])];
      const avail=juniors.filter(j=>{
        if(busyIds.includes(j.id))return false;
        const es=[...(["M","AM"].map(sl=>{const e=(plan[sk(dy,dm3,dd,sl)]||{})[j.id];return Array.isArray(e)?(e[0]&&e[0].acteId):(e&&e.acteId);}))];
        return !es.some(a=>["ABSENCE","FORM","FORMATION","GARDE","REPOS_GARDE"].includes(a));
      });
      const shuffled=avail.map(j=>({j,r:Math.random()})).sort((a,b)=>a.r-b.r).map(x=>x.j);
      shuffled.sort((a,b)=>replCount[a.id]-replCount[b.id]);
      const jr=shuffled[0];
      if(jr){
        replCount[jr.id]++;
        ["M","AM"].forEach(sl=>{planPatch[sk(dy,dm3,dd,sl)]=planPatch[sk(dy,dm3,dd,sl)]||{};planPatch[sk(dy,dm3,dd,sl)][jr.id]={acteId:"TOUR_USIC",salle:null};});
        choices.push(jr.init+" remplace "+med.init+" ("+JOURSC[dt.getDay()]+" "+dd+" "+MOIS[dm3].slice(0,4)+(MOIS[dm3].length>4?".":"")+")");
      }else{
        choices.push("⚠ aucun junior dispo pour remplacer "+med.init+" ("+JOURSC[dt.getDay()]+" "+dd+" "+MOIS[dm3].slice(0,4)+(MOIS[dm3].length>4?".":"")+")");
      }
    });
    });
    setTourDerog(p=>{
      const n={...p};
      Object.keys(newDerog).forEach(dk2=>{n[dk2]={...(n[dk2]||{}),[newDerog[dk2]]:true};});
      return n;
    });
    setPlan(p=>{
      let next={...p};
      Object.keys(planPatch).forEach(k=>{next[k]={...(next[k]||{}),...planPatch[k]};});
      return next;
    });
    if(choices.length>0)toast("Temps partiel USIC : "+choices.join(" · "),"info");
  },[medecins,plan,tourMed]);
  const cleanTPForWeek=useCallback((medId,weekKey)=>{
    const med=medecins.find(m=>m.id===medId);
    if(!med||!med.partTime)return;
    const offDows=[1,2,3,4,5].filter(dw2=>(med.workDays||{})[String(dw2)]===false);
    if(offDows.length===0)return;
    const[wy2,wm2,wd2]=weekKey.split("-").map(Number);
    const dks=[],sks=[];
    offDows.forEach(dw2=>{
      const dt=new Date(wy2,wm2,wd2+(dw2-1));
      const dy=dt.getFullYear(),dm3=dt.getMonth(),dd=dt.getDate();
      dks.push(dKey(dy,dm3,dd));
      ["M","AM"].forEach(sl=>sks.push(sk(dy,dm3,dd,sl)));
    });
    setTourDerog(p=>{
      const n={...p};
      dks.forEach(dk2=>{if(n[dk2]&&n[dk2][medId]){const o={...n[dk2]};delete o[medId];if(Object.keys(o).length===0)delete n[dk2];else n[dk2]=o;}});
      return n;
    });
    setPlan(p=>{
      let next={...p};
      sks.forEach(k=>{
        if(!next[k])return;
        const dm2={...next[k]};let ch=false;
        // retirer le TP du médecin + les remplacements junior TOUR_USIC posés ce jour
        const eM=Array.isArray(dm2[medId])?dm2[medId][0]:dm2[medId];
        if(eM&&eM.acteId==="TP"){delete dm2[medId];ch=true;}
        Object.keys(dm2).forEach(mid=>{
          const e=Array.isArray(dm2[mid])?dm2[mid][0]:dm2[mid];
          if(e&&e.acteId==="TOUR_USIC"){delete dm2[mid];ch=true;}
        });
        if(ch)next[k]=dm2;
      });
      return next;
    });
  },[medecins]);

    const saveToFirebase=useCallback(async(data)=>{
    if(!PLANNING_DOC||!setDoc)return;
    try{localChange.current=true;await setDoc(PLANNING_DOC,data,{merge:true});}
    catch(err){console.error("Save:",err);setFbStatus("error");}
  },[]);

  useEffect(()=>{if(!isFirstLoad.current)saveToFirebase({plan:JSON.stringify(plan)});},[plan]);
  useEffect(()=>{if(!isFirstLoad.current)saveToFirebase({tourMed:JSON.stringify(tourMed)});},[tourMed]);
  useEffect(()=>{if(!isFirstLoad.current)saveToFirebase({tourMins:JSON.stringify(tourMins)});},[tourMins]);
  useEffect(()=>{if(!isFirstLoad.current)saveToFirebase({tourMinsHard:JSON.stringify(tourMinsHard)});},[tourMinsHard]);
  useEffect(()=>{if(!isFirstLoad.current)saveToFirebase({tourCfg:JSON.stringify(tourCfg)});},[tourCfg]);
  useEffect(()=>{if(!isFirstLoad.current)saveToFirebase({tourAvoid:JSON.stringify(tourAvoid)});},[tourAvoid]);
  useEffect(()=>{if(!isFirstLoad.current)saveToFirebase({tourWish:JSON.stringify(tourWish)});},[tourWish]);
  useEffect(()=>{if(!isFirstLoad.current)saveToFirebase({gardeAvoid:JSON.stringify(gardeAvoid)});},[gardeAvoid]);
  useEffect(()=>{if(!isFirstLoad.current)saveToFirebase({gardeWish:JSON.stringify(gardeWish)});},[gardeWish]);
  useEffect(()=>{if(!isFirstLoad.current)saveToFirebase({tourDerog:JSON.stringify(tourDerog)});},[tourDerog]);
  useEffect(()=>{if(!isFirstLoad.current)saveToFirebase({tourReport:tourReport||""});},[tourReport]);
  useEffect(()=>{if(!isFirstLoad.current)saveToFirebase({astReport:astReport||""});},[astReport]);
  useEffect(()=>{if(!isFirstLoad.current)saveToFirebase({salleReg:JSON.stringify(salleReg)});},[salleReg]);
  // Consultation des archives : charge les mois archivés de la période affichée
  useEffect(()=>{
    const {sy,sm}=perStart(year,month);
    const wanted=[];
    for(let mi=0;mi<PCFG.len;mi++){
      const m2=(sm+mi)%12,y2=sm+mi>11?sy+1:sy;
      const mk=y2+"-"+String(m2+1).padStart(2,"0");
      const hasLive=Object.keys(plan).some(k=>k.indexOf(mk)===0);
      if(!hasLive&&!archFetched.current[mk])wanted.push(mk);
    }
    if(wanted.length===0)return;
    wanted.forEach(async(mk)=>{
      archFetched.current[mk]=true;
      try{
        const snap=await window.firebaseDB.collection("archives").doc("arch-"+mk).get();
        const d=snap&&snap.data&&snap.data();
        if(d&&d.plan){const frag=JSON.parse(d.plan);if(Object.keys(frag).length>0)setArchPlan(p=>({...p,...frag}));}
      }catch(e){}
    });
  },[year,month,plan]);
  useEffect(()=>{if(!isFirstLoad.current)saveToFirebase({periodCfg:JSON.stringify(periodCfg)});},[periodCfg]);
  useEffect(()=>{if(!isFirstLoad.current)saveToFirebase({planningType:JSON.stringify(planningType)});},[planningType]);
  useEffect(()=>{if(!isFirstLoad.current)saveToFirebase({notes:JSON.stringify(notes)});},[notes]);
  useEffect(()=>{if(!isFirstLoad.current)saveToFirebase({medecins:JSON.stringify(medecins)});},[medecins]);
  useEffect(()=>{if(!isFirstLoad.current)saveToFirebase({actes:JSON.stringify(actes)});},[actes]);
  useEffect(()=>{if(!isFirstLoad.current)saveToFirebase({editPin});},[editPin]);
  useEffect(()=>{if(!isFirstLoad.current)saveToFirebase({astreinte:JSON.stringify(astreinte)});},[astreinte]);
  useEffect(()=>{if(!isFirstLoad.current)saveToFirebase({medPins:JSON.stringify(medPins)});},[medPins]);

  useEffect(()=>{ applyTheme(darkMode); },[darkMode]);
  const toast=(msg,type="ok")=>{ setNotif({msg,type}); setTimeout(()=>setNotif(null),3500); };
  const acteById=useCallback(id=>actes.find(a=>a.id===id),[actes]);
  const isEdit=accessMode==="edit";
  // ─── Undo/Redo history (edit mode) ───
  const histRef=useRef({stack:[],idx:-1,restoring:false});
  const [histVer,setHistVer]=useState(0);
  const histSnapshot=()=>({plan,tourMed,astreinte,notes,planningType});
  useEffect(()=>{
    if(isFirstLoad.current)return;
    const h=histRef.current;
    if(h.restoring){h.restoring=false;return;}
    // Truncate redo branch, push snapshot
    h.stack=h.stack.slice(0,h.idx+1);
    h.stack.push(JSON.stringify(histSnapshot()));
    if(h.stack.length>50)h.stack.shift();
    h.idx=h.stack.length-1;
    setHistVer(v=>v+1);
  },[plan,tourMed,astreinte,notes,planningType]);
  const applySnapshot=(snap)=>{
    const s=JSON.parse(snap);
    histRef.current.restoring=true;
    setPlan(s.plan);setTourMed(s.tourMed);setAstreinte(s.astreinte);
    setNotes(s.notes);setPlanningType(s.planningType);
  };
  const canUndo=histRef.current.idx>0;
  const canRedo=histRef.current.idx<histRef.current.stack.length-1;
  const doUndo=()=>{
    const h=histRef.current;
    if(h.idx<=0)return;
    h.idx--;
    applySnapshot(h.stack[h.idx]);
    setHistVer(v=>v+1);
  };
  const doRedo=()=>{
    const h=histRef.current;
    if(h.idx>=h.stack.length-1)return;
    h.idx++;
    applySnapshot(h.stack[h.idx]);
    setHistVer(v=>v+1);
  };
  const isMedEdit=accessMode==="medecinEdit";
  // Returns true if current user can edit this specific medecin's data
  const canEdit=(medId)=>isEdit||(isMedEdit&&editMedId===medId);
  const isAnyEdit=isEdit||isMedEdit;
  const nDays=dIM(year,month);
  const todayY=today.getFullYear(), todayM=today.getMonth(), todayD=today.getDate();
  const allDays=useMemo(()=>{
    const all=Array.from({length:nDays},(_,i)=>i+1);
    if(showFull) return all;
    const isCurrentMonth=year===todayY&&month===todayM;
    if(!isCurrentMonth) return all;
    return all.filter(d=>d>=todayD);
  },[nDays,showFull,year,month,todayY,todayM,todayD]);

  /* ── getEntries ── */
  // 4-month period days
  const getPeriodRange=(y,m)=>perStart(y,m);
  const allDays4=useMemo(()=>{
    const {sy,sm}=getPeriodRange(year,month);
    const days=[];
    for(let mi=0;mi<PCFG.len;mi++){
      const m2=(sm+mi)%12,y2=sm+mi>11?sy+1:sy;
      const dim=new Date(y2,m2+1,0).getDate();
      for(let d=1;d<=dim;d++) days.push({y:y2,m:m2,d,label:MOIS[m2].slice(0,3)});
    }
    return days;
  },[year,month]);


  const getEntries=useCallback((medId,y2,m2,d2,slot)=>{
    const _p=Object.keys(archPlan).length>0?{...archPlan,...plan}:plan;
    if(slot!=="JOUR"){
      const abs=(_p[sk(y2,m2,d2,"JOUR")]||{})[medId];
      if((abs&&abs.acteId)==="ABSENCE") return slot==="M"?[{...abs,_fullDay:true}]:slot==="AM"?[{_blocked:true}]:[];
    }
    if(slot==="JOUR"){const e=(_p[sk(y2,m2,d2,"JOUR")]||{})[medId];return e?(Array.isArray(e)?e:[e]):[];}
    const entries=(_p[sk(y2,m2,d2,slot)]||{})[medId];
    if(entries)return Array.isArray(entries)?entries:[entries];
    if(!isWE(y2,m2,d2)&&(slot==="M"||slot==="AM")){
      const wk=wKey(y2,m2,d2),wm=tourMed[wk]||{HC:[],USIC:[]};
      const dgS=((tourDerog||{})[dKey(y2,m2,d2)]||{})[medId];
      if(dgS===true||(dgS&&dgS[slot]))return [];
      if((wm.HC||[]).includes(medId))return [{acteId:"TOUR_HC",salle:null}];
      if((wm.USIC||[]).includes(medId))return [{acteId:"TOUR_USIC",salle:null}];
    }
    return[];
  },[plan,archPlan,tourMed]);

  const getEntry=useCallback((medId,y2,m2,d2,slot)=>getEntries(medId,y2,m2,d2,slot)[0]||null,[getEntries]);

  /* ── isMedAvailable ── */
  const isMedAvailable=useCallback((med,y2,m2,d2,slot)=>{
    const check=slot==="N"?["N","JOUR"]:slot==="JOUR"?["JOUR","M","AM"]:[slot,"JOUR"];
    const ids=[];
    check.forEach(sl=>getEntries(med.id,y2,m2,d2,sl).forEach(e=>{if((e&&e.acteId)&&!e._blocked)ids.push(e.acteId);}));
    if(ids.some(id=>["ABSENCE","FORMATION"].includes(id)))return "blocked";
    if(ids.some(id=>!["TOUR_HC","TOUR_USIC"].includes(id)))return "warning";
    return "free";
  },[getEntries]);

  /* ── setEntry / addEntry / removeEntry ── */
  const setEntry=useCallback((medId,y2,m2,d2,slot,entry)=>{
    const key=sk(y2,m2,d2,slot);
    setPlan(p=>{const dm={...(p[key]||{})};if(entry)dm[medId]=entry;else delete dm[medId];return{...p,[key]:dm};});
  },[]);

  const addEntry=useCallback((medId,y2,m2,d2,slot,entry)=>{
    const key=sk(y2,m2,d2,slot);
    setPlan(p=>{const dm={...(p[key]||{})};const ex=dm[medId];if(!ex)dm[medId]=entry;else if(Array.isArray(ex))dm[medId]=[...ex,entry];else dm[medId]=[ex,entry];return{...p,[key]:dm};});
  },[]);

  const removeEntry=useCallback((medId,y2,m2,d2,slot,acteId)=>{
    const key=sk(y2,m2,d2,slot);
    setPlan(p=>{const dm={...(p[key]||{})};const ex=dm[medId];if(!ex)return p;if(Array.isArray(ex)){const f=ex.filter(e=>e.acteId!==acteId);if(f.length===0)delete dm[medId];else dm[medId]=f.length===1?f[0]:f;}else delete dm[medId];return{...p,[key]:dm};});
  },[]);

  /* ── applyGarde (atomic) ── */
  const applyGarde=useCallback((medId,y2,m2,d2)=>{
    const dw=dow(y2,m2,d2);
    const gardeSlot=(dw===6||dw===0)?"JOUR":"N";
    const dt=new Date(y2,m2,d2+1);
    const ny=dt.getFullYear(),nm=dt.getMonth(),nd2=dt.getDate();
    setPlan(p=>{
      let next={...p};
      const gk=sk(y2,m2,d2,gardeSlot);
      const gdm={...(next[gk]||{})};
      Object.keys(gdm).forEach(mid=>{
        const e=Array.isArray(gdm[mid])?gdm[mid][0]:gdm[mid];
        if((e&&e.acteId)==="GARDE"){
          const prevId=parseInt(mid);
          const rSlots=isWE(ny,nm,nd2)?["JOUR"]:["M","AM"];
          rSlots.forEach(sl=>{const rk=sk(ny,nm,nd2,sl);const rdm={...(next[rk]||{})};if(rdm[prevId]&&rdm[prevId].acteId==="REPOS_GARDE"){delete rdm[prevId];next={...next,[rk]:rdm};}});
          delete gdm[mid];
        }
      });
      next={...next,[gk]:gdm};
      next[gk]={...next[gk],[medId]:{acteId:"GARDE",salle:null}};
      if(isWE(ny,nm,nd2)){
        const k=sk(ny,nm,nd2,"JOUR"),dm={...(next[k]||{})};
        if(!dm[medId]||dm[medId].acteId!=="ABSENCE")dm[medId]={acteId:"REPOS_GARDE",salle:null};
        next={...next,[k]:dm};
      } else {
        ["M","AM"].forEach(sl=>{const k=sk(ny,nm,nd2,sl),dm={...(next[k]||{})};if(!dm[medId]||dm[medId].acteId!=="ABSENCE")dm[medId]={acteId:"REPOS_GARDE",salle:null};next={...next,[k]:dm};});
      }
      return next;
    });
    toast("Garde + repos automatique","info");
  },[]);

  /* ── applyAbsence ── */
  const applyAbsence=useCallback(({medId,dateFrom,dateTo,slots,absType="ABSENCE"})=>{
    const [fy,fm,fd]=parseDate(dateFrom);
    const fromT=new Date(fy,fm,fd).getTime(),toT=new Date(...parseDate(dateTo)).getTime();
    setPlan(p=>{
      let next={...p};
      let cy=fy,cm=fm;
      while(new Date(cy,cm,1).getTime()<=new Date(...parseDate(dateTo)).getTime()){
        for(let d=1;d<=dIM(cy,cm);d++){
          const t=new Date(cy,cm,d).getTime();
          if(t<fromT||t>toT)continue;
          (isWE(cy,cm,d)?["JOUR"]:slots).forEach(sl=>{const k=sk(cy,cm,d,sl);const dm={...(next[k]||{})};dm[medId]={acteId:absType||"ABSENCE",salle:null};next={...next,[k]:dm};});
        }
        if(cm===11){cy++;cm=0;}else cm++;
      }
      return next;
    });
    toast(absType==="FORMATION"?"Formation appliquée":"Absence appliquée");
  },[]);

  const removeAbsence=useCallback(({medId,dateFrom,dateTo})=>{
    const [fy,fm,fd]=parseDate(dateFrom);
    const fromT=new Date(fy,fm,fd).getTime(),toT=new Date(...parseDate(dateTo)).getTime();
    setPlan(p=>{
      let next={...p};
      let cy=fy,cm=fm;
      while(new Date(cy,cm,1).getTime()<=new Date(...parseDate(dateTo)).getTime()){
        for(let d=1;d<=dIM(cy,cm);d++){
          const t=new Date(cy,cm,d).getTime();
          if(t<fromT||t>toT)continue;
          ["M","AM","JOUR","N"].forEach(sl=>{
            const k=sk(cy,cm,d,sl);
            if(!next[k]||!next[k][medId])return;
            const e=next[k][medId];
            const acteId=Array.isArray(e)?e[0]&&e[0].acteId:e&&e.acteId;
            if(acteId==="ABSENCE"||acteId==="FORMATION"){
              const dm={...next[k]};delete dm[medId];next={...next,[k]:dm};
            }
          });
        }
        if(cm===11){cy++;cm=0;}else cm++;
      }
      return next;
    });
    toast("Absence retirée");
  },[]);

  /* ── applyPlanningType ── */
  /* ── Application flexible du planning type (multi-mois, départ configurable) ── */
  const applyPTFlex=useCallback((medId,monthsList,fromToday)=>{
    const tod=new Date();tod.setHours(0,0,0,0);
    const targets=medId?medecins.filter(m=>m.id===medId):medecins;
    let nApplied=0;
    setPlan(p=>{
      let next={...p};
      monthsList.forEach(({y:ay,m:am})=>{
        const dim=new Date(ay,am+1,0).getDate();
        for(let d=1;d<=dim;d++){
          if(isWE(ay,am,d))continue;
          if(fromToday&&new Date(ay,am,d)<tod)continue;
          const dw=dow(ay,am,d);
          const wk=wKey(ay,am,d),wm=tourMed[wk]||{HC:[],USIC:[]};
          const allTm=[...(wm.HC||[]),...(wm.USIC||[])];
          targets.forEach(med=>{
            if(allTm.includes(med.id))return;
            if(med.partTime&&(med.workDays||{})[String(dw)]===false){
              ["M","AM"].forEach(sl=>{
                const k=sk(ay,am,d,sl),ex=(next[k]||{})[med.id];
                const exA=Array.isArray(ex)?(ex[0]&&ex[0].acteId):(ex&&ex.acteId);
                if(["ABSENCE","GARDE","REPOS_GARDE","TOUR_HC","TOUR_USIC"].includes(exA))return;
                if(!next[k])next[k]={};
                next[k]={...next[k],[med.id]:{acteId:"TP",salle:null}};
                nApplied++;
              });
              return;
            }
            const pt=planningType[med.id];if(!pt||!pt[dw])return;
            ["M","AM"].forEach(sl=>{
              const k=sk(ay,am,d,sl),ex=(next[k]||{})[med.id];
              const exA=Array.isArray(ex)?(ex[0]&&ex[0].acteId):(ex&&ex.acteId);
              if(["ABSENCE","GARDE","REPOS_GARDE","TOUR_HC","TOUR_USIC","TP"].includes(exA))return;
              const [acteId,salle]=(pt[dw][sl])||[null,null];if(!acteId)return;
              if(!next[k])next[k]={};
              next[k]={...next[k],[med.id]:{acteId,salle:salle||null}};
              nApplied++;
            });
          });
        }
      });
      return next;
    });
    const medLbl=medId?(medecins.find(m=>m.id===medId)||{}).init||"":"tous";
    toast("Planning type appliqué ("+medLbl+", "+monthsList.length+" mois"+(fromToday?", à partir d'aujourd'hui":"")+")","info");
  },[medecins,planningType,tourMed]);

  /* ── Modale d'application du PT ── */
  const [ptModal,setPtModal]=React.useState(null); // null | {medId:null|number}
  const [ptMonths,setPtMonths]=React.useState([]); // indices cochés
  const [ptFromToday,setPtFromToday]=React.useState(false);
  const ptPeriodMonths=React.useMemo(()=>{
    const p=perStart(year,month);const arr=[];
    for(let i=0;i<PCFG.len;i++){const mm=(p.sm+i)%12,yy=p.sm+i>11?p.sy+1:p.sy;arr.push({y:yy,m:mm});}
    return arr;
  },[year,month,PCFG.len,PCFG.startM]);
  const removePTFlex=useCallback((medId,monthsList,fromToday)=>{
    const tod=new Date();tod.setHours(0,0,0,0);
    const KEEP=["GARDE","REPOS_GARDE","TOUR_HC","TOUR_USIC","ABSENCE","FORM","FORMATION"];
    const targetIds=medId?[medId]:medecins.map(m=>m.id);
    setPlan(p=>{
      let next={...p};
      monthsList.forEach(({y:ay,m:am})=>{
        const dim=new Date(ay,am+1,0).getDate();
        for(let d=1;d<=dim;d++){
          if(fromToday&&new Date(ay,am,d)<tod)continue;
          ["M","AM","JOUR","N"].forEach(sl=>{
            const k=sk(ay,am,d,sl);
            if(!next[k])return;
            const dm={...next[k]};let changed=false;
            targetIds.forEach(mid=>{
              const e=dm[mid];if(!e)return;
              const a=Array.isArray(e)?(e[0]&&e[0].acteId):(e&&e.acteId);
              if(!KEEP.includes(a)){delete dm[mid];changed=true;}
            });
            if(changed)next[k]=dm;
          });
        }
      });
      return next;
    });
    toast("Affectations retirées ("+monthsList.length+" mois"+(fromToday?", à partir d'aujourd'hui":"")+"). Gardes, absences, formations et tour conservés.","info");
  },[medecins]);
  const openPtModal=(medId,mode)=>{
    setPtMonths(ptPeriodMonths.map((_,i)=>i)); // tous cochés par défaut
    setPtFromToday(false); // nominal : depuis le début de la période
    setPtModal({medId:medId||null,mode:mode||"apply"});
  };
  const runPtModal=()=>{
    const list=ptPeriodMonths.filter((_,i)=>ptMonths.includes(i));
    if(list.length===0){toast("Sélectionnez au moins un mois","warn");return;}
    if(ptModal.mode==="remove"){
      if(!window.confirm("Retirer toutes les affectations d'activités sur les mois sélectionnés ?"))return;
      removePTFlex(ptModal.medId,list,ptFromToday);
    }else{
      applyPTFlex(ptModal.medId,list,ptFromToday);
    }
    setPtModal(null);
  };

  const applyPlanningType=useCallback(()=>{
    setPlan(p=>{
      let next={...p};
      allDays.forEach(d=>{
        if(isWE(year,month,d))return;
        const dw=dow(year,month,d);
        const wk=wKey(year,month,d),wm=tourMed[wk]||{HC:[],USIC:[]};
        const allTm=[...(wm.HC||[]),...(wm.USIC||[])];
        medecins.forEach(med=>{
          if(allTm.includes(med.id))return;
          const pt=planningType[med.id];if(!pt||!pt[dw])return;
          ["M","AM"].forEach(sl=>{
            const k=sk(year,month,d,sl),ex=(next[k]||{})[med.id];
            const exA=Array.isArray(ex)?(ex[0]&&ex[0].acteId):(ex&&ex.acteId);
            if(["ABSENCE","GARDE","REPOS_GARDE"].includes(exA))return;
            const [acteId,salle]=(pt[dw][sl])||[null,null];if(!acteId)return;
            if(!next[k])next[k]={};
            next[k]={...next[k],[med.id]:{acteId,salle:salle||null}};
          });
        });
      });
      return next;
    });
    toast("Planning type appliqué","info");
  },[allDays,year,month,medecins,planningType,tourMed]);

  /* ── applyPlanningType for one med ── */
  const applyPlanningTypeMed=useCallback((medId)=>{
    const med=medecins.find(m=>m.id===medId);
    if(!med)return;
    setPlan(p=>{
      let next={...p};
      allDays.forEach(d=>{
        if(isWE(year,month,d))return;
        const dw=dow(year,month,d);
        const wk=wKey(year,month,d),wm=tourMed[wk]||{HC:[],USIC:[]};
        const allTm=[...(wm.HC||[]),...(wm.USIC||[])];
        if(allTm.includes(medId))return;
        const pt=planningType[medId];if(!pt||!pt[dw])return;
        ["M","AM"].forEach(sl=>{
          const k=sk(year,month,d,sl),ex=(next[k]||{})[medId];
          const exA=Array.isArray(ex)?(ex[0]&&ex[0].acteId):(ex&&ex.acteId);
          if(["ABSENCE","GARDE","REPOS_GARDE"].includes(exA))return;
          const [acteId,salle]=(pt[dw][sl])||[null,null];if(!acteId)return;
          if(!next[k])next[k]={};
          next[k]={...next[k],[medId]:{acteId,salle:salle||null}};
        });
      });
      return next;
    });
    toast(`PT appliqué pour ${med.nom}`,"info");
  },[allDays,year,month,medecins,planningType,tourMed]);

  /* ── clearPlanningType (global or individual) ── */
  const clearPlanningType=useCallback((medId=null)=>{
    setPlan(p=>{
      let next={...p};
      allDays.forEach(d=>{
        if(isWE(year,month,d))return;
        ["M","AM"].forEach(sl=>{
          const k=sk(year,month,d,sl);
          if(!next[k])return;
          const newSlot={...next[k]};
          if(medId!==null){
            // Clear only for this med (except ABSENCE/GARDE/REPOS)
            const ex=newSlot[medId];
            const exA=Array.isArray(ex)?(ex[0]&&ex[0].acteId):(ex&&ex.acteId);
            if(!["ABSENCE","GARDE","REPOS_GARDE"].includes(exA)) delete newSlot[medId];
          } else {
            // Clear all meds (except ABSENCE/GARDE/REPOS)
            Object.keys(newSlot).forEach(mid=>{
              const ex=newSlot[mid];
              const exA=Array.isArray(ex)?(ex[0]&&ex[0].acteId):(ex&&ex.acteId);
              if(!["ABSENCE","GARDE","REPOS_GARDE"].includes(exA)) delete newSlot[mid];
            });
          }
          next={...next,[k]:newSlot};
        });
      });
      return next;
    });
    toast(medId?`Planning effacé pour ${(medecins.find(m=>m.id===medId)||{nom:"?"}).nom}`:`Planning effacé pour ${MOIS[month]}`,"info");
  },[allDays,year,month,medecins]);

  /* ── salleOcc ── */
  const salleOcc=useCallback((acteId,y2,m2,d2,slot)=>{
    const res={};
    medecins.forEach(med=>{
      getEntries(med.id,y2,m2,d2,slot).forEach(e=>{
        if((e&&e.acteId)===acteId&&e.salle){if(!res[e.salle])res[e.salle]=[];if(!res[e.salle].find(x=>x.id===med.id))res[e.salle].push(med);}
      });
    });
    return res;
  },[medecins,getEntries]);

  /* ── weeks ── */
  const weeks=useMemo(()=>{
    const seen=new Set(),ws=[];
    allDays.forEach(d=>{const k=wKey(year,month,d);if(!seen.has(k)){seen.add(k);const mo=getMon(year,month,d);ws.push({key:k,label:`${mo.getDate()} ${MOIS[mo.getMonth()]}`});}});
    return ws;
  },[year,month,allDays]);

  const isAbsentInWeek=useCallback((medId,wk)=>{
    const[wy,wm2,wd]=wk.split("-").map(Number);
    return[0,1,2,3,4].some(i=>{const dt=new Date(wy,wm2,wd+i);return["M","AM","JOUR"].some(sl=>{const e=(plan[sk(dt.getFullYear(),dt.getMonth(),dt.getDate(),sl)]||{})[medId];const ae=Array.isArray(e)?e[0]:e;return ae&&ae.acteId==="ABSENCE";});});
  },[plan]);

  const tmCount=medId=>Object.values(tourMed).reduce((n,w)=>((w.HC||[]).includes(medId)||(w.USIC||[]).includes(medId))?n+1:n,0);
  const getPeriodStart=(y,m)=>{const p=perStart(y,m);return{sy:p.sy,sm:p.sm};};
  const prevM=()=>{
    const{sm,sy}=getPeriodStart(year,month);
    const p=perPrev(sy,sm);
    setYearMonth(p.sy,p.sm);
  };
  const nextM=()=>{
    const{sm,sy}=getPeriodStart(year,month);
    const p=perNext(sy,sm);
    setYearMonth(p.sy,p.sm);
  };
  const [daySwapSpan,setDaySwapSpan]=useState("J");
  const openCell=(medId,y2,m2,d2,slot)=>{
    if(!canEdit(medId))return;
    setMData({medId,y:y2,m:m2,d:d2,slot});setModal("cell");
  };

  const medPlan=medecins.filter(m=>m.role==="medecin");
  const medAttache=medecins.filter(m=>m.role==="attache");
  const filteredMeds=medPlan.filter(m=>planFilter.length===0||planFilter.includes(m.id));

  /* ── Login ── */
  // Show loading while Firebase connects (so medPins are available for login)
  if(accessMode==="ask"&&fbStatus==="connecting"&&!PLANNING_DOC) return(
    <div style={{minHeight:"100vh",background:"#1a1f2e",display:"flex",alignItems:"center",justifyContent:"center",fontFamily:"sans-serif",color:"#4ade80",fontSize:20}}>
      ♥ Chargement...
    </div>
  );

  if(accessMode==="ask") return(
    <div style={{minHeight:"100vh",background:"var(--bg)",display:"flex",alignItems:"center",justifyContent:"center",fontFamily:"'Sora',sans-serif"}}>
      <div style={{background:"var(--modal)",border:"1px solid var(--border)",borderRadius:16,padding:36,width:340,textAlign:"center",boxShadow:"0 20px 60px var(--shadow)"}}>
        <div style={{fontSize:32,marginBottom:8}}>♥</div>
        <div style={{fontWeight:800,fontSize:20,color:"var(--txt)",marginBottom:4}}>CardioPlanning</div>
        <div style={{color:"var(--txt2)",fontSize:13,marginBottom:20}}>CHL & CHB</div>
        <div style={{marginBottom:14}}>
          <label style={{display:"block",fontSize:10,color:"var(--txt3)",fontWeight:700,textTransform:"uppercase",marginBottom:5}}>Profil (optionnel)</label>
          <select value={userProfile} onChange={e=>setUserProfile(parseInt(e.target.value))} style={{...S.fi,width:"100%"}}>
            <option value={0}>— Aucun —</option>
            {MEDECINS_INIT.filter(m=>m.role==="medecin").map(m=><option key={m.id} value={m.id}>Dr. {m.prenom} {m.nom}</option>)}
          </select>
        </div>
        <button style={{width:"100%",padding:"11px",borderRadius:9,border:"1px solid var(--border)",background:"var(--bg2)",color:"var(--txt)",cursor:"pointer",fontSize:14,marginBottom:14,fontWeight:600}} onClick={()=>setAccessMode("view")}>👁 Consulter</button>
        <div style={{color:"var(--txt3)",fontSize:12,marginBottom:12,display:"flex",alignItems:"center",justifyContent:"center",gap:6}}>
          — édition —
          {fbStatus==="connecting"&&<span style={{fontSize:10,color:"#f59e0b"}}>⏳ Chargement...</span>}
          {fbStatus==="ok"&&Object.keys(medPins).length>0&&<span style={{fontSize:10,color:"#4ade80"}}>✓ {Object.keys(medPins).length} PIN(s) médecin</span>}
        </div>
        <input value={pinInput} onChange={e=>setPinInput(e.target.value)} onKeyDown={e=>{if(e.key==="Enter"){
    if(pinInput===editPin){setAccessMode("edit");setPinError(false);return;}
    const medEntry=Object.entries(medPins).find(([id,pin])=>pin===pinInput&&pin.length>=3);
    if(medEntry){setEditMedId(parseInt(medEntry[0]));setUserProfile(parseInt(medEntry[0]));setAccessMode("medecinEdit");setPinError(false);}
    else setPinError(true);
  }}}
          type="password" placeholder="PIN" style={{...S.fi,width:"100%",textAlign:"center",letterSpacing:6,fontSize:16,marginBottom:8}}/>
        {pinError&&<div style={{color:"#ef4444",fontSize:12,marginBottom:8}}>Code incorrect</div>}
        <button style={{width:"100%",padding:"10px",borderRadius:9,border:"none",background:"#1d4ed8",color:"#fff",cursor:"pointer",fontSize:14,fontWeight:700}}
          onClick={()=>{
            if(pinInput===editPin){setAccessMode("edit");setPinError(false);return;}
            // Check medecin PINs
            const medEntry=Object.entries(medPins).find(([id,pin])=>pin===pinInput&&pin.length>=3);
            if(medEntry){
              setEditMedId(parseInt(medEntry[0]));
              setUserProfile(parseInt(medEntry[0]));
              setAccessMode("medecinEdit");
              setPinError(false);
            } else {
              setPinError(true);
            }
          }}>✏️ Édition</button>
        <div style={{marginTop:14,fontSize:10,color:"var(--txt3)",textAlign:"center"}}>{APP_VERSION}</div>
      </div>
    </div>
  );

  const _per=getPeriodRange(year,month);
  const _pem=(_per.sm+PCFG.len-1)%12,_pey=_per.sm+PCFG.len-1>11?_per.sy+1:_per.sy;
  const _titlePeriod=MOIS[_per.sm]+" — "+MOIS[_pem]+" "+(_per.sy!==_pey?_per.sy+"/"+_pey:_pey);
  return(
    <div style={S.app}>
      <style>{`@import url('https://fonts.googleapis.com/css2?family=Sora:wght@400;600;700;800&family=JetBrains+Mono:wght@500;700&display=swap');
*{box-sizing:border-box;margin:0;padding:0}
::-webkit-scrollbar{width:5px;height:5px}
::-webkit-scrollbar-track{background:var(--bg)}
::-webkit-scrollbar-thumb{background:var(--border);border-radius:3px}
td{background:var(--bg2)}

nav::-webkit-scrollbar { display: none; }
header::-webkit-scrollbar { display: none; }

@media print {
  html { font-size: 90% !important; }

  /* Forcer toutes les variables CSS en mode clair */
  html, :root {
    --bg: #ffffff !important;
    --bg2: #ffffff !important;
    --bg-n: #e8edf5 !important;     /* Nuit : gris-bleu léger */
    --bg-we: #fdf5e4 !important;    /* Weekend : crème léger */
    --bg-weh: #faefd0 !important;   /* Weekend header : crème */
    --bg-td: #edfaf3 !important;    /* Aujourd'hui : vert très léger */
    --border: #cbd5e1 !important;
    --border2: #e2e8f0 !important;
    --txt: #1e293b !important;
    --txt2: #475569 !important;
    --txt3: #64748b !important;
    --th: #f1f5f9 !important;
    --td-fix: #f1f5f9 !important;
    --today-c: #15803d !important;
    --nav-act: #dcfce7 !important;
    --nav-act-c: #15803d !important;
  }

  body { background: white !important; -webkit-print-color-adjust: exact !important; print-color-adjust: exact !important; }

  /* Masquer header, nav, boutons */
  header, nav, button, .no-print { display: none !important; }

  /* Fond blanc par défaut, texte noir */
  body, div, span, p, h2, main {
    color: #1e293b !important;
    box-shadow: none !important;
  }
  body { background: white !important; }
  /* td/th utilisent les variables CSS pour garder les couleurs nuit/WE/today */
  td, th { color: #1e293b !important; box-shadow: none !important; }

  /* CONSERVER les couleurs des badges d'activité */
  div[style*="JetBrains Mono"] {
    -webkit-print-color-adjust: exact !important;
    print-color-adjust: exact !important;
  }

  /* Tableaux */
  table { width: 100% !important; page-break-inside: auto; border-collapse: collapse !important; }
  tr { page-break-inside: avoid; }
  td, th { border: 1px solid #cbd5e1 !important; }

  /* Séparateur de semaine = coupure de page */
  tr[style*="border-top: 3px"] { page-break-before: always; }

  /* Masquer scrollbars */
  div { overflow: visible !important; max-height: none !important; }

  /* Marges */
  @page { margin: 1cm; size: A4 landscape; }
}
`}</style>

      {notif&&<div style={{...S.notif,background:"var(--bg-td)",borderColor:"#4ade80"}}>{notif.msg}</div>}
      {isMedEdit&&<div style={{position:"fixed",bottom:0,left:0,right:0,background:"#1d4ed8",color:"#fff",textAlign:"center",fontSize:12,padding:"6px",zIndex:500,fontWeight:600}}>
        ✏️ Mode édition restreinte — Dr. {(medecins.find(m=>m.id===editMedId)||{nom:""}).nom} · <button onClick={()=>setAccessMode("view")} style={{background:"none",border:"1px solid rgba(255,255,255,.5)",borderRadius:4,color:"#fff",cursor:"pointer",fontSize:11,padding:"1px 7px",marginLeft:8}}>Quitter</button>
      </div>}

      {/* HEADER */}
      <header style={S.hdr}>
        <div style={{display:"flex",alignItems:"center",gap:7,flexShrink:0}}>
          <span onClick={()=>setAccessMode("ask")} title="Retour à l'accueil" style={{fontSize:20,color:"#f85149",cursor:"pointer"}}>♥</span>
          {isAnyEdit&&<div style={{display:"flex",gap:3}}>
            <button onClick={doUndo} disabled={!canUndo} title="Annuler (retour arrière)"
              style={{width:26,height:26,borderRadius:6,border:"1px solid rgba(255,255,255,.25)",background:canUndo?"rgba(255,255,255,.1)":"transparent",color:canUndo?"#f0f6fc":"#484f58",cursor:canUndo?"pointer":"default",fontSize:13,display:"flex",alignItems:"center",justifyContent:"center"}}>↶</button>
            <button onClick={doRedo} disabled={!canRedo} title="Rétablir (retour avant)"
              style={{width:26,height:26,borderRadius:6,border:"1px solid rgba(255,255,255,.25)",background:canRedo?"rgba(255,255,255,.1)":"transparent",color:canRedo?"#f0f6fc":"#484f58",cursor:canRedo?"pointer":"default",fontSize:13,display:"flex",alignItems:"center",justifyContent:"center"}}>↷</button>
          </div>}
          <div>
            <div style={{fontWeight:800,fontSize:14,color:"#f0f6fc"}}>CardioPlanning</div>
            <div style={{fontSize:8,color:"#484f58",display:"flex",alignItems:"center",gap:4}}>
              CHL & CHB{!isEdit&&<span style={{color:"#e3b341",marginLeft:5}}>👁</span>}
              <span style={{marginLeft:4,width:6,height:6,borderRadius:"50%",display:"inline-block",
                background:fbStatus==="ok"?"#4ade80":fbStatus==="error"?"#ef4444":fbStatus==="offline"?"#94a3b8":"#f59e0b"}}
                title={fbStatus==="ok"?"Firebase connecté":fbStatus==="error"?"Erreur Firebase":fbStatus==="offline"?"Mode local (CodeSandbox)":"Connexion..."}/>
            </div>
          </div>
        </div>
        <nav style={S.nav}>
          {orderedTabs.map(([v,l])=>(
            <button key={v}
              draggable
              onDragStart={()=>setDragTab(v)}
              onDragOver={e=>{e.preventDefault();}}
              onDrop={e=>{ e.preventDefault(); if(dragTab&&dragTab!==v){ setTabOrder(p=>{ const a=[...p],fi=a.indexOf(dragTab),ti=a.indexOf(v); a.splice(fi,1); a.splice(ti,0,dragTab); return a; }); } setDragTab(null); }}
              onClick={()=>setTab(v)}
              style={{...S.nb,...(tab===v?S.nba:{}),cursor:"grab",userSelect:"none"}}>{l}</button>
          ))}
        </nav>
      {Object.keys(archPlan).length>0&&(()=>{
        const {sy,sm}=perStart(year,month);
        const shown=[];
        for(let mi=0;mi<PCFG.len;mi++){const m2=(sm+mi)%12,y2=sm+mi>11?sy+1:sy;const mk=y2+"-"+String(m2+1).padStart(2,"0");if(Object.keys(archPlan).some(k=>k.indexOf(mk)===0)&&!Object.keys(plan).some(k=>k.indexOf(mk)===0))shown.push(MOIS[m2]+" "+y2);}
        return shown.length>0?<div style={{padding:"4px 12px",fontSize:10,fontWeight:700,color:"#7c3aed",background:"rgba(124,58,237,.08)",borderBottom:"1px solid var(--border)"}}>🗄 Données archivées affichées ({shown.join(", ")}) — consultation : les modifications iraient dans les données actives.</div>:null;
      })()}

      </header>

      <main style={S.main}>

      {/* MON PLANNING */}
      

      {/* PLANNING */}
      {tab==="planning"&&(
        <div>
          <div style={S.bar}>
            <div style={{display:"flex",alignItems:"center",gap:8}}>
              <button onClick={prevM} style={S.arr}>‹</button>
              <h2 style={S.mTit}>{"📅 "+_titlePeriod}</h2>
              <button onClick={nextM} style={S.arr}>›</button>
            </div>
            <div style={{display:"flex",gap:4,alignItems:"center",marginLeft:"auto"}}>
              <button onClick={()=>setDarkMode(d=>!d)} style={{...S.arr,fontSize:13,width:30}}>{darkMode?"☀️":"🌓"}</button>
              <button onClick={()=>setShowFull(f=>!f)} title={showFull?"Depuis aujourd'hui":"Mois complet"} style={{...S.arr,fontSize:16,width:32,color:showFull?"var(--today-c)":"var(--txt2)",border:`1px solid ${showFull?"var(--today-c)":"var(--border)"}`}}>{showFull?"📅":"🗓️"}</button>
            </div>
          </div>
          {isAnyEdit&&<div style={{display:"flex",gap:6,alignItems:"center",marginBottom:8}}>
            <button style={{fontSize:11,padding:"3px 12px",borderRadius:6,border:"1.5px solid #388bfd",background:"rgba(56,139,253,.10)",color:"#388bfd",fontWeight:800,cursor:"pointer"}} onClick={()=>openPtModal(null)}>📋 Planning type</button>
          </div>}
          <div style={{display:"flex",flexWrap:"wrap",gap:4,marginBottom:8,alignItems:"center"}}>
            <span style={{fontSize:10,color:"var(--txt3)",fontWeight:700,textTransform:"uppercase",marginRight:4}}>Filtre:</span>
            <button onClick={()=>setPlanFilter([])} style={{padding:"2px 8px",borderRadius:10,border:"1px solid var(--border)",background:planFilter.length===0?"#1d4ed8":"var(--bg2)",color:planFilter.length===0?"#fff":"var(--txt2)",fontSize:11,cursor:"pointer",fontWeight:600}}>Tous</button>
            {medPlan.map(m=>{const on=planFilter.includes(m.id);return <button key={m.id} onClick={()=>setPlanFilter(p=>on?p.filter(x=>x!==m.id):[...p,m.id])} style={{padding:"2px 7px",borderRadius:10,border:`1px solid ${on?m.color:"var(--border)"}`,background:on?m.color:"var(--bg2)",color:on?"#fff":"var(--txt2)",fontSize:11,cursor:"pointer",fontWeight:on?700:400}}>{m.init}</button>;})}
          </div>
          {orient==="H"
            ?<GridH allDays={allDays} year={year} month={month} meds={filteredMeds} getEntries={getEntries} acteById={acteById} onCell={openCell} isEdit={isAnyEdit} notes={notes} isVac={isVac} applyGarde={applyGarde} allMeds={medecins} viewPeriod={viewPeriod} allDays4={allDays4} showFull={showFull} getAstreinteForDay={getAstreinteForDay}/>
            :<GridV allDays={allDays} year={year} month={month} meds={filteredMeds} getEntries={getEntries} acteById={acteById} onCell={openCell} isEdit={isAnyEdit} notes={notes} isVac={isVac} applyGarde={applyGarde} allMeds={medecins} viewPeriod={viewPeriod} allDays4={allDays4} showFull={showFull} getAstreinteForDay={getAstreinteForDay}/>}
        </div>
      )}

      {/* TOUR MÉDICAL */}
      {tab==="tourmedical"&&<TourTab tourMins={tourMins} tourMinsHard={tourMinsHard} tourAvoid={tourAvoid} tourWish={tourWish} applyTPForWeek={applyTPForWeek} cleanTPForWeek={cleanTPForWeek} clearWeekActivities={clearWeekActivities} reapplyPTWeek={reapplyPTWeek} purgeTourExtras={purgeTourExtras} plan={plan} tourDerog={tourDerog} lastReport={tourReport} setLastReport={setTourReport} tourCfg={tourCfg} setTourCfg={setTourCfg} year={tourYear} month={tourMonth} setYear={setTourYear} setMonth={setTourMonth} tourMed={tourMed} setTourMed={setTourMed} medecins={medecins} getEntries={getEntries} isEdit={isEdit} darkMode={darkMode} setDarkMode={setDarkMode} planningType={planningType} setPlan={setPlan} allDays={allDays} toast={toast}/>}

      {tab==="chl"&&<SiteView site="CHL" salleReg={salleReg} year={year} month={month} prevM={prevM} nextM={nextM} actes={actes} medecins={medecins} getEntries={getEntries} salleOcc={salleOcc} allDays={allDays} isEdit={isEdit} orient={orient} setOrient={setOrient} notes={notes}
        onPickSite={({salle,siteActes,d,sl,y,m})=>{setMData({salle,siteActes,d,sl,y,m});setModal("pickMedSite");}}
        darkMode={darkMode} setDarkMode={setDarkMode} showFull={showFull} setShowFull={setShowFull} viewPeriod={viewPeriod} allDays4={allDays4} setViewPeriod={setViewPeriod}/>}

      {tab==="chb"&&<SiteView site="CHB" salleReg={salleReg} year={year} month={month} prevM={prevM} nextM={nextM} actes={actes} medecins={medecins} getEntries={getEntries} salleOcc={salleOcc} allDays={allDays} isEdit={isEdit} showFull={showFull} setShowFull={setShowFull} orient={orient} setOrient={setOrient} notes={notes}
        onPickSite={({salle,siteActes,d,sl,y,m})=>{
          const bip=actes.find(a=>a.id==="BIP");
          const full=bip&&["CHB-1","CHB-2","CHB-3"].includes(salle)?[...siteActes.filter(a=>a.id!=="BIP"),bip]:siteActes;
          setMData({salle,siteActes:full,d,sl,y,m});setModal("pickMedSite");}} viewPeriod={viewPeriod} allDays4={allDays4} setViewPeriod={setViewPeriod}/>}

      {tab==="plateau"&&<ActTabView title="❤️ PT Cardio" titleColor="#e3b341"
        rows={[
          {label:"Salle-Stim",ids:["STIM","STIM_AG","EEP_AG"],color:"#e3b341",salle:S_STIM,multiActe:true},
          {label:"Salle-EEP",ids:["EEP"],color:"#f472b6",salle:S_EEP,multiActe:true},
          {label:"Dobu",ids:["DOBU"],color:"#60a5fa",salle:null,hasSalleChoice:true,sallesDisp:["CHL-4","CHL-5"]},
          {label:"ETO",ids:["ETO_CHL"],color:"#2dd4bf",salle:null,hasSalleChoice:true,sallesDisp:SALLES_CHL},
          {label:"Reveal",ids:["REVEAL"],color:"#818cf8",salle:null,hasSalleChoice:true,sallesDisp:SALLES_CHL},
          {label:"EE CHL",ids:["EE_CHL"],color:"#4ade80",salle:S_EE_CHL},
        ].concat(actes.filter(a=>acteRecapIn(a,"PLATEAU")&&!a.isSystem).map(a=>((a.salles||[]).length>1?{label:a.label,ids:[a.id],color:a.color,salle:null,hasSalleChoice:true,sallesDisp:a.salles}:{label:a.label,ids:[a.id],color:a.color,salle:(a.salles&&a.salles[0])||null})))}
        year={year} month={month} prevM={prevM} nextM={nextM} medecins={medecins} actes={actes}
        getEntries={getEntries} allDays={allDays} isEdit={isEdit} showFull={showFull} setShowFull={setShowFull} orient={orient} setOrient={setOrient} darkMode={darkMode} setDarkMode={setDarkMode} showFull={showFull} setShowFull={setShowFull} viewPeriod={viewPeriod} allDays4={allDays4} setViewPeriod={setViewPeriod}
        onPickAct={({row,d,sl,y,m})=>{setMData({row,d,sl,y,m});setModal("pickMedAct");}}/>}

      {tab==="angio"&&<SiteView site="ANGIO" salleReg={salleReg} year={year} month={month} prevM={prevM} nextM={nextM}
        actes={actes} medecins={medecins} getEntries={getEntries} salleOcc={salleOcc}
        allDays={allDays} isEdit={isEdit} orient={orient} setOrient={setOrient} notes={notes}
        onPickSite={({salle,siteActes,d,sl,y,m})=>{setMData({salle,siteActes,d,sl,y,m});setModal("pickMedSite");}}
        darkMode={darkMode} setDarkMode={setDarkMode} showFull={showFull} setShowFull={setShowFull} viewPeriod={viewPeriod} allDays4={allDays4} setViewPeriod={setViewPeriod}/>}
      {false&&null&&<ActTabView title="🔬 PT Angio" titleColor="#c084fc"
        rows={[
          {label:"Coronarographie",ids:["CORO"],color:"#c084fc",salle:null},
          {label:"TAVI",ids:["TAVI"],color:"#fb7185",salle:null},
          {label:"FOP / FAG",ids:["FOP"],color:"#34d399",salle:null},
        ]}
        year={year} month={month} prevM={prevM} nextM={nextM} medecins={medecins} actes={actes}
        getEntries={getEntries} allDays={allDays} isEdit={isEdit} orient={orient} setOrient={setOrient} darkMode={darkMode} setDarkMode={setDarkMode} showFull={showFull} setShowFull={setShowFull} viewPeriod={viewPeriod} allDays4={allDays4} setViewPeriod={setViewPeriod}
        onPickAct={({row,d,sl,y,m})=>{setMData({row,d,sl,y,m});setModal("pickMedAct");}}/>}

      {tab==="garde"&&<GardeView year={year} month={month} prevM={prevM} nextM={nextM} medecins={medecins} getEntry={getEntry} allDays={allDays} isEdit={isEdit} orient={orient} setOrient={setOrient} applyGarde={applyGarde} isMedAvailable={isMedAvailable} plan={plan} setPlan={setPlan} darkMode={darkMode} setDarkMode={setDarkMode} showFull={showFull} setShowFull={setShowFull} viewPeriod={viewPeriod} allDays4={allDays4} setViewPeriod={setViewPeriod} tourMed={tourMed} gardeAvoid={gardeAvoid} gardeWish={gardeWish} toast={toast}/>}

      {tab==="bip"&&<BipTab year={year} month={month} prevM={prevM} nextM={nextM} medecins={medecins} allDays={allDays} isEdit={isEdit} actes={actes} getEntries={getEntries} salleOcc={salleOcc} addEntry={addEntry} removeEntry={removeEntry} isMedAvailable={isMedAvailable} orient={orient} setOrient={setOrient} darkMode={darkMode} setDarkMode={setDarkMode} showFull={showFull} setShowFull={setShowFull}/>}

      {tab==="plantype"&&(
        <div>
          <div style={S.bar}>
            <div style={{display:"flex",alignItems:"center",gap:8}}>
              <button onClick={prevM} style={S.arr}>‹</button>
              <h2 style={S.mTit}>{"📋 Planning type — "+(MOIS[perStart(year,month).sm]+" — "+MOIS[(perStart(year,month).sm+PCFG.len-1)%12]+" "+perStart(year,month).sy)}</h2>
              <button onClick={nextM} style={S.arr}>›</button>
            </div>
            <div style={{display:"flex",gap:4,alignItems:"center",marginLeft:"auto"}}>
              
              
              <button onClick={()=>setDarkMode(d=>!d)} style={{...S.arr,fontSize:13,width:30}}>{darkMode?"☀️":"🌓"}</button>
            </div>
          </div>
          {isEdit&&<div style={{display:"flex",gap:6,alignItems:"center",marginBottom:8}}>
            <button style={{fontSize:11,padding:"3px 12px",borderRadius:6,border:"1.5px solid #388bfd",background:"rgba(56,139,253,.10)",color:"#388bfd",fontWeight:800,cursor:"pointer"}} onClick={()=>openPtModal(null)}>📋 Planning type</button>
            <button style={{fontSize:11,padding:"3px 12px",borderRadius:6,border:"1px solid #dc2626",background:"var(--bg2)",color:"#dc2626",fontWeight:700,cursor:"pointer"}} onClick={()=>openPtModal(null,"remove")}>🗑 Retirer</button>
          </div>}
          <div style={{fontSize:11,color:"var(--txt3)",marginBottom:8}}>Semaine type par médecin. Le bouton ▶ PT l'applique aux mois de la période affichée (choix des mois et du point de départ dans la fenêtre). TM exclus automatiquement. Clic sur une case pour définir.</div>
          <PlanTypeGrid medecins={[...medPlan,...medAttache,...medecins.filter(m=>m.role==="ide")]} actes={actes} planningType={planningType} setPlanningType={setPlanningType} isEdit={isEdit} orient={orient} acteById={acteById} setMData={setMData} setModal={setModal}/>
        </div>
      )}

      {tab==="attache"&&(
        <div>
          <div style={S.bar}>
            <div style={{display:"flex",alignItems:"center",gap:8}}><button onClick={prevM} style={S.arr}>‹</button><h2 style={S.mTit}>{"👔 Attachés — "+(MOIS[perStart(year,month).sm]+" — "+MOIS[(perStart(year,month).sm+PCFG.len-1)%12]+" "+perStart(year,month).sy)}</h2><button onClick={nextM} style={S.arr}>›</button></div>
            <div style={{display:"flex",gap:4,alignItems:"center",marginLeft:"auto"}}><button onClick={()=>setDarkMode(d=>!d)} style={{...S.arr,fontSize:13,width:30}}>{darkMode?"☀️":"🌓"}</button><button onClick={()=>setShowFull(f=>!f)} title={showFull?"Depuis aujourd'hui":"Mois complet"} style={{...S.arr,fontSize:16,width:32,color:showFull?"var(--today-c)":"var(--txt2)",border:`1px solid ${showFull?"var(--today-c)":"var(--border)"}`}}>{showFull?"📅":"🗓️"}</button></div>
          </div>
           {isEdit&&<div style={{display:"flex",gap:6,alignItems:"center",marginBottom:8}}>
             <button style={{fontSize:11,padding:"3px 12px",borderRadius:6,border:"1.5px solid #388bfd",background:"rgba(56,139,253,.10)",color:"#388bfd",fontWeight:800,cursor:"pointer"}} onClick={()=>openPtModal(null)}>📋 Planning type</button>
           </div>}
          {orient==="H"
            ?<GridH allDays={allDays} year={year} month={month} meds={[...medAttache,...medecins.filter(m=>m.role==="ide")]} getEntries={getEntries} acteById={acteById} onCell={openCell} isEdit={isAnyEdit} notes={notes} isVac={isVac} applyGarde={applyGarde} allMeds={medecins} viewPeriod={viewPeriod} allDays4={allDays4} showFull={showFull} showGarde={false} getAstreinteForDay={getAstreinteForDay}/>
            :<GridV allDays={allDays} year={year} month={month} meds={[...medAttache,...medecins.filter(m=>m.role==="ide")]} getEntries={getEntries} acteById={acteById} onCell={openCell} isEdit={isAnyEdit} notes={notes} isVac={isVac} applyGarde={applyGarde} allMeds={medecins} viewPeriod={viewPeriod} allDays4={allDays4} showFull={showFull} showGarde={false} getAstreinteForDay={getAstreinteForDay}/>}
        </div>
      )}

      {tab==="activites"&&(
        <div>
          <div style={S.bar}><h2 style={S.mTit}>⚙️ Activités <span style={{fontSize:10,color:"var(--txt3)",fontWeight:400,marginLeft:8}}>{APP_VERSION}</span></h2><div style={{display:"flex",gap:4,alignItems:"center",marginLeft:"auto"}}><button onClick={()=>setDarkMode(d=>!d)} style={{...S.arr,fontSize:13,width:30}}>{darkMode?"☀️":"🌓"}</button></div></div>
      {isEdit&&<div style={{display:"flex",gap:6,alignItems:"center",marginBottom:10}}>
        <button style={{fontSize:11,padding:"3px 12px",borderRadius:6,border:"1.5px solid #16a34a",background:"rgba(22,163,74,.10)",color:"#16a34a",fontWeight:800,cursor:"pointer"}} onClick={()=>{setMData({_new:true,id:"",label:"",short:"",color:"#3b82f6",bg:"#0c1a2e",hasSalle:false,salles:[],isSystem:false,site:"tous",medecinsAutorise:[]});setModal("editActe");}}>+ Nouvelle activité</button>
      </div>}
          {["tous","CHL","CHB"].map(site=>(
            <div key={site} style={{marginBottom:14}}>
              <div style={{fontSize:10,fontWeight:700,color:"var(--txt3)",textTransform:"uppercase",letterSpacing:.5,marginBottom:6}}>{site==="tous"?"Toutes":site}</div>
              <div style={{display:"grid",gridTemplateColumns:"repeat(auto-fill,minmax(270px,1fr))",gap:6}}>
                {actes.filter(a=>(a.site||"tous")===site).map(a=>(
                  <div key={a.id} style={{...S.card,borderLeft:`3px solid ${a.color}`,display:"flex",alignItems:"center",gap:9}}>
                    <div style={{padding:"3px 6px",borderRadius:5,fontSize:10,fontWeight:800,fontFamily:"'JetBrains Mono',monospace",background:a.color,color:"#111",flexShrink:0}}>{a.short}</div>
                    <div style={{flex:1}}>
                      <div style={{fontWeight:700,color:"var(--txt)",fontSize:12}}>{a.label}</div>
                      {a.hasSalle&&<div style={{fontSize:9,color:"var(--txt3)"}}>{a.salles.join(", ")||"—"}</div>}
                      {(a.medecinsAutorise&&a.medecinsAutorise.length)>0&&<div style={{fontSize:9,color:"var(--txt3)"}}>{a.medecinsAutorise.join(", ")}</div>}
                    </div>
                    {isEdit&&<div style={{display:"flex",gap:4}}>
                      <button style={{...S.icnBtn}} onClick={()=>{setMData({...a,_new:false,sallesStr:(a.salles||[]).join(","),medStr:(a.medecinsAutorise||[]).join(",")});setModal("editActe");}}>✏️</button>
                      {!a.isSystem&&<button style={{...S.icnBtn,background:"#fff1f2",border:"1px solid #fecdd3",color:"#dc2626"}} onClick={()=>{if(confirm(`Supprimer "${a.label}" ?`))setActes(p=>p.filter(x=>x.id!==a.id));}}>🗑️</button>}
                    </div>}
                  </div>
                ))}
              </div>
            </div>
          ))}
        </div>
      )}

      {tab==="equipe"&&(
        <div>
          <div style={S.bar}><h2 style={S.mTit}>👥 Équipe</h2><div style={{display:"flex",gap:4,alignItems:"center",marginLeft:"auto"}}><button onClick={()=>setDarkMode(d=>!d)} style={{...S.arr,fontSize:13,width:30}}>{darkMode?"☀️":"🌓"}</button></div></div>
      {isEdit&&<div style={{display:"flex",gap:6,alignItems:"center",marginBottom:10}}>
        <button style={{fontSize:11,padding:"3px 12px",borderRadius:6,border:"1.5px solid #16a34a",background:"rgba(22,163,74,.10)",color:"#16a34a",fontWeight:800,cursor:"pointer"}} onClick={()=>{setMData({_new:true,id:Date.now(),nom:"",prenom:"",init:"",color:"#3b82f6",garde:true,tourMed:true,role:"medecin"});setModal("editMed");}}>+ Ajouter</button>
      </div>}
          {["medecin","attache","ide"].map(role=>(
            <div key={role} style={{marginBottom:18}}>
              <div style={{fontSize:10,fontWeight:700,color:"var(--txt3)",textTransform:"uppercase",letterSpacing:.5,marginBottom:7}}>{role==="medecin"?"Médecins":role==="attache"?"Attachés":"IDE"}</div>
              <div style={{display:"grid",gridTemplateColumns:"repeat(auto-fill,minmax(260px,1fr))",gap:7}}>
                {medecins.filter(m=>(m.role||"medecin")===role).map(m=>(
                  <div key={m.id} style={{...S.card,display:"flex",alignItems:"center",gap:9}}>
                    <div style={{width:38,height:38,borderRadius:"50%",background:m.color,display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:12,fontWeight:800,flexShrink:0}}>{m.init}</div>
                    <div style={{flex:1}}>
                      <div style={{fontWeight:700,color:"var(--txt)",fontSize:13}}>{m.prenom} {m.nom}</div>
                      <div style={{display:"flex",gap:3,marginTop:2,flexWrap:"wrap"}}>
                        {role==="medecin"&&(m.garde?<Chp bg="#16a34a" c="#fff">Garde</Chp>:<Chp bg="#dc2626" c="#fff">Sans garde</Chp>)}
                        {role==="medecin"&&(m.tourMed?<Chp bg="#1d4ed8" c="#fff">TM</Chp>:<Chp bg="#d97706" c="#fff">Sans TM</Chp>)}
                      </div>
                      <div style={{display:"flex",flexWrap:"wrap",gap:2,marginTop:3}}>
                        {actes.filter(a=>!a.isSystem&&(!(a.medecinsAutorise&&a.medecinsAutorise.length)||a.medecinsAutorise.includes(m.init))).slice(0,5).map(a=>(
                          <span key={a.id} style={{fontSize:7,padding:"1px 4px",borderRadius:7,
                            background:a.color,
                            color:(()=>{try{const r=parseInt(a.color.slice(1,3),16)/255,g=parseInt(a.color.slice(3,5),16)/255,b=parseInt(a.color.slice(5,7),16)/255;const l=0.2126*(r<=0.04045?r/12.92:Math.pow((r+0.055)/1.055,2.4))+0.7152*(g<=0.04045?g/12.92:Math.pow((g+0.055)/1.055,2.4))+0.0722*(b<=0.04045?b/12.92:Math.pow((b+0.055)/1.055,2.4));return l>0.35?"#111":"#fff";}catch{return"#fff";}})(),
                            fontWeight:700,fontFamily:"'JetBrains Mono',monospace"}}>{a.short}</span>
                        ))}
                      </div>
                    </div>
                    <div style={{display:"flex",flexDirection:"column",gap:3}}>
                      <div style={{display:"flex",gap:3}}>
                        <button style={{...S.icnBtn}} onClick={()=>{setMData({...m,_new:false});setModal("editMed");}}>✏️</button>
                        {isEdit&&<button style={{...S.icnBtn,background:"#fff1f2",border:"1px solid #fecdd3",color:"#dc2626"}} onClick={()=>{if(confirm(`Supprimer ${m.nom} ?`))setMedecins(p=>p.filter(x=>x.id!==m.id));}}>🗑️</button>}
                      </div>
                      <button style={{...S.icnBtn,fontSize:11,textAlign:"center"}} onClick={()=>{setMData({...m});setModal("editMedActivites");}}>🎯</button>
                      {isEdit&&<button style={{...S.icnBtn,fontSize:11,textAlign:"center"}} onClick={()=>{setMData({...m,_pinMode:true});setModal("editMedPin");}}>🔑</button>}
                    </div>
                  </div>
                ))}
              </div>
            </div>
          ))}
        </div>
      )}

      {tab==="astreinte"&&(()=>{
        const astMeds=medecins.filter(m=>m.astreinte===true);
        const astToday=new Date();

        const monKey2=(y,m,d)=>{const dt=new Date(y,m,d);const dw=dt.getDay();const diff=dw===0?-6:1-dw;const mn=new Date(dt);mn.setDate(d+diff);return mn.getFullYear()+"-"+mn.getMonth()+"-"+mn.getDate();};
        const astForDay2=(y,m,d)=>{
          const dk=y+"-"+m+"-"+d;
          const wk=monKey2(y,m,d);
          const v=astreinte[dk]!==undefined?astreinte[dk]:astreinte[wk];
          return(v!==undefined&&v!==null)?String(v):null;
        };
        const JOURS_C=["Lun","Mar","Mer","Jeu","Ven","Sam","Dim"];
        const {sy,sm}=perStart(astYear,astMonth);
        const prevAst=()=>{const p=perPrev(sy,sm);setAstYear(p.sy);setAstMonth(p.sm);};
        const nextAst=()=>{const p=perNext(sy,sm);setAstYear(p.sy);setAstMonth(p.sm);};
        const allDays4M=perDaysList(sy,sm);
        const stats={};
        astMeds.forEach(m=>{stats[String(m.id)]=0;});
        allDays4M.forEach(({y,m,d})=>{const mid=astForDay2(y,m,d);if(mid&&stats[mid]!==undefined)stats[mid]++;});
        const prevP=()=>{const p=perPrev(sy,sm);setAstYear(p.sy);setAstMonth(p.sm);};
        const nextP=()=>{const p=perNext(sy,sm);setAstYear(p.sy);setAstMonth(p.sm);};
        const pLabel=MOIS[sm]+" — "+MOIS[(sm+PCFG.len-1)%12]+" "+sy;
        // ── Répartition automatique des astreintes (semaines complètes lun→dim) ──
        const astMondays=(()=>{
          const first=allDays4M[0],last=allDays4M[allDays4M.length-1];
          const d0=new Date(first.y,first.m,first.d);
          const dw0=d0.getDay();const shift=dw0===0?-6:1-dw0;
          const mon0=new Date(first.y,first.m,first.d+shift);
          const end=new Date(last.y,last.m,last.d);
          const list=[];
          for(let mn=new Date(mon0);mn<=end;mn.setDate(mn.getDate()+7)){
            list.push({y:mn.getFullYear(),m:mn.getMonth(),d:mn.getDate()});
          }
          return list;
        })();
        const astWeekDays=(mon)=>[0,1,2,3,4,5,6].map(i=>{const dt=new Date(mon.y,mon.m,mon.d+i);return{y:dt.getFullYear(),m:dt.getMonth(),d:dt.getDate()};});
        const astAbsPart=(mid,days)=>days.some(({y,m,d})=>{
          const sls=isWE(y,m,d)?["JOUR"]:["M","AM"];
          return sls.some(sl=>getEntries(mid,y,m,d,sl).some(e=>["ABSENCE","FORM","FORMATION"].includes(e.acteId)));
        });
        const runAstAuto=()=>{
          if(astMeds.length===0){toast("Aucun médecin d'astreinte (cochez-le dans l'onglet Équipe)","warn");return;}
          if(!window.confirm("Assigner automatiquement une semaine d'astreinte (lun→dim) sur chaque semaine vide de la période, équitablement entre "+astMeds.length+" médecins ?\nLes semaines et jours déjà posés sont conservés."))return;
          const counts={};astMeds.forEach(m2=>{counts[String(m2.id)]=0;});
          const lastW={};
          const patch={};const skipped=[];let nA=0;
          astMondays.forEach((mon,idx)=>{
            const mk=mon.y+"-"+mon.m+"-"+mon.d;
            const days=astWeekDays(mon);
            const taken=astreinte[mk]!==undefined||days.some(({y,m,d})=>astreinte[y+"-"+m+"-"+d]!==undefined);
            if(taken){
              const v=astreinte[mk];
              if(v!==undefined&&counts[String(v)]!==undefined){counts[String(v)]+=7;lastW[String(v)]=idx;}
              return;
            }
            const cands=astMeds.filter(m2=>!astAbsPart(m2.id,days));
            if(cands.length===0){skipped.push({mon,days});return;}
            const shuffled=cands.map(m2=>({m2,r:Math.random()})).sort((a,b)=>a.r-b.r).map(x=>x.m2);
            shuffled.sort((a,b)=>{
              const ca=counts[String(a.id)],cb=counts[String(b.id)];
              if(ca!==cb)return ca-cb;
              const la=lastW[String(a.id)]!==undefined?idx-lastW[String(a.id)]:999;
              const lb=lastW[String(b.id)]!==undefined?idx-lastW[String(b.id)]:999;
              return lb-la;
            });
            const pick=shuffled[0];
            patch[mk]=String(pick.id);
            counts[String(pick.id)]+=7;lastW[String(pick.id)]=idx;nA++;
          });
          // Phase 2 : semaines sans candidat complet → attribution jour par jour (exceptions),
          // en privilégiant le moins chargé et les segments consécutifs chez la même personne
          const exDetails=[];const unfilledDays=[];
          skipped.forEach(({mon,days})=>{
            let i2=0;const segs=[];
            while(i2<7){
              const day=days[i2];
              const dayOK=(m2,dd)=>!astAbsPart(m2.id,[dd]);
              const avail=astMeds.filter(m2=>dayOK(m2,day));
              if(avail.length===0){unfilledDays.push(day.d+" "+MOIS[day.m].slice(0,4));i2++;continue;}
              // pour chaque candidat : longueur de course consécutive possible à partir d'ici
              const runLen=(m2)=>{let L=0;for(let k2=i2;k2<7;k2++){if(dayOK(m2,days[k2]))L++;else break;}return L;};
              const scored=avail.map(m2=>({m2,L:runLen(m2),c:counts[String(m2.id)],r:Math.random()}));
              scored.sort((a,b)=>b.L-a.L||a.c-b.c||a.r-b.r);
              const pick=scored[0];
              for(let k2=0;k2<pick.L;k2++){
                const dd=days[i2+k2];
                patch[dd.y+"-"+dd.m+"-"+dd.d]=String(pick.m2.id);
                counts[String(pick.m2.id)]++;
              }
              const dA=days[i2],dB=days[i2+pick.L-1];
              const lblA=dA.d+" "+MOIS[dA.m].slice(0,4);
              const lblB=dB.d+" "+MOIS[dB.m].slice(0,4);
              segs.push(pick.m2.init+" ("+(pick.L>1?lblA+"→"+lblB:lblA)+")");
              i2+=pick.L;
            }
            exDetails.push("sem. du "+mon.d+" "+MOIS[mon.m].slice(0,4)+" en exception : "+segs.join(" · "));
          });
          if(Object.keys(patch).length>0)setAstreinte(p=>({...p,...patch}));
          let msg="Répartition effectuée : "+nA+" semaine(s) complète(s) assignée(s).";
          if(exDetails.length>0)msg+=" ✂ "+exDetails.join(" ; ")+".";
          if(unfilledDays.length>0)msg+=" ⚠ Jours restés SANS astreinte (tous absents) : "+unfilledDays.join(", ")+".";
          if(exDetails.length===0&&unfilledDays.length===0)msg+=" ✓ Toutes les semaines sont complètes.";
          msg+=" Totaux (jours) : "+astMeds.map(m2=>m2.init+" "+counts[String(m2.id)]).join(" · ")+".";
          setAstReport(msg);
          toast("Astreintes : "+nA+" semaine(s) assignée(s)","info");
        };
        const clearAstPeriod=()=>{
          if(!window.confirm("Retirer TOUTES les astreintes de la période affichée ("+pLabel+") ?"))return;
          if(!window.confirm("Confirmer définitivement ? (récupérable via Annuler ↶)"))return;
          setAstreinte(p=>{
            const n={...p};
            astMondays.forEach(mon=>{delete n[mon.y+"-"+mon.m+"-"+mon.d];});
            allDays4M.forEach(({y,m,d})=>{delete n[y+"-"+m+"-"+d];});
            return n;
          });
          setAstReport(null);
          toast("Astreintes de la période retirées","info");
        };
        const exportCSV=()=>{
          const rows=[["Date","Jour","Médecin"]];
          allDays4M.forEach(({y,m,d})=>{
            const dt=new Date(y,m,d);const dw=JOURS_C[(dt.getDay()+6)%7];
            const mid=astForDay2(y,m,d);const med=mid?medecins.find(x=>String(x.id)===String(mid)):null;
            rows.push([d+"/"+String(m+1).padStart(2,"0")+"/"+y,dw,med?med.prenom+" "+med.nom:"-"]);
          });
          const csv=rows.map(r=>r.join(";")).join("\n");
          const blob=new Blob(["\uFEFF"+csv],{type:"text/csv;charset=utf-8"});
          const a=document.createElement("a");a.href=URL.createObjectURL(blob);a.download="astreintes.csv";a.click();
        };
        return(
          <div style={{padding:16}}>
            <div style={{display:"flex",alignItems:"center",gap:6,marginBottom:12,flexWrap:"wrap"}}>
              <button onClick={prevP} style={S.arr}>‹</button>
              <h2 style={{...S.mTit,margin:0}}><span style={{color:"#7c3aed"}}>📞</span> {pLabel}</h2>
              <button onClick={nextP} style={S.arr}>›</button>
              </div>
            <div style={{display:"flex",gap:6,alignItems:"center",marginBottom:10}}>
              {isEdit&&<button onClick={runAstAuto} style={{fontSize:11,padding:"3px 12px",borderRadius:6,border:"1.5px solid #7c3aed",background:"rgba(124,58,237,.10)",color:"#7c3aed",fontWeight:800,cursor:"pointer"}}>⚙️ Répartition auto</button>}
              {isEdit&&<button onClick={clearAstPeriod} style={{fontSize:11,padding:"3px 12px",borderRadius:6,border:"1px solid #dc2626",background:"var(--bg2)",color:"#dc2626",fontWeight:700,cursor:"pointer"}}>🗑 Retirer</button>}
              <button onClick={exportCSV} style={{...S.btnP,fontSize:11,padding:"3px 10px"}}>🖨️ Export</button>
            </div>
            {astReport&&(
              <div style={{display:"flex",alignItems:"flex-start",gap:8,padding:"8px 12px",marginBottom:10,borderRadius:8,border:"1px solid "+(astReport.includes("⚠")?"#f59e0b":"#16a34a"),background:astReport.includes("⚠")?"rgba(245,158,11,.08)":"rgba(22,163,74,.08)",fontSize:11,color:"var(--txt)",lineHeight:1.5}}>
                <span style={{flexShrink:0}}>ℹ️</span>
                <span style={{flex:1}}>{astReport}</span>
              </div>
            )}
            {/* Stats — au-dessus, style onglet Gardes */}
            <div style={{maxWidth:560,marginBottom:14,padding:12,borderRadius:10,border:"1px solid var(--border)",background:"var(--bg2)"}}>
              <div style={{fontSize:11,fontWeight:800,color:"var(--txt2)",textTransform:"uppercase",letterSpacing:.5,marginBottom:8}}>📞 Astreintes posées — {pLabel}</div>
              <table style={{borderCollapse:"collapse",width:"100%"}}>
                <thead><tr>
                  <th style={{textAlign:"left",padding:"3px 8px",fontSize:10,color:"var(--txt3)"}}>Praticien</th>
                  <th style={{padding:"3px 6px",fontSize:10,color:"var(--txt3)"}}>Jours</th>
                  <th style={{padding:"3px 6px",fontSize:10,color:"var(--txt3)"}}>Semaines équiv.</th>
                </tr></thead>
                <tbody>
                  {astMeds.slice().sort((a,b)=>(stats[b.id]||0)-(stats[a.id]||0)).map(m=>(
                    <tr key={m.id} style={{borderBottom:"1px solid var(--border2)"}}>
                      <td style={{padding:"3px 8px",fontSize:11,fontWeight:700,color:"var(--txt)"}}>
                        <span style={{display:"inline-flex",width:16,height:16,borderRadius:"50%",background:m.color,color:"#fff",fontSize:7,fontWeight:800,alignItems:"center",justifyContent:"center",marginRight:5,verticalAlign:"middle"}}>{m.init}</span>
                        {m.nom}
                      </td>
                      <td style={{textAlign:"center",padding:"3px 6px",fontSize:12,fontWeight:800,color:(stats[m.id]||0)>0?"#f85149":"var(--txt3)"}}>{stats[m.id]||0}</td>
                      <td style={{textAlign:"center",padding:"3px 6px",fontSize:11,color:"var(--txt)"}}>{((stats[m.id]||0)/7).toFixed(1)}</td>
                    </tr>
                  ))}
                </tbody>
              </table>
              <div style={{fontSize:9,color:"var(--txt3)",marginTop:4}}><span style={{display:"inline-block",width:8,height:8,borderRadius:2,border:"2px solid #7c3aed",marginRight:4,verticalAlign:"middle"}}/>exception jour · période affichée</div>
            </div>
            {/* Tableau des jours — style onglet Gardes */}
            <div style={{overflowX:"auto",overflowY:"auto",maxHeight:"calc(100vh - 110px)",borderRadius:8,border:"1px solid var(--border)"}}>
              <table style={{borderCollapse:"collapse",tableLayout:"fixed"}}>
                <thead>
                  <tr>
                    <th style={{...S.thFix,position:"sticky",top:0,left:0,zIndex:40,minWidth:80}}>Date</th>
                    <th style={{...S.thFix,position:"sticky",top:0,zIndex:20,minWidth:150}}>Astreinte</th>
                  </tr>
                </thead>
                <tbody>
                  {allDays4M.map(({y,m,d})=>{
                    const dt=new Date(y,m,d);const dw2=dt.getDay();
                    const we=dw2===6||dw2===0;
                    const isT=d===astToday.getDate()&&m===astToday.getMonth()&&y===astToday.getFullYear();
                    const dk=y+"-"+m+"-"+d;const wk=monKey2(y,m,d);
                    const hasExc=dk!==wk&&typeof astreinte[dk]==="string";
                    const mid=astForDay2(y,m,d);
                    const med=mid?medecins.find(x=>String(x.id)===String(mid)):null;
                    const isAbsMed=med?(getEntries(med.id,y,m,d,"M").some(e=>["ABSENCE","FORMATION","FORM"].includes(e.acteId))||getEntries(med.id,y,m,d,"JOUR").some(e=>["ABSENCE","FORMATION","FORM"].includes(e.acteId))):false;
                    return(
                      <tr key={dk} style={{height:36,borderBottom:"1px solid var(--border2)",...(we?{background:"var(--bg-we)"}:{}),...(isT?{background:"var(--bg-td)"}:{})}}>
                        <td style={{...S.tdFix,position:"sticky",left:0,zIndex:5,textAlign:"center",background:isT?"var(--bg-td)":we?"var(--bg-we)":"var(--td-fix)"}}>
                          <div style={{fontWeight:800,color:isT?"var(--today-c)":we?"#92400e":"var(--txt)",fontSize:13,fontFamily:"'JetBrains Mono',monospace"}}>{d} <span style={{fontSize:9,fontWeight:600}}>{MOIS[m].slice(0,4)}</span></div>
                          <div style={{fontSize:9,color:we?"#92400e":isT?"var(--today-c)":"var(--txt3)",fontWeight:600}}>{["Dim","Lun","Mar","Mer","Jeu","Ven","Sam"][dw2]}</div>
                        </td>
                        <td style={{...S.td,padding:4,cursor:isAnyEdit?"pointer":"default",...(hasExc?{outline:"2px solid #7c3aed",outlineOffset:-2}:{})}}
                          onClick={isAnyEdit?()=>{setAstPickModal({dayKey:dk,wKey:wk,isWeek:false,label:["Dim","Lun","Mar","Mer","Jeu","Ven","Sam"][dw2]+" "+d+" "+MOIS[m]+" "+y});setAstSearch("");}:undefined}>
                          {med?(<div style={{display:"flex",alignItems:"center",gap:6,padding:"4px 8px",borderRadius:6,background:med.color+"22"}}>
                            <div style={{width:22,height:22,borderRadius:"50%",background:med.color,display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:9,fontWeight:800}}>{med.init}</div>
                            <span style={{fontSize:12,fontWeight:600,color:isAbsMed?"#ef4444":"var(--txt)"}}>{med.prenom} {med.nom}</span>
                            {isAbsMed&&<span style={{fontSize:9,color:"#ef4444",fontWeight:700}}>⚠ abs</span>}
                            {hasExc&&!isAbsMed&&<span style={{fontSize:9,color:"#7c3aed",marginLeft:"auto",fontWeight:700}}>exc.</span>}
                          </div>):(<span style={{color:"var(--txt3)",fontSize:11}}>—</span>)}
                        </td>
                      </tr>
                    );
                  })}
                </tbody>
              </table>
            </div>
          </div>
        );
      })()}
      {astPickModal&&(()=>{
        const astMeds2=medecins.filter(m=>m.astreinte===true);
        const monKey2b=(y,m,d)=>{const dt=new Date(y,m,d);const dw=dt.getDay();const diff=dw===0?-6:1-dw;const mn=new Date(dt);mn.setDate(d+diff);return mn.getFullYear()+"-"+mn.getMonth()+"-"+mn.getDate();};
        const {dayKey,wKey,isWeek,label}=astPickModal;
        const curId=isWeek?astreinte[wKey]:astPickModal&&dayKey&&astreinte[dayKey]!==undefined?astreinte[dayKey]:astreinte[wKey];
        // Check if med is absent for the relevant day(s)
        const isAbsDay=(medId,y,m,d)=>
          getEntries(medId,y,m,d,"M").some(e=>["ABSENCE","FORMATION"].includes(e.acteId))||
          getEntries(medId,y,m,d,"JOUR").some(e=>["ABSENCE","FORMATION"].includes(e.acteId));
        // For week mode: check each of the 7 days and return list of absent days
        const getAbsDaysInWeek=(medId)=>{
          const parts=wKey.split("-");
          const wy=parseInt(parts[0]),wm=parseInt(parts[1]),wd=parseInt(parts[2]);
          const absent=[];
          for(let i=0;i<7;i++){
            const dt=new Date(wy,wm,wd+i);
            if(isAbsDay(medId,dt.getFullYear(),dt.getMonth(),dt.getDate()))
              absent.push(["Lun","Mar","Mer","Jeu","Ven","Sam","Dim"][i]);
          }
          return absent;
        };
        const isAbsentForPick=(medId)=>{
          if(isWeek) return false; // Never fully block for week - show per-day info instead
          if(dayKey){
            const parts=dayKey.split("-");
            return isAbsDay(medId,parseInt(parts[0]),parseInt(parts[1]),parseInt(parts[2]));
          }
          return false;
        };
        const filtered=astMeds2.filter(m=>!astSearch||m.init.toUpperCase().startsWith(astSearch.toUpperCase()));
        const onEnter=e=>{if(e.key==="Enter"&&filtered.length===1){
          const m=filtered[0];
          setAstreinte(p=>{const n={...p};if(isWeek){n[wKey]=m.id;}else{n[dayKey]=m.id;}return n;});
          setAstPickModal(null);
        }};
        return(
          <Ov onClose={()=>setAstPickModal(null)}>
            <div style={{minWidth:300}}>
              <div style={S.mHd}>
                <div style={S.mTit2}>📞 Astreinte — {label}</div>
                <button onClick={()=>setAstPickModal(null)} style={S.xBtn}>×</button>
              </div>
              {isWeek&&<div style={{fontSize:11,color:"var(--txt3)",marginBottom:8,padding:"4px 0"}}>Assigne toute la semaine (lun→dim)</div>}
              {!isWeek&&<div style={{fontSize:11,color:"#7c3aed",marginBottom:8,padding:"4px 0"}}>Exception pour ce jour uniquement</div>}
              <input autoFocus value={astSearch} onChange={e=>setAstSearch(e.target.value.toUpperCase())} onKeyDown={onEnter}
                placeholder="Initiales..." style={{width:"100%",padding:"7px 10px",borderRadius:7,border:"1px solid var(--border)",background:"var(--bg2)",color:"var(--txt)",fontSize:13,fontFamily:"'JetBrains Mono',monospace",fontWeight:700,letterSpacing:2,marginBottom:8,boxSizing:"border-box"}}/>
              {filtered.length===1&&<div style={{fontSize:10,color:"var(--txt3)",marginBottom:4,textAlign:"center"}}>↵ Entrée pour confirmer</div>}
              <div style={{display:"flex",flexDirection:"column",gap:4,maxHeight:300,overflowY:"auto"}}>
                {filtered.map(m=>{
                  const on=String(m.id)===String(curId);
                  const absent=isAbsentForPick(m.id);
                  const absDays=isWeek?getAbsDaysInWeek(m.id):[];
                  const hasAbs=isWeek?absDays.length>0:absent;
                  return(
                    <button key={m.id}
                      disabled={!isWeek&&absent}
                      onClick={(!isWeek&&absent)?undefined:()=>{
                        setAstreinte(p=>{const n={...p};
                          if(on){if(isWeek)delete n[wKey];else delete n[dayKey];}
                          else{if(isWeek){n[wKey]=String(m.id);}else{n[dayKey]=String(m.id);}}
                          return n;});
                        setAstPickModal(null);
                      }}
                      style={{display:"flex",alignItems:"center",gap:8,padding:"8px 10px",borderRadius:8,
                        border:"1px solid "+(on?"#7c3aed":hasAbs?"#fca5a5":"var(--border)"),
                        background:on?"#f5f3ff":hasAbs?"#fff8f8":"var(--bg2)",
                        cursor:(!isWeek&&absent)?"not-allowed":"pointer"}}>
                      <div style={{width:26,height:26,borderRadius:"50%",background:m.color,display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:9,fontWeight:800}}>{m.init}</div>
                      <div style={{flex:1}}>
                        <div style={{fontSize:12,fontWeight:600,color:"var(--txt)"}}>{m.prenom} {m.nom}</div>
                        {isWeek&&absDays.length>0&&<div style={{fontSize:9,color:"#ef4444",marginTop:1}}>Absent: {absDays.join(", ")}</div>}
                        {!isWeek&&absent&&<div style={{fontSize:9,color:"#ef4444",marginTop:1}}>Absent ce jour</div>}
                      </div>
                      {on&&<span style={{color:"#7c3aed",fontSize:11,flexShrink:0}}>✓</span>}
                    </button>
                  );
                })
              </div>
              {!isWeek&&dayKey&&astreinte[dayKey]!==undefined&&(
                <button onClick={()=>{setAstreinte(p=>{const n={...p};delete n[dayKey];return n;});setAstPickModal(null);}}
                  style={{marginTop:8,width:"100%",padding:"6px",borderRadius:7,border:"1px solid var(--border)",background:"var(--bg)",cursor:"pointer",color:"var(--txt3)",fontSize:11}}>
                  ↺ Supprimer exception — revenir à la semaine
                </button>
              )}
            </div>
          </Ov>
        );
      })()}

      {tab==="stats"&&isEdit&&<StatsTab medecins={medecins} actes={actes} plan={plan} year={year} month={month} darkMode={darkMode} setDarkMode={setDarkMode} tourMed={tourMed}/>}
      {tab==="partage"&&(
        <div style={{maxWidth:500}}>
          <h2 style={{...S.mTit,marginBottom:16}}>⚙️ Paramètres <span style={{fontSize:10,color:"var(--txt3)",fontWeight:400,marginLeft:8}}>{APP_VERSION}</span></h2>

          <div style={{...S.card,marginBottom:10}}>
            <div style={{fontWeight:700,color:"#3fb950",fontSize:13,marginBottom:6}}>👁 Lecture seule<div style={{display:"flex",gap:4,alignItems:"center",marginLeft:"auto"}}><button onClick={()=>setDarkMode(d=>!d)} style={{...S.arr,fontSize:13,width:30}}>{darkMode?"☀️":"🌓"}</button></div></div>
            <div style={{fontSize:11,color:"var(--txt3)"}}>Partagez l'URL directement. Sans PIN, le planning est consultable mais non modifiable.</div>
          </div>

          {isEdit&&<div style={{...S.card,marginBottom:10}}>
            <div style={{fontWeight:700,color:"#388bfd",fontSize:13,marginBottom:6}}>🔐 Code PIN éditeur</div>
            <div style={{display:"flex",gap:8}}>
              <input type="password" id="np" placeholder="Nouveau PIN" style={{...S.fi,flex:1,textAlign:"center",letterSpacing:4}}/>
              <button style={S.btnP} onClick={()=>{const v=document.getElementById("np").value;if(v.length>=4){setEditPin(v);toast("PIN mis à jour");}else toast("Min 4 car.","warn");}}>OK</button>
            </div>
          </div>}

          {isEdit&&<div style={{...S.card,marginBottom:10}}>
            <div style={{fontWeight:700,color:"#e3b341",fontSize:13,marginBottom:6}}>📆 Période d'affichage</div>
            <div style={{fontSize:11,color:"var(--txt3)",marginBottom:10}}>Tous les onglets affichent le planning par blocs de cette durée, alignés sur le mois de départ.</div>
            <div style={{display:"flex",gap:14,flexWrap:"wrap",alignItems:"center"}}>
              <label style={{display:"flex",alignItems:"center",gap:6,fontSize:12,color:"var(--txt)"}}>
                Durée
                <select value={periodCfg.len} onChange={e=>setPeriodCfg(p=>({...p,len:parseInt(e.target.value)}))}
                  style={{padding:"5px 8px",borderRadius:6,border:"1px solid var(--border)",background:"var(--inp)",color:"var(--txt)",fontSize:13}}>
                  {[1,2,3,4,6,12].map(v=><option key={v} value={v}>{v} mois</option>)}
                </select>
              </label>
              <label style={{display:"flex",alignItems:"center",gap:6,fontSize:12,color:"var(--txt)"}}>
                Mois de départ
                <select value={periodCfg.startM} onChange={e=>setPeriodCfg(p=>({...p,startM:parseInt(e.target.value)}))}
                  style={{padding:"5px 8px",borderRadius:6,border:"1px solid var(--border)",background:"var(--inp)",color:"var(--txt)",fontSize:13}}>
                  {MOIS.map((mn,mi)=><option key={mi} value={mi}>{mn}</option>)}
                </select>
              </label>
            </div>
            <div style={{marginTop:8,fontSize:10,color:"var(--txt3)"}}>Actuellement : blocs de {periodCfg.len} mois à partir de {MOIS[periodCfg.startM]} (ex. {MOIS[periodCfg.startM]} — {MOIS[(periodCfg.startM+periodCfg.len-1)%12]}).</div>
          </div>}

          {isEdit&&<div style={{...S.card,marginBottom:10}}>
            <div style={{fontWeight:700,color:"#a371f7",fontSize:13,marginBottom:6}}>🔄 Tour médical — minimums par surspécialité</div>
            <div style={{fontSize:11,color:"var(--txt3)",marginBottom:10}}>Séniors devant rester disponibles chaque semaine (hors tour, hors absents). L'algorithme vise l'<b>idéal</b> et ne descend au <b>minimum</b> que si aucune solution n'existe.</div>
            <table style={{borderCollapse:"collapse"}}>
              <thead>
                <tr>
                  <th style={{textAlign:"left",padding:"3px 10px 3px 0",fontSize:10,color:"var(--txt3)"}}></th>
                  {[["coro","Coro"],["pace","Pace"],["eep","EEP"],["ett","ETT"]].map(([k,lb])=><th key={k} style={{padding:"3px 8px",fontSize:11,color:"var(--txt2)",fontWeight:700}}>{lb}</th>)}
                </tr>
              </thead>
              <tbody>
                <tr>
                  <td style={{padding:"3px 10px 3px 0",fontSize:11,color:"var(--txt2)",fontWeight:600}}>Idéal</td>
                  {["coro","pace","eep","ett"].map(k=><td key={k} style={{padding:"3px 8px",textAlign:"center"}}>
                    <input type="number" min={0} max={9} value={tourMins[k]}
                      onChange={e=>setTourMins(p=>({...p,[k]:Math.max(0,parseInt(e.target.value)||0)}))}
                      style={{width:44,padding:"4px 6px",borderRadius:6,border:"1px solid var(--border)",background:"var(--inp)",color:"var(--txt)",fontSize:13,textAlign:"center"}}/>
                  </td>)}
                </tr>
                <tr>
                  <td style={{padding:"3px 10px 3px 0",fontSize:11,color:"var(--txt2)",fontWeight:600}}>Minimum</td>
                  {["coro","pace","eep","ett"].map(k=><td key={k} style={{padding:"3px 8px",textAlign:"center"}}>
                    <input type="number" min={0} max={9} value={tourMinsHard[k]}
                      onChange={e=>setTourMinsHard(p=>({...p,[k]:Math.max(0,parseInt(e.target.value)||0)}))}
                      style={{width:44,padding:"4px 6px",borderRadius:6,border:"1px solid var(--border)",background:"var(--inp)",color:"var(--txt)",fontSize:13,textAlign:"center"}}/>
                  </td>)}
                </tr>
              </tbody>
            </table>
          </div>}

          <div style={{...S.card,marginBottom:10}}>
            {/* Vacances scolaires */}
            <div style={{marginBottom:20,padding:"14px 16px",background:"var(--bg)",borderRadius:10,border:"1px solid var(--border)"}}>
              <div style={{fontWeight:700,fontSize:13,color:"var(--txt)",marginBottom:8}}>🏖 Vacances scolaires</div>
              <div style={{fontSize:12,color:"var(--txt2)",marginBottom:10}}>Les jours de vacances apparaissent avec un fond grisé dans tous les calendriers.</div>
              <div style={{display:"flex",alignItems:"center",gap:10,flexWrap:"wrap"}}>
                <span style={{fontSize:12,fontWeight:600,color:"var(--txt2)"}}>Zone :</span>
                <div style={{display:"flex",gap:6}}>
                  {["A","B","C"].map(z=>(
                    <button key={z} onClick={()=>{setVacZone(z);try{localStorage.setItem("cp6_vaczone",z);}catch{}}}
                      style={{padding:"6px 16px",borderRadius:7,border:`1px solid ${vacZone===z?"#1d4ed8":"var(--border)"}`,
                        background:vacZone===z?"#1d4ed8":"var(--bg2)",color:vacZone===z?"#fff":"var(--txt2)",
                        fontWeight:700,fontSize:13,cursor:"pointer"}}>
                      Zone {z}
                    </button>
                  ))}
                </div>
                <span style={{fontSize:11,color:vacDates.size>0?"#16a34a":"#f59e0b",fontWeight:600}}>
                  {vacDates.size>0?`✓ ${vacDates.size} jours chargés`:"⏳ Chargement..."}
                </span>
                {vacSource&&<div style={{fontSize:10,color:"var(--txt3)",marginTop:3}}>Source : {vacSource}</div>}
              </div>
            </div>

            {isEdit&&(()=>{
              const {sy,sm}=perStart(year,month);
              const perStartDate=new Date(sy,sm,1);
              const monthsInPlan=Object.keys(plan).map(k=>k.slice(0,7)).filter((v,i2,a2)=>a2.indexOf(v)===i2)
                .filter(mk=>{const y2=+mk.slice(0,4),m2=+mk.slice(5,7)-1;return new Date(y2,m2,1)<perStartDate;}).sort();
              return(
              <div style={{marginBottom:14,padding:10,borderRadius:8,border:"1px solid var(--border)",background:"var(--bg2)"}}>
                <div style={{fontSize:11,fontWeight:700,color:"var(--txt2)",marginBottom:6}}>🗄 Archivage</div>
                {monthsInPlan.length===0
                  ?<div style={{fontSize:10,color:"var(--txt3)"}}>Aucun mois antérieur à la période affichée dans les données actives — rien à archiver pour l'instant.</div>
                  :<div>
                    <div style={{fontSize:10,color:"var(--txt2)",marginBottom:5}}>{monthsInPlan.length} mois archivable(s) : {monthsInPlan.join(", ")}. L'archivage copie ces cases dans Firebase (collection séparée), télécharge un export JSON, puis les retire des données actives. Elles restent consultables en naviguant vers ces mois (lecture).</div>
                    <button onClick={async()=>{
                        if(!window.confirm("Archiver les "+monthsInPlan.length+" mois antérieurs à la période affichée ("+monthsInPlan.join(", ")+") ?"))return;
                        const okB=await makeBackup(true);
                        if(!okB&&!window.confirm("⚠ La sauvegarde de sécurité a échoué. Continuer quand même ?"))return;
                        const byMonth={};
                        Object.keys(plan).forEach(k=>{const mk=k.slice(0,7);if(monthsInPlan.includes(mk)){(byMonth[mk]=byMonth[mk]||{})[k]=plan[k];}});
                        try{
                          for(const mk of monthsInPlan){
                            const ref=window.firebaseDB.collection("archives").doc("arch-"+mk);
                            const prev=(await ref.get()).data()||{};
                            const merged={...(prev.plan?JSON.parse(prev.plan):{}),...byMonth[mk]};
                            await ref.set({plan:JSON.stringify(merged),_ts:Date.now()});
                          }
                        }catch(e){toast("Échec de la copie en archive — RIEN n'a été retiré","warn");return;}
                        const blob=new Blob([JSON.stringify(byMonth,null,1)],{type:"application/json"});
                        const a2=document.createElement("a");a2.href=URL.createObjectURL(blob);a2.download="archive-cardio-"+monthsInPlan[0]+"_"+monthsInPlan[monthsInPlan.length-1]+".json";a2.click();
                        setPlan(p=>{const n2={};Object.keys(p).forEach(k=>{if(!monthsInPlan.includes(k.slice(0,7)))n2[k]=p[k];});return n2;});
                        Object.keys(byMonth).forEach(mk=>{archFetched.current[mk]=true;});
                        setArchPlan(p2=>{const add={};Object.keys(byMonth).forEach(mk=>Object.assign(add,byMonth[mk]));return {...p2,...add};});
                        toast("Archivage terminé : "+monthsInPlan.length+" mois copiés puis retirés des données actives","info");refreshArchList();
                      }} style={{fontSize:11,padding:"4px 14px",borderRadius:6,border:"1.5px solid #7c3aed",background:"rgba(124,58,237,.10)",color:"#7c3aed",fontWeight:800,cursor:"pointer"}}>🗄 Archiver ces mois</button>
                  </div>}
                {archivedList.length>0&&<div style={{marginTop:8,paddingTop:7,borderTop:"1px dashed var(--border)"}}>
                  <div style={{fontSize:10,fontWeight:700,color:"var(--txt2)",marginBottom:4}}>Mois archivés ({archivedList.length}) :</div>
                  <div style={{display:"flex",flexWrap:"wrap",gap:4}}>
                    {archivedList.map(mk=>(
                      <span key={mk} style={{display:"inline-flex",alignItems:"center",gap:4,fontSize:10,fontWeight:700,padding:"3px 7px",borderRadius:12,border:"1px solid #7c3aed",background:"rgba(124,58,237,.07)",color:"#7c3aed"}}>
                        🗄 {mk}
                        <button title="Désarchiver : remettre ce mois dans les données actives" onClick={async()=>{
                            if(!window.confirm("Désarchiver "+mk+" ? Le mois sera remis dans les données actives (les cases actives existantes sont conservées en cas de doublon)."))return;
                            try{
                              const ref=window.firebaseDB.collection("archives").doc("arch-"+mk);
                              const d2=(await ref.get()).data();
                              if(!d2||!d2.plan){toast("Archive introuvable","warn");return;}
                              const frag=JSON.parse(d2.plan);
                              setPlan(p=>({...frag,...p}));
                              setArchPlan(p=>{const n2={};Object.keys(p).forEach(k=>{if(k.indexOf(mk)!==0)n2[k]=p[k];});return n2;});
                              delete archFetched.current[mk];
                              await ref.delete();
                              refreshArchList();
                              toast("Mois "+mk+" désarchivé — de retour dans les données actives","info");
                            }catch(e){toast("Échec du désarchivage","warn");}
                          }} style={{border:"none",background:"none",cursor:"pointer",fontSize:10,padding:0,color:"#16a34a",fontWeight:900}}>↩</button>
                      </span>
                    ))}
                  </div>
                </div>}
              </div>);
            })()}
            <div style={{marginBottom:14,padding:10,borderRadius:8,border:"1px solid var(--border)",background:"var(--bg2)"}}>
              <div style={{fontSize:11,fontWeight:700,color:"var(--txt2)",marginBottom:6}}>🏥 Salles</div>
              {["CHL","CHB","ANGIO","PLATEAU"].map(site2=>{
                const list=salleReg.filter(s=>Array.isArray(s.s)?s.s.indexOf(site2)>=0:s.s===site2);
                const lbl={CHL:"CHL",CHB:"CHB",ANGIO:"PT Angio",PLATEAU:"PT Cardio"}[site2];
                return <div key={site2} style={{marginBottom:6}}>
                  <div style={{fontSize:9,fontWeight:800,color:"var(--txt3)",textTransform:"uppercase",marginBottom:3}}>{lbl}</div>
                  <div style={{display:"flex",flexWrap:"wrap",gap:4}}>
                    {list.map(s=>(
                      <span key={s.n} style={{display:"inline-flex",alignItems:"center",gap:4,fontSize:10,fontWeight:700,padding:"3px 7px",borderRadius:12,border:salleEdit===s.n?"1.5px solid #388bfd":"1px solid var(--border)",background:"var(--bg)",color:"var(--txt)"}}>
                        <span onClick={()=>{setMData({...s,_origN:s.n});setModal("salleCfg");}} style={{cursor:"pointer",textDecoration:"underline dotted",padding:"2px 2px"}}>{s.n}</span>
                        <button onClick={()=>{
                            if(!window.confirm("Supprimer la salle "+s.n+" du registre ?\n(Elle sera aussi retirée des activités ; les cases déjà posées gardent leur salle.)"))return;
                            setSalleReg(p=>p.filter(x=>x.n!==s.n));
                            setActes(p=>p.map(a=>({...a,salles:(a.salles||[]).filter(sx=>sx!==s.n)})));
                          }} style={{border:"none",background:"none",cursor:"pointer",fontSize:13,padding:"0 3px",color:"#dc2626",fontWeight:900}}>×</button>
                      </span>
                    ))}
                    {list.length===0&&<span style={{fontSize:9,color:"var(--txt3)"}}>—</span>}
                  </div>
                </div>;
              })}
              {salleEdit&&(()=>{
                const inSalle=actes.filter(a=>(a.salles||[]).includes(salleEdit));
                return(
                <div style={{marginTop:6,marginBottom:6,padding:8,borderRadius:7,border:"1.5px solid #388bfd",background:"rgba(56,139,253,.05)"}}>
                  <div style={{fontSize:10,fontWeight:800,color:"#388bfd",marginBottom:5}}>Activités possibles dans {salleEdit} <span style={{color:"var(--txt3)",fontWeight:600}}>({inSalle.length})</span></div>
                  <div style={{display:"flex",flexWrap:"wrap",gap:4}}>
                    {actes.filter(a=>a.hasSalle&&!a.isSystem).map(a=>{
                      const on=(a.salles||[]).includes(salleEdit);
                      return <button key={a.id} type="button"
                        onClick={()=>setActes(p=>p.map(x=>x.id!==a.id?x:{...x,salles:on?(x.salles||[]).filter(s2=>s2!==salleEdit):(x.salles||[]).concat([salleEdit])}))}
                        style={{fontSize:10,padding:"3px 8px",borderRadius:12,cursor:"pointer",fontWeight:700,border:on?"1.5px solid "+a.color:"1px solid var(--border)",background:on?a.color+"26":"var(--bg2)",color:on?"var(--txt)":"var(--txt3)"}}>{a.short}</button>;
                    })}
                  </div>
                  <div style={{fontSize:9,color:"var(--txt3)",marginTop:4}}>Un clic ajoute/retire la salle de l'activité — c'est la même donnée que les pastilles de l'éditeur d'activité.</div>
                </div>);
              })()}
                            <button onClick={()=>{setMData({n:"",s:"CHL",_new:true});setModal("salleCfg");}}
                style={{marginTop:8,width:"100%",padding:"9px",borderRadius:8,border:"1.5px solid #16a34a",background:"rgba(22,163,74,.10)",color:"#16a34a",fontWeight:800,cursor:"pointer",fontSize:13}}>➕ Créer une salle</button>
              <div style={{fontSize:9,color:"var(--txt3)",marginTop:4}}>Les salles créées ici restent disponibles même si aucune activité ne les utilise. Renommer propage aux activités et au planning.</div>
            </div>
            <div style={{marginBottom:14,padding:10,borderRadius:8,border:"1px solid var(--border)",background:"var(--bg2)"}}>
              <div style={{fontSize:11,fontWeight:700,color:"var(--txt2)",marginBottom:6}}>🌓 Thème</div>
              <div style={{display:"flex",gap:6}}>
                <button onClick={()=>{try{localStorage.removeItem("cp6_theme");}catch(e){};const h=new Date().getHours();setDarkModeRaw(h>=20||h<7);}}
                  style={{fontSize:11,padding:"4px 12px",borderRadius:6,border:"1.5px solid #7c3aed",background:"rgba(124,58,237,.10)",color:"#7c3aed",fontWeight:800,cursor:"pointer"}}>🕐 Auto (20h–7h)</button>
                <button onClick={()=>setDarkMode(false)} style={{fontSize:11,padding:"4px 12px",borderRadius:6,border:"1px solid var(--border)",background:!darkMode?"var(--nav-act)":"var(--bg2)",color:!darkMode?"var(--nav-act-c)":"var(--txt2)",fontWeight:700,cursor:"pointer"}}>☀️ Jour</button>
                <button onClick={()=>setDarkMode(true)} style={{fontSize:11,padding:"4px 12px",borderRadius:6,border:"1px solid var(--border)",background:darkMode?"var(--nav-act)":"var(--bg2)",color:darkMode?"var(--nav-act-c)":"var(--txt2)",fontWeight:700,cursor:"pointer"}}>🌓 Nuit</button>
              </div>
              <div style={{fontSize:10,color:"var(--txt3)",marginTop:4}}>Auto : suit l'heure de l'appareil à l'ouverture. Jour/Nuit : choix mémorisé sur cet appareil (le bouton 🌓 des onglets fait pareil).</div>
            </div>
            {docSize!==null&&(()=>{
              const LIMIT=1048576;
              const pct=Math.min(100,Math.round(docSize/LIMIT*100));
              const col=pct<60?"#16a34a":pct<85?"#f59e0b":"#dc2626";
              return(
              <div style={{marginBottom:14,padding:10,borderRadius:8,border:"1px solid var(--border)",background:"var(--bg2)"}}>
                <div style={{fontSize:11,fontWeight:700,color:"var(--txt2)",marginBottom:5}}>📦 Poids des données : {(docSize/1024).toFixed(0)} Ko / 1024 Ko <span style={{color:col,fontWeight:800}}>({pct}%)</span></div>
                <div style={{height:8,borderRadius:4,background:"var(--border2)",overflow:"hidden"}}>
                  <div style={{height:"100%",width:pct+"%",background:col,borderRadius:4}}/>
                </div>
                <div style={{fontSize:10,color:"var(--txt3)",marginTop:4}}>Limite Firebase : 1 Mo par document. {pct<60?"Large marge.":pct<85?"À surveiller — un archivage des anciens mois sera à prévoir.":"⚠ Proche de la limite : archivez les anciens mois rapidement."}</div>
              </div>);
            })()}
            <div style={{fontWeight:700,color:"#e3b341",fontSize:13,marginBottom:6}}>💾 Sauvegarde des données</div>
            <div style={{fontSize:11,color:"var(--txt3)",marginBottom:12}}>
              Téléchargez une copie de toutes vos données. En cas de problème, importez ce fichier pour tout restaurer.
            </div>
            <div style={{marginBottom:14,padding:10,borderRadius:8,border:"1px solid var(--border)",background:"var(--bg2)"}}>
              <div style={{fontSize:11,fontWeight:700,color:"var(--txt2)",marginBottom:4}}>🕐 Sauvegardes automatiques (toutes les 72 h, 10 conservées)</div>
              <div style={{fontSize:10,color:"var(--txt3)",marginBottom:8}}>Restaurer écrase les données actuelles par celles de la sauvegarde choisie.</div>
              <div style={{display:"flex",flexDirection:"column",gap:4,marginBottom:8}}>
                {backupList.length===0&&<span style={{fontSize:11,color:"var(--txt3)"}}>Aucune sauvegarde pour l'instant.</span>}
                {backupList.map(b=>(
                  <div key={b.id} style={{display:"flex",alignItems:"center",gap:8,fontSize:11,color:"var(--txt)"}}>
                    <span style={{flex:1}}>{new Date(b.ts).toLocaleString("fr-FR",{day:"2-digit",month:"short",year:"numeric",hour:"2-digit",minute:"2-digit"})}</span>
                    <button style={{padding:"3px 10px",borderRadius:6,border:"1px solid #388bfd",background:"var(--bg2)",color:"#388bfd",fontSize:10,fontWeight:700,cursor:"pointer"}}
                      onClick={()=>previewBackup(b.id,b.ts)}>
                      👁 Aperçu
                    </button>
                    <button style={{padding:"3px 10px",borderRadius:6,border:"1px solid #dc2626",background:"var(--bg2)",color:"#dc2626",fontSize:10,fontWeight:700,cursor:"pointer"}}
                      onClick={()=>{if(window.confirm("Restaurer la sauvegarde du "+new Date(b.ts).toLocaleString("fr-FR")+" ?\nLes données actuelles seront remplacées.")&&window.confirm("Confirmer définitivement la restauration ?"))restoreBackup(b.id);}}>
                      ↩ Restaurer
                    </button>
                  </div>
                ))}
              </div>
              <button style={{...S.qBtn}} onClick={()=>makeBackup(true)}>💾 Sauvegarder maintenant</button>
            </div>
            <div style={{display:"flex",gap:8,flexWrap:"wrap"}}>
              <button style={{...S.btnP,background:"#e3b341",color:"#111"}} onClick={()=>{
                const data={plan,tourMed,planningType,notes,medecins,actes,editPin,
                  exportDate:new Date().toISOString(),version:"v6"};
                const blob=new Blob([JSON.stringify(data,null,2)],{type:"application/json"});
                const url=URL.createObjectURL(blob);
                const a=document.createElement("a");
                const today=new Date();
                const ds=today.getFullYear()+"-"+String(today.getMonth()+1).padStart(2,"0")+"-"+String(today.getDate()).padStart(2,"0");
                a.href=url;a.download="cardio-backup-"+ds+".json";a.click();
                URL.revokeObjectURL(url);
                toast("Sauvegarde téléchargée");
              }}>💾 Sauvegarder</button>
              {isEdit&&<button style={{...S.btnP,background:"#7c3aed"}} onClick={()=>{
                const input=document.createElement("input");
                input.type="file";input.accept=".json";
                input.onchange=e=>{
                  const file=e.target.files[0];if(!file)return;
                  const reader=new FileReader();
                  reader.onload=ev=>{
                    try{
                      const data=JSON.parse(ev.target.result);
                      if(!data.version)throw new Error("Fichier invalide");
                      const d=new Date(data.exportDate).toLocaleDateString("fr-FR");
                      if(!confirm("Restaurer la sauvegarde du "+d+" ?\nToutes les données actuelles seront remplacées."))return;
                      if(data.plan)setPlan(data.plan);
                      if(data.tourMed)setTourMed(data.tourMed);
                      if(data.planningType)setPlanningType(data.planningType);
                      if(data.notes)setNotes(data.notes);
                      if(data.medecins)setMedecins(data.medecins);
                      if(data.actes)setActes(data.actes);
                      toast("Sauvegarde restaurée");
                    }catch(err){toast("Fichier invalide","warn");}
                  };
                  reader.readAsText(file);
                };
                input.click();
              }}>📂 Importer</button>}
            </div>
          </div>

          <div style={S.card}>
            <div style={{fontWeight:700,color:"var(--txt2)",fontSize:13,marginBottom:6}}>☁️ Synchronisation Firebase</div>
            <div style={{display:"flex",alignItems:"center",gap:8}}>
              <div style={{width:10,height:10,borderRadius:"50%",flexShrink:0,background:fbStatus==="ok"?"#4ade80":fbStatus==="error"?"#ef4444":fbStatus==="offline"?"#94a3b8":"#f59e0b"}}/>
              <span style={{fontSize:12,color:"var(--txt2)"}}>
                {fbStatus==="ok"?"Connecté — données sauvegardées automatiquement":
                 fbStatus==="error"?"Erreur de connexion — vérifiez votre réseau":
                 fbStatus==="offline"?"Mode local — sans sauvegarde automatique":
                 "Connexion en cours..."}
              </span>
            </div>
          </div>
        </div>
      )}

      </main>

      {/* ═══ MODALS ═══ */}

      {/* CELL */}
      {bkPreview&&(()=>{
        const {ts,b,c:cc,added,removed,changed}=bkPreview;
        const months=Object.keys(b.byMonth||{}).concat(Object.keys(cc.byMonth||{})).filter((v,i,arr)=>arr.indexOf(v)===i).sort();
        const MOIS_N={"01":"Janv","02":"Févr","03":"Mars","04":"Avr","05":"Mai","06":"Juin","07":"Juil","08":"Août","09":"Sept","10":"Oct","11":"Nov","12":"Déc"};
        const identical=added===0&&removed===0&&changed===0;
        const Row=({label,vb,vc})=>(
          <tr style={{borderBottom:"1px solid var(--border2)"}}>
            <td style={{padding:"4px 8px",fontSize:11,color:"var(--txt2)"}}>{label}</td>
            <td style={{textAlign:"center",padding:"4px 8px",fontSize:12,fontWeight:800,color:"#388bfd"}}>{vb}</td>
            <td style={{textAlign:"center",padding:"4px 8px",fontSize:12,fontWeight:700,color:"var(--txt)"}}>{vc}</td>
            <td style={{textAlign:"center",padding:"4px 8px",fontSize:11,fontWeight:700,color:vb===vc?"var(--txt3)":(vb>vc?"#16a34a":"#f85149")}}>{vb===vc?"=":(vb>vc?"+"+(vb-vc):(vb-vc))}</td>
          </tr>
        );
        return(
        <Ov onClose={()=>setBkPreview(null)}>
          <div style={{...S.modal,maxWidth:520,maxHeight:"88vh",overflowY:"auto"}} onClick={e=>e.stopPropagation()}>
            <div style={{display:"flex",justifyContent:"space-between",alignItems:"center",marginBottom:6}}>
              <div style={S.mTit2}>👁 Aperçu — sauvegarde du {new Date(ts).toLocaleString("fr-FR",{day:"2-digit",month:"short",year:"numeric",hour:"2-digit",minute:"2-digit"})}</div>
              <button onClick={()=>setBkPreview(null)} style={S.xBtn}>×</button>
            </div>
            {identical
              ?<div style={{padding:"8px 12px",borderRadius:8,border:"1px solid #16a34a",background:"rgba(22,163,74,.08)",fontSize:12,fontWeight:700,color:"#16a34a",marginBottom:10}}>✓ Cette sauvegarde est identique au planning actuel.</div>
              :<div style={{padding:"8px 12px",borderRadius:8,border:"1px solid #f59e0b",background:"rgba(245,158,11,.08)",fontSize:12,color:"var(--txt)",marginBottom:10,lineHeight:1.5}}>
                Restaurer cette sauvegarde : <b style={{color:"#16a34a"}}>{removed} case(s) ré-apparaîtraient</b> (présentes alors, effacées depuis), <b style={{color:"#f85149"}}>{added} case(s) seraient perdues</b> (ajoutées depuis), <b style={{color:"#e3b341"}}>{changed} case(s) reviendraient à leur ancien contenu</b>.
              </div>}
            <table style={{borderCollapse:"collapse",width:"100%",marginBottom:10}}>
              <thead><tr>
                <th style={{textAlign:"left",padding:"3px 8px",fontSize:10,color:"var(--txt3)"}}></th>
                <th style={{padding:"3px 8px",fontSize:10,color:"#388bfd"}}>Sauvegarde</th>
                <th style={{padding:"3px 8px",fontSize:10,color:"var(--txt3)"}}>Actuel</th>
                <th style={{padding:"3px 8px",fontSize:10,color:"var(--txt3)"}}>Δ</th>
              </tr></thead>
              <tbody>
                <Row label="Cases remplies (total)" vb={b.nEntries} vc={cc.nEntries}/>
                <Row label="Gardes posées" vb={b.nGardes} vc={cc.nGardes}/>
                <Row label="Semaines de tour attribuées" vb={b.nTourW} vc={cc.nTourW}/>
                <Row label="Membres de l'équipe" vb={b.nMeds} vc={cc.nMeds}/>
                {months.map(mk=>(
                  <Row key={mk} label={"— "+(MOIS_N[mk.slice(5,7)]||mk.slice(5,7))+" "+mk.slice(0,4)} vb={b.byMonth[mk]||0} vc={cc.byMonth[mk]||0}/>
                ))}
              </tbody>
            </table>
            <div style={{display:"flex",gap:8,justifyContent:"flex-end"}}>
              <button onClick={()=>setBkPreview(null)} style={{padding:"9px 16px",borderRadius:8,border:"1px solid var(--border)",background:"var(--bg2)",color:"var(--txt2)",fontWeight:700,fontSize:13,cursor:"pointer"}}>Fermer</button>
              <button style={{...S.btnP,padding:"9px 18px",background:"#dc2626"}}
                onClick={()=>{if(window.confirm("Restaurer la sauvegarde du "+new Date(ts).toLocaleString("fr-FR")+" ?\nLes données actuelles seront remplacées.")&&window.confirm("Confirmer définitivement la restauration ?")){restoreBackup(bkPreview.id);setBkPreview(null);}}}>
                ↩ Restaurer cette sauvegarde
              </button>
            </div>
          </div>
        </Ov>
        );
      })()}
      {modal==="daySwap"&&mData&&(()=>{
        const{medId,y:y2,m:m2,d:d2}=mData;
        const med=medecins.find(m=>m.id===medId);
        const wkC=wKey(y2,m2,d2),wmC=tourMed[wkC]||{HC:[],USIC:[]};
        const unitC=(wmC.HC||[]).includes(medId)?"HC":"USIC";
        const busyC=[...(wmC.HC||[]),...(wmC.USIC||[])];
        const dkC=dKey(y2,m2,d2);
        const spanSel=daySwapSpan; // "J","M","AM"
        const slots=spanSel==="J"?["M","AM"]:[spanSel];
        const cands=medecins.filter(mc=>mc.role==="medecin"&&mc.tourMed&&mc.id!==medId&&!busyC.includes(mc.id)).map(mc=>{
          const blockedBy=[];
          slots.forEach(sl=>{
            const e=(plan[sk(y2,m2,d2,sl)]||{})[mc.id];
            const a=Array.isArray(e)?(e[0]&&e[0].acteId):(e&&e.acteId);
            if(["ABSENCE","FORM","FORMATION","GARDE","REPOS_GARDE","TP"].includes(a))blockedBy.push(a==="ABSENCE"?"absent":a==="TP"?"temps partiel":a==="GARDE"?"garde":a==="REPOS_GARDE"?"repos de garde":"formation");
          });
          return {m:mc,blocked:blockedBy.length>0,reason:blockedBy[0]||""};
        });
        const doDaySwap=(replId)=>{
          const repl=medecins.find(m2=>m2.id===replId);
          // 1. dérogation du tourneur (jour entier ou slot)
          setTourDerog(p=>{
            const n={...p};const o={...(n[dkC]||{})};
            if(spanSel==="J")o[medId]=true;
            else{
              const cur=o[medId];
              const obj=cur===true?{M:true,AM:true}:{...(cur||{})};
              obj[spanSel]=true;
              o[medId]=(obj.M&&obj.AM)?true:obj;
            }
            n[dkC]=o;return n;
          });
          // 2. entrée Tour réelle pour le remplaçant sur les slots
          setPlan(p=>{
            let next={...p};
            slots.forEach(sl=>{
              const k=sk(y2,m2,d2,sl);
              if(!next[k])next[k]={};
              next[k]={...next[k],[replId]:{acteId:"TOUR_"+unitC,salle:null}};
            });
            return next;
          });
          toast(repl.init+" remplace "+med.init+" au tour "+unitC+" ("+JOURSL[dow(y2,m2,d2)]+" "+d2+(spanSel==="J"?", journée":spanSel==="M"?", matin":", après-midi")+")","info");
          setModal(null);
        };
        return(
        <Ov onClose={()=>setModal("cell")}>
          <div style={{...S.modal,maxWidth:430}} onClick={e=>e.stopPropagation()}>
            <div style={{display:"flex",justifyContent:"space-between",alignItems:"center",marginBottom:6}}>
              <div style={S.mTit2}>⇄ Échanger ce jour de tour</div>
              <button onClick={()=>setModal("cell")} style={S.xBtn}>×</button>
            </div>
            <div style={{fontSize:12,color:"var(--txt2)",marginBottom:8}}>
              <b style={{color:med&&med.color}}>{med&&med.init}</b> quitte le tour <b>{unitC}</b> le {JOURSL[dow(y2,m2,d2)]} {d2} {MOIS[m2]} — choisissez son remplaçant :
            </div>
            <div style={{display:"flex",gap:6,marginBottom:10}}>
              {[["J","Journée"],["M","Matin"],["AM","Après-midi"]].map(([v,lb])=>(
                <button key={v} onClick={()=>setDaySwapSpan(v)}
                  style={{flex:1,padding:"6px 4px",borderRadius:7,fontSize:12,fontWeight:700,cursor:"pointer",
                    border:"2px solid "+(spanSel===v?"#388bfd":"var(--border2)"),
                    background:spanSel===v?"rgba(56,139,253,.14)":"var(--bg2)",color:spanSel===v?"#388bfd":"var(--txt2)"}}>{lb}</button>
              ))}
            </div>
            <div style={{maxHeight:"46vh",overflowY:"auto"}}>
              {cands.map(({m:m2,blocked,reason})=>(
                <div key={m2.id} onClick={()=>{if(!blocked)doDaySwap(m2.id);}}
                  style={{display:"flex",alignItems:"center",gap:8,padding:"8px 10px",borderRadius:8,marginBottom:5,
                    cursor:blocked?"not-allowed":"pointer",opacity:blocked?.45:1,
                    border:"1px solid var(--border2)",background:"var(--bg2)"}}>
                  <span style={{width:22,height:22,borderRadius:"50%",background:m2.color,color:"#fff",fontSize:8,fontWeight:800,display:"inline-flex",alignItems:"center",justifyContent:"center"}}>{m2.init}</span>
                  <span style={{fontSize:12,fontWeight:700,color:"var(--txt)",flex:1}}>{m2.nom} {m2.statut==="junior"?<span style={{fontSize:9,color:"#8b5cf6"}}>junior</span>:null}</span>
                  {blocked&&<span style={{fontSize:10,color:"#f85149",fontWeight:600}}>{reason}</span>}
                  {!blocked&&<span style={{fontSize:11,color:"#388bfd",fontWeight:800}}>⇄</span>}
                </div>
              ))}
              {cands.length===0&&<div style={{fontSize:11,color:"var(--txt3)"}}>Aucun candidat (tous déjà de tour cette semaine).</div>}
            </div>
          </div>
        </Ov>
        );
      })()}
      {modal==="prefs"&&mData&&(()=>{
        const {medId,y:y2,m:m2,d:d2}=mData;
        const med=medecins.find(mm=>mm.id===medId);
        const wk3=wKey(y2,m2,d2);
        const dk3=dKey(y2,m2,d2);
        const tgl=(setter,key)=>setter(p=>{const n={...p};const o={...(n[key]||{})};if(o[medId])delete o[medId];else o[medId]=true;if(Object.keys(o).length===0)delete n[key];else n[key]=o;return n;});
        const rowStyle=(active,color)=>({display:"flex",alignItems:"center",justifyContent:"space-between",gap:8,padding:"8px 10px",borderRadius:8,marginBottom:6,cursor:"pointer",fontSize:12,fontWeight:600,
          border:"1px solid "+(active?color:"var(--border)"),background:active?color+"22":"var(--bg2)",color:active?color:"var(--txt)"});
        return(
        <Ov onClose={()=>setModal("cell")}>
          <div style={{...S.modal,maxWidth:420}} onClick={e=>e.stopPropagation()}>
            <div style={{display:"flex",justifyContent:"space-between",alignItems:"center",marginBottom:6}}>
              <div style={S.mTit2}>⚙️ Préférences — {med?med.prenom+" "+med.nom:""}</div>
              <button onClick={()=>setModal("cell")} style={S.xBtn}>×</button>
            </div>
            <div style={{fontSize:11,color:"var(--txt3)",marginBottom:12}}>Semaine du {wk3.split("-")[2]} / jour du {d2} {MOIS[m2]}. Ce sont des préférences : l'algorithme les respecte quand c'est possible, elles ne bloquent jamais une pose manuelle.</div>
            {med&&med.tourMed&&<div style={{fontSize:10,color:"var(--txt3)",fontWeight:700,textTransform:"uppercase",marginBottom:4}}>Tour médical (semaine entière)</div>}
            {med&&med.tourMed&&<div style={rowStyle(!!((tourAvoid[wk3]||{})[medId]),"#7c3aed")} onClick={()=>{tgl(setTourAvoid,wk3);if((tourWish[wk3]||{})[medId])tgl(setTourWish,wk3);}}>
              <span>🚫 Préfère ne pas tourner cette semaine</span><span>{(tourAvoid[wk3]||{})[medId]?"✓":""}</span>
            </div>}
            {med&&med.tourMed&&<div style={rowStyle(!!((tourWish[wk3]||{})[medId]),"#16a34a")} onClick={()=>{tgl(setTourWish,wk3);if((tourAvoid[wk3]||{})[medId])tgl(setTourAvoid,wk3);}}>
              <span>⭐ Souhaite tourner cette semaine</span><span>{(tourWish[wk3]||{})[medId]?"✓":""}</span>
            </div>}
            {med&&med.garde&&<div style={{fontSize:10,color:"var(--txt3)",fontWeight:700,textTransform:"uppercase",margin:"10px 0 4px"}}>Garde (ce jour précis)</div>}
            {med&&med.garde&&<div style={rowStyle(!!((gardeAvoid[dk3]||{})[medId]),"#dc2626")} onClick={()=>{tgl(setGardeAvoid,dk3);if((gardeWish[dk3]||{})[medId])tgl(setGardeWish,dk3);}}>
              <span>🚫 Préfère ne pas être de garde ce jour</span><span>{(gardeAvoid[dk3]||{})[medId]?"✓":""}</span>
            </div>}
            {med&&med.garde&&<div style={rowStyle(!!((gardeWish[dk3]||{})[medId]),"#16a34a")} onClick={()=>{tgl(setGardeWish,dk3);if((gardeAvoid[dk3]||{})[medId])tgl(setGardeAvoid,dk3);}}>
              <span>⭐ Souhaite être de garde ce jour</span><span>{(gardeWish[dk3]||{})[medId]?"✓":""}</span>
            </div>}
            <div style={{display:"flex",justifyContent:"flex-end",marginTop:10}}>
              <button onClick={()=>setModal("cell")} style={{...S.btnP,padding:"8px 16px"}}>OK</button>
            </div>
          </div>
        </Ov>
        );
      })()}

      {ptModal&&(
        <Ov onClose={()=>setPtModal(null)}>
          <div style={{...S.modal,maxWidth:430}} onClick={e=>e.stopPropagation()}>
            <div style={{display:"flex",justifyContent:"space-between",alignItems:"center",marginBottom:10}}>
              <div style={S.mTit2}>{ptModal.mode==="remove"?"🧹 Retirer les affectations":"▶ Appliquer le planning type"}</div>
              <button onClick={()=>setPtModal(null)} style={S.xBtn}>×</button>
            </div>
            <div style={{fontSize:12,color:"var(--txt2)",marginBottom:12,fontWeight:600}}>
              {ptModal.medId
                ?("Pour : "+((medecins.find(m2=>m2.id===ptModal.medId)||{}).prenom||"")+" "+((medecins.find(m2=>m2.id===ptModal.medId)||{}).nom||""))
                :"Pour : tous les médecins"}
            </div>
            <div style={{fontSize:10,color:"var(--txt3)",fontWeight:700,textTransform:"uppercase",marginBottom:6}}>Mois à appliquer</div>
            <div style={{display:"flex",gap:8,flexWrap:"wrap",marginBottom:14}}>
              {ptPeriodMonths.map((pm,i)=>(
                <label key={i} style={{display:"flex",alignItems:"center",gap:5,fontSize:12,color:"var(--txt)",padding:"5px 10px",borderRadius:7,border:"1px solid "+(ptMonths.includes(i)?"#1d4ed8":"var(--border)"),background:ptMonths.includes(i)?"rgba(29,78,216,.12)":"var(--bg2)",cursor:"pointer"}}>
                  <input type="checkbox" checked={ptMonths.includes(i)}
                    onChange={()=>setPtMonths(p=>p.includes(i)?p.filter(x=>x!==i):[...p,i])}/>
                  {MOIS[pm.m]} {pm.y}
                </label>
              ))}
            </div>
            <div style={{fontSize:10,color:"var(--txt3)",fontWeight:700,textTransform:"uppercase",marginBottom:6}}>Point de départ</div>
            <div style={{display:"flex",gap:12,marginBottom:16}}>
              <label style={{display:"flex",alignItems:"center",gap:5,fontSize:12,color:"var(--txt)",cursor:"pointer"}}>
                <input type="radio" name="ptstart" checked={ptFromToday} onChange={()=>setPtFromToday(true)}/>
                À partir d'aujourd'hui
              </label>
              <label style={{display:"flex",alignItems:"center",gap:5,fontSize:12,color:"var(--txt)",cursor:"pointer"}}>
                <input type="radio" name="ptstart" checked={!ptFromToday} onChange={()=>setPtFromToday(false)}/>
                Depuis le début de la période
              </label>
            </div>
            <div style={{fontSize:10,color:"var(--txt3)",marginBottom:14}}>{ptModal.mode==="remove"?"Retire toutes les activités posées. Gardes, repos de garde, absences, formations et tour médical sont conservés.":"Les absences, gardes et repos de garde existants sont préservés. Les semaines de tour médical sont exclues."}</div>
            <div style={{display:"flex",gap:8,justifyContent:"flex-end"}}>
              <button onClick={()=>setPtModal(null)}
                style={{padding:"9px 16px",borderRadius:8,border:"1px solid var(--border)",background:"var(--bg2)",color:"var(--txt2)",fontWeight:700,fontSize:13,cursor:"pointer"}}>
                Annuler
              </button>
              <button onClick={runPtModal} style={{...S.btnP,padding:"9px 18px",...(ptModal.mode==="remove"?{background:"#dc2626"}:{})}}>{ptModal.mode==="remove"?"🧹 Retirer":"▶ Appliquer"}</button>
            </div>
          </div>
        </Ov>
      )}

      {modal==="cell"&&mData&&(()=>{
        const {medId,y:y2,m:m2,d:d2,slot}=mData;
        const med=medecins.find(x=>x.id===medId);
        const we=isWE(y2,m2,d2),isNight=slot==="N",canGarde=(med&&med.garde)===true;
        const canEditThisMed=canEdit(medId);
        const dw2=dow(y2,m2,d2);
        const entries=getEntries(medId,y2,m2,d2,slot);
        const curIds=entries.filter(e=>!e._blocked&&!e._fullDay).map(e=>e.acteId);
        const hasOther=curIds.some(id=>!["TOUR_HC","TOUR_USIC"].includes(id));

        const eligible=actes.filter(a=>{
          if(isNight)return a.id==="GARDE"&&canGarde;
          if(we)return a.id==="ABSENCE"||(a.id==="GARDE"&&canGarde);
          if(SYS.includes(a.id)) return a.id==="ABSENCE";
          // Check if medecin is authorized for this activity
          if((a.medecinsAutorise&&a.medecinsAutorise.length)>0&&!(med&&a.medecinsAutorise.includes(med.init)))return false;
          return true;
        });

        const doGarde=()=>{ applyGarde(medId,y2,m2,d2); setModal(null); };
        const doAdd=(acteId,salle=null)=>{
          if(acteId==="GARDE"){doGarde();return;}
          const _curA=getEntries(medId,y2,m2,d2,we?"JOUR":slot).map(e2=>e2.acteId);
          if(_curA.includes(acteId)){toast("Cette activité est déjà posée sur ce créneau — retirez-la d'abord (×) si besoin","warn");return;}
          const acteObj=acteById(acteId);
          const finalSalle=salle||(acteObj&&acteObj.fixedSalle)||null;
          addEntry(medId,y2,m2,d2,we?"JOUR":slot,{acteId,salle:finalSalle});
          setModal(null);
        };

        return(
          <Ov onClose={()=>setModal(null)}>
            <div style={S.mHd}>
              <div>
                <div style={S.mTit2}>{JOURSL[dw2]} {d2} {MOIS[m2]} {y2}</div>
                <div style={{color:"var(--txt2)",fontSize:12,marginTop:2}}>
                  <span style={{color:(med&&med.color),fontWeight:800}}>{(med&&med.init)}</span> — Dr. {(med&&med.prenom)} {(med&&med.nom)} · <span style={{color:"#388bfd"}}>{SLOTL[slot]}</span>
                </div>
              </div>
              <button onClick={()=>setModal(null)} style={S.xBtn}>×</button>
            </div>

            {curIds.length>0&&(
              <div style={{marginBottom:10}}>
                <div style={{fontSize:10,color:"var(--txt3)",fontWeight:700,textTransform:"uppercase",marginBottom:5}}>Activités</div>
                <div style={{display:"flex",flexWrap:"wrap",gap:4}}>
                  {entries.filter(e=>e.acteId).map((e,i)=>{
                    const a=acteById(e.acteId);if(!a)return null;
                    return(
                      <div key={i} style={{display:"flex",alignItems:"center",gap:3}}>
                        <Badge a={a}/>
                        {canEditThisMed&&<button onClick={()=>{
                          if(e.acteId==="GARDE"){
                            removeEntry(medId,y2,m2,d2,slot,e.acteId);
                            const dt=new Date(y2,m2,d2+1);const ny=dt.getFullYear(),nm=dt.getMonth(),nd3=dt.getDate();
                            setPlan(p=>{let next={...p};["JOUR","M","AM"].forEach(sl=>{const k=sk(ny,nm,nd3,sl);const dm={...(next[k]||{})};if(dm[medId]&&dm[medId].acteId==="REPOS_GARDE"){delete dm[medId];next={...next,[k]:dm};}});return next;});
                          } else removeEntry(medId,y2,m2,d2,slot,e.acteId);
                        }} style={{background:"#fee2e2",border:"1px solid #fca5a5",cursor:"pointer",color:"#dc2626",fontSize:11,padding:"1px 5px",borderRadius:4,fontWeight:900}}>×</button>}
                      </div>
                    );
                  })}
                </div>
              </div>
            )}

            {hasOther&&canEditThisMed&&(
              <div style={{display:"flex",alignItems:"center",gap:6,padding:"6px 10px",borderRadius:7,background:"#1a1000",border:"1px solid #f59e0b44",marginBottom:10}}>
                <span>⚠️</span><span style={{fontSize:11,color:"#f59e0b"}}>Ce médecin a déjà une activité sur ce créneau.</span>
              </div>
            )}

            {canEditThisMed&&(
              <div style={{display:"flex",gap:5,marginBottom:10,flexWrap:"wrap"}}>
                {!isNight&&canEditThisMed&&<button style={S.qBtn} onClick={()=>{setMData({medId,y:y2,m:m2,d:d2,slot,_absMode:true});setModal("absence");}}>Pose et retrait Abs sur période</button>}
                {canEditThisMed&&<button style={{...S.qBtn,borderColor:"#dc2626",background:"#fee2e2",color:"#991b1b"}} onClick={()=>{setMData({medId,y:y2,m:m2,d:d2,slot,_clearMode:true});setModal("clearPeriod");}}>🗑 Effacer activités sur période</button>}
                {isEdit&&<button style={{...S.qBtn,borderColor:"#1d4ed8",background:"#eff6ff",color:"#1e40af"}} onClick={()=>{setModal(null);openPtModal(medId);}}>▶ PT {med&&med.init}</button>}
                {canEditThisMed&&med&&(med.tourMed||med.garde)&&<button style={{...S.qBtn,borderColor:"#7c3aed",background:"#f3e8ff",color:"#6d28d9"}}
                  onClick={()=>{setModal("prefs");}}>
                  ⚙️ Préférences tour & garde…
                </button>}
                {canEditThisMed&&med&&(()=>{
                  const wkC=wKey(y2,m2,d2),wmC=tourMed[wkC]||{HC:[],USIC:[]};
                  const isTourWk=[...(wmC.HC||[]),...(wmC.USIC||[])].includes(medId);
                  if(!isTourWk||isWE(y2,m2,d2))return null;
                  const dkC=dKey(y2,m2,d2);
                  const derog=((tourDerog||{})[dkC]||{})[medId];
                  const unitC=(wmC.HC||[]).includes(medId)?"HC":"USIC";
                  if(derog)return(<button style={{...S.qBtn,borderColor:"#16a34a",background:"rgba(22,163,74,.10)",color:"#16a34a"}}
                    onClick={()=>{
                      // Annulation : lever la dérogation + retirer les entrées Tour réelles du jour (le remplaçant)
                      setTourDerog(p=>{const n={...p};const o={...(n[dkC]||{})};delete o[medId];if(Object.keys(o).length===0)delete n[dkC];else n[dkC]=o;return n;});
                      setPlan(p=>{
                        let next={...p};
                        ["M","AM"].forEach(sl=>{
                          const k=sk(y2,m2,d2,sl);if(!next[k])return;
                          const dm3={...next[k]};let ch=false;
                          Object.keys(dm3).forEach(mid2=>{
                            const e2=Array.isArray(dm3[mid2])?dm3[mid2][0]:dm3[mid2];
                            if(e2&&e2.acteId==="TOUR_"+unitC){delete dm3[mid2];ch=true;}
                          });
                          if(ch)next[k]=dm3;
                        });
                        return next;
                      });
                      toast(med.init+" remis au tour "+unitC+" ce jour (remplacement retiré)","info");
                      setModal(null);
                    }}>
                    ↩ Remettre au tour ce jour
                  </button>);
                  return(<button style={{...S.qBtn,borderColor:"#f59e0b",background:"rgba(245,158,11,.10)",color:"#b45309"}}
                    onClick={()=>{setModal("daySwap");}}>
                    ⇄ Échanger ce jour de tour…
                  </button>);
                })()}
                {isEdit&&<button style={{...S.qBtn,borderColor:"#dc2626",background:"#fee2e2",color:"#991b1b"}} onClick={()=>clearPlanningType(medId)}>🗑 Effacer mois {med&&med.nom}</button>}
                {(isNight||we)&&canGarde&&canEditThisMed&&<button style={{...S.qBtn,borderColor:"#388bfd",background:"#0c1a2e",color:"#388bfd"}} onClick={doGarde}>🌙 Garde + repos auto</button>}
                {isNight&&!canGarde&&<span style={{color:"var(--txt3)",fontSize:12}}>Ce médecin ne participe pas aux gardes.</span>}
              </div>
            )}

            {canEditThisMed&&<div style={{fontSize:10,color:"var(--txt3)",fontWeight:700,textTransform:"uppercase",marginBottom:6}}>Ajouter</div>}
            {canEditThisMed&&(
              <div style={S.actGrd}>
                {eligible.filter(a=>a.id!=="GARDE").map(a=>{
                  const on=curIds.includes(a.id);
                  // Check if fixedSalle is already occupied by ANY activity using that room
                  const fixedSalleOcc=a.fixedSalle?(()=>{
                    // Gather all medecins in this physical room across all actes that use it
                    const roomOccupants=[];
                    actes.filter(ax=>ax.fixedSalle===a.fixedSalle||ax.salles&&ax.salles.includes(a.fixedSalle)).forEach(ax=>{
                      const occ=salleOcc(ax.id,y2,m2,d2,slot)[a.fixedSalle]||[];
                      occ.forEach(m=>{ if(!roomOccupants.find(x=>x.id===m.id)) roomOccupants.push(m); });
                    });
                    return roomOccupants;
                  })():[];
                  const salleWarn=fixedSalleOcc.length>0&&!fixedSalleOcc.find(m=>m.id===medId);
                  return(
                    <button key={a.id} style={{...S.actTog,
                      background:a.color,color:"#111",
                      border:`2px solid ${salleWarn?"#f59e0b":on?"#333":a.color}`,
                      fontWeight:900,
                      opacity:on?1:0.75}}
                      title={salleWarn?`⚠ ${a.fixedSalle} occupée par ${fixedSalleOcc.map(m=>m.init).join(", ")}`:undefined}
                      onClick={()=>{ if(a.fixedSalle){doAdd(a.id,a.fixedSalle);}else if(a.hasSalle)setMData(p=>({...p,_pickSalle:a.id}));else doAdd(a.id); }}>
                      <span style={{fontWeight:800,fontSize:11,fontFamily:"'JetBrains Mono',monospace"}}>{a.short}{salleWarn?" ⚠":""}</span>
                      <span style={{fontSize:10}}>{a.label}</span>
                      {salleWarn&&<span style={{fontSize:9,color:"#f59e0b"}}>{fixedSalleOcc.map(m=>m.init).join(", ")} déjà assigné</span>}
                    </button>
                  );
                })
              </div>
            )}

            {mData&&mData._pickSalle&&isEdit&&(()=>{
              const a=acteById(mData._pickSalle);if(!a)return null;
              // Check occupancy for each salle: ALL activities, not just this one
              const occ=salleOcc(a.id,y2,m2,d2,slot);
              // Build full room occupancy across ALL actes
              const fullRoomOcc={};
              actes.filter(ax=>ax.hasSalle).forEach(ax=>{
                const axOcc=salleOcc(ax.id,y2,m2,d2,slot);
                Object.entries(axOcc).forEach(([s,meds])=>{
                  if(!fullRoomOcc[s])fullRoomOcc[s]=[];
                  meds.forEach(m=>{if(!fullRoomOcc[s].find(x=>x.id===m.id))fullRoomOcc[s].push(m);});
                });
              });
              return(
                <div style={{marginTop:9,padding:10,background:"var(--bg)",borderRadius:8,border:`1px solid ${a.color}33`}}>
                  <div style={{fontSize:10,color:a.color,fontWeight:700,marginBottom:7}}>{a.label} — Salle</div>
                  <div style={{display:"flex",flexWrap:"wrap",gap:5}}>
                    {!a.fixedSalle&&<button style={{padding:"5px 9px",borderRadius:5,border:"1px solid var(--border)",cursor:"pointer",background:"var(--bg2)",color:"var(--txt2)",fontSize:11,fontWeight:700}} onClick={()=>doAdd(a.id,null)}>Sans salle</button>}
                    {(a.salles||[]).map(s=>{
                      const roomOccs=fullRoomOcc[s]||[];
                      const selfOccs=occ[s]||[];
                      const isFull=a.maxParSalle&&selfOccs.length>=a.maxParSalle;
                      const hasOther=roomOccs.length>0&&!roomOccs.every(m=>m.id===medId);
                      const warn=isFull||hasOther;
                      const allOccs=[...new Set([...roomOccs,...selfOccs].map(m=>m.init))];
                      return <button key={s}
                        style={{padding:"5px 9px",borderRadius:5,
                          border:`1px solid ${warn?"#f59e0b":"var(--border)"}`,
                          cursor:"pointer",fontFamily:"'JetBrains Mono',monospace",fontSize:11,fontWeight:700,
                          background:warn?"#fff3cd":a.color,color:warn?"#92400e":"#111"}}
                        title={warn?`⚠ ${allOccs.join(", ")} déjà dans cette salle`:""}
                        onClick={()=>{ doAdd(a.id,s); }}>
                        {s.replace("CHB-","").replace("CHL-","")+( warn?` ⚠ (${allOccs.join(",")})`:"")}
                      </button>;
                    })}
                  </div>
                  {Object.values(fullRoomOcc).some(arr=>arr.length>0)&&(
                    <div style={{marginTop:6,fontSize:10,color:"#f59e0b"}}>⚠ Salles marquées = déjà occupées sur ce créneau</div>
                  )}
                </div>
              );
            })()}

            <div style={{marginTop:12,borderTop:"1px solid var(--border)",paddingTop:10}}>
              <div style={{fontSize:10,color:"var(--txt3)",fontWeight:700,textTransform:"uppercase",marginBottom:5}}>📝 Note</div>
              <textarea value={notes[nk(medId,y2,m2,d2,slot)]||""} onChange={e=>setNotes(p=>({...p,[nk(medId,y2,m2,d2,slot)]:e.target.value}))}
                placeholder="Note visible au survol..." readOnly={!canEditThisMed}
                style={{width:"100%",padding:"6px 8px",borderRadius:7,border:"1px solid var(--border)",background:"var(--inp)",color:"var(--txt)",fontSize:12,fontFamily:"'Sora',sans-serif",resize:"vertical",minHeight:48,outline:"none"}}/>
            </div>
          </Ov>
        );
      })()}

            {modal==="editMedPin"&&mData&&(
        <Ov onClose={()=>setModal(null)}>
          <div style={S.mHd}>
            <div>
              <div style={S.mTit2}>🔑 PIN — Dr. {mData.prenom} {mData.nom}</div>
              <div style={{fontSize:11,color:"var(--txt3)",marginTop:2}}>Ce PIN permet au médecin de modifier uniquement son propre planning.</div>
            </div>
            <button onClick={()=>setModal(null)} style={S.xBtn}>×</button>
          </div>
          <div style={{marginBottom:12}}>
            <div style={{fontSize:12,color:"var(--txt2)",marginBottom:8}}>PIN actuel : <strong style={{color:medPins[mData.id]?"var(--today-c)":"var(--txt3)"}}>{medPins[mData.id]||"Non défini"}</strong></div>
            <div style={{display:"flex",gap:8}}>
              <input id="medpin" type="text" placeholder="Nouveau PIN (min 3 car.)" maxLength={8}
                style={{...S.fi,flex:1,textAlign:"center",letterSpacing:4,fontSize:16}}/>
              <button style={S.btnP} onClick={()=>{
                const v=document.getElementById("medpin").value.trim();
                if(v.length<3)return toast("Min 3 caractères","warn");
                if(v===editPin)return toast("Ce PIN est réservé à l'admin","warn");
                // Check not used by another med
                const conflict=Object.entries(medPins).find(([id,p])=>p===v&&parseInt(id)!==mData.id);
                if(conflict){const m2=medecins.find(m=>m.id===parseInt(conflict[0]));return toast(`Ce PIN est déjà utilisé par ${m2?.init||"un autre médecin"}`,"warn");}
                setMedPins(p=>({...p,[mData.id]:v}));
                toast(`PIN de ${mData.init} enregistré`);
                setModal(null);
              }}>OK</button>
            </div>
            {medPins[mData.id]&&<button style={{...S.qBtn,marginTop:8,width:"100%"}} onClick={()=>{
              setMedPins(p=>{const n={...p};delete n[mData.id];return n;});
              toast(`PIN de ${mData.init} supprimé`);setModal(null);
            }}>Supprimer le PIN</button>}
          </div>
          <div style={{fontSize:11,color:"var(--txt3)",padding:"8px 10px",background:"var(--bg)",borderRadius:7}}>
            💡 Le médecin entre son PIN sur l'écran de connexion → accès en édition restreinte à sa colonne uniquement.
          </div>
        </Ov>
      )}

      {modal==="clearPeriod"&&mData&&<Ov onClose={()=>setModal(null)}>
        <ClearPeriodModal
          medecins={medecins}
          initMedId={mData.medId}
          initDate={`${mData.y}-${String(mData.m+1).padStart(2,"0")}-${String(mData.d).padStart(2,"0")}`}
          onApply={({keepAbs,medId,dateFrom,dateTo,slots,absType="ABSENCE"})=>{
            const KEEP=keepAbs?["GARDE","REPOS_GARDE","TOUR_HC","TOUR_USIC","ABSENCE","FORM","FORMATION"]:SYS.filter(x=>x!=="ABSENCE");
            // Remove all non-system entries for medId over the period
            const df=new Date(dateFrom),dt=new Date(dateTo);
            const cur=new Date(df);
            while(cur<=dt){
              const y3=cur.getFullYear(),m3=cur.getMonth(),d3=cur.getDate();
              const slotsToClr=slots.includes("ALL")||slots.length===2?["M","AM","JOUR"]:slots;
              slotsToClr.forEach(sl=>{
                const key=sk(y3,m3,d3,sl);
                setPlan(p=>{
                  const dm={...(p[key]||{})};
                  if(dm[medId]){
                    const ex=dm[medId];
                    const entries=Array.isArray(ex)?ex:[ex];
                    const kept=entries.filter(e=>KEEP.includes(e.acteId));
                    if(kept.length===0)delete dm[medId];
                    else dm[medId]=kept.length===1?kept[0]:kept;
                  }
                  return{...p,[key]:dm};
                });
              });
              cur.setDate(cur.getDate()+1);
            }
            setModal(null);
          }}
          onClose={()=>setModal(null)}
        />
      </Ov>}

      {modal==="absence"&&<Ov onClose={()=>setModal(null)}><AbsModal medecins={medecins}
  initMedId={mData&&mData._absMode?mData.medId:null}
  initDate={mData&&mData._absMode?`${mData.y}-${String(mData.m+1).padStart(2,"0")}-${String(mData.d).padStart(2,"0")}`:null}
  onApply={p=>{applyAbsence(p);setModal(null);}}
  onRemove={p=>{removeAbsence(p);setModal(null);}}
  onClose={()=>setModal(null)}/></Ov>}
      {modal==="pickMedAct"&&mData&&<PickMedActModal mData={mData} setMData={setMData} medecins={medecins} actes={actes} getEntries={getEntries} isMedAvailable={isMedAvailable} addEntry={addEntry} removeEntry={removeEntry} onClose={()=>setModal(null)}/>}
      {modal==="pickMedSite"&&mData&&<PickMedSiteModal mData={mData} medecins={medecins} actes={actes} getEntries={getEntries} isMedAvailable={isMedAvailable} addEntry={addEntry} removeEntry={removeEntry} onClose={()=>setModal(null)}/>}
      {modal==="editPT"&&mData&&<EditPTModal mData={mData} setMData={setMData} medecins={medecins} actes={actes} planningType={planningType} setPlanningType={setPlanningType} onClose={()=>setModal(null)}/>}

      {modal==="editActe"&&mData&&(
        <Ov onClose={()=>setModal(null)}>
          <div style={S.mHd}><div style={S.mTit2}>{mData._new?"Nouvelle activité":"Modifier activité"}</div><button onClick={()=>setModal(null)} style={S.xBtn}>×</button></div>
          <div style={S.fGrd}>
            <FF l="Libellé" v={mData.label} c={v=>setMData(p=>({...p,label:v}))}/>
            <FF l="Abréviation" v={mData.short} c={v=>setMData(p=>({...p,short:v.toUpperCase().slice(0,6)}))}/>
            {mData._new&&<FF l="ID unique" v={mData.id} c={v=>setMData(p=>({...p,id:v.toUpperCase().replace(/\s/g,"_")}))}/>}
            <div style={{gridColumn:"1/-1"}}>
              <label style={S.fl}>Couleur du badge</label>
              <div style={{display:"flex",alignItems:"center",gap:10,marginTop:4}}>
                <input type="color" value={mData.color||"#888888"} 
                  onChange={e=>{
                    const c=e.target.value;
                    const lum=hexToLum(c);
                    // bg = auto-computed lighter/darker version
                    setMData(p=>({...p,color:c,bg:c}));
                  }} style={{width:48,height:36,padding:2,borderRadius:6,border:"1px solid var(--border)",cursor:"pointer"}}/>
                <div style={{padding:"5px 12px",borderRadius:6,background:mData.color,
                  color:hexToLum(mData.color||"#888")>0.35?"#111":"#fff",
                  fontWeight:800,fontSize:13,fontFamily:"'JetBrains Mono',monospace"}}>
                  {mData.short||"ABC"}
                </div>
                <span style={{fontSize:11,color:"var(--txt3)"}}>Aperçu du badge</span>
              </div>
            </div>
            <div style={{gridColumn:"1/-1"}}><label style={S.fl}>Site</label><div style={{display:"flex",gap:5}}>{["tous","CHL","CHB"].map(s=><button key={s} onClick={()=>setMData(p=>({...p,site:s}))} style={{flex:1,padding:"6px",borderRadius:6,border:"none",cursor:"pointer",fontWeight:700,fontSize:12,background:mData.site===s?"#1d4ed8":"var(--bg2)",color:mData.site===s?"#fff":"var(--txt2)"}}>{s}</button>)}</div></div>
            <div style={{gridColumn:"1/-1",display:"flex",gap:8,alignItems:"center"}}><input type="checkbox" checked={mData.hasSalle} onChange={e=>setMData(p=>({...p,hasSalle:e.target.checked}))} style={{width:14,height:14}}/><label style={{color:"var(--txt2)",fontSize:12}}>A une salle associée</label></div>
            <div style={{gridColumn:"1/-1"}}>
              <label style={{color:"var(--txt2)",fontSize:12,display:"block",marginBottom:3}}>↩ Colonne/ligne de reprise dans :</label>
              <div style={{display:"flex",gap:10,flexWrap:"wrap"}}>
                {[["CHL","🏥 CHL"],["CHB","🏥 CHB"],["ANGIO","🔬 PT Angio"],["PLATEAU","❤️ PT Cardio"]].map(([v2,l2])=>{
                  const cur=mData.recapSites||[].concat(mData.recapSite?[mData.recapSite]:[]).concat(mData.ptCardio?["PLATEAU"]:[]);
                  const on=cur.includes(v2);
                  return <label key={v2} style={{display:"inline-flex",alignItems:"center",gap:4,fontSize:11,color:"var(--txt2)",cursor:"pointer"}}>
                    <input type="checkbox" checked={on} onChange={()=>setMData(p=>{
                      const base=p.recapSites||[].concat(p.recapSite?[p.recapSite]:[]).concat(p.ptCardio?["PLATEAU"]:[]);
                      const nx=on?base.filter(x=>x!==v2):base.concat([v2]);
                      return {...p,recapSites:nx,recapSite:undefined,ptCardio:undefined};
                    })} style={{width:13,height:13}}/>{l2}</label>;
                })}
              </div>
            </div>
            {mData.hasSalle&&<div style={{gridColumn:"1/-1"}}><label style={S.fl}>Salles</label>
              <div style={{display:"flex",flexWrap:"wrap",gap:4,marginBottom:5}}>
                {salleReg.map(x=>x.n).concat(actes.flatMap(a2=>a2.salles||[])).filter((s,ix,arr)=>arr.indexOf(s)===ix).sort().map(s=>{
                  const on=(mData.salles||[]).includes(s);
                  return <button key={s} type="button" onClick={()=>setMData(p=>{const cur=p.salles||[];const nx=on?cur.filter(x=>x!==s):cur.concat([s]);return {...p,salles:nx,sallesStr:nx.join(", ")};})}
                    style={{fontSize:10,padding:"3px 8px",borderRadius:12,cursor:"pointer",fontWeight:700,border:on?"1.5px solid #388bfd":"1px solid var(--border)",background:on?"rgba(56,139,253,.15)":"var(--bg2)",color:on?"#388bfd":"var(--txt2)"}}>{s}</button>;
                })}
              </div>
              <div style={{fontSize:9,color:"var(--txt3)"}}>Créer/renommer une salle : Paramètres → 🏥 Salles.</div></div>}
            <div style={{gridColumn:"1/-1"}}><label style={S.fl}>Médecins autorisés (vide = tous)</label>
              <div style={{display:"flex",flexWrap:"wrap",gap:4,maxHeight:120,overflowY:"auto"}}>
                {medecins.filter(m2=>m2.role!=="ide").map(m2=>{
                  const on=(mData.medecinsAutorise||[]).includes(m2.init);
                  return <button key={m2.id} type="button" onClick={()=>setMData(p=>{const cur=p.medecinsAutorise||[];const nx=on?cur.filter(x=>x!==m2.init):cur.concat([m2.init]);return {...p,medecinsAutorise:nx,medStr:nx.join(", ")};})}
                    style={{fontSize:10,padding:"3px 8px",borderRadius:12,cursor:"pointer",fontWeight:700,display:"inline-flex",alignItems:"center",gap:4,border:on?"1.5px solid "+m2.color:"1px solid var(--border)",background:on?m2.color+"26":"var(--bg2)",color:on?"var(--txt)":"var(--txt3)"}}>
                    <span style={{width:12,height:12,borderRadius:"50%",background:m2.color,display:"inline-block"}}/>{m2.init}</button>;
                })}
              </div></div>
          </div>
          <button style={{...S.btnP,width:"100%",marginTop:10}} onClick={()=>{
            if(!mData.label||!mData.short)return toast("Libellé et abréviation requis","warn");
            if(mData._new&&!mData.id)return toast("ID requis","warn");
            if(mData._new&&actes.find(a=>a.id===mData.id))return toast("ID déjà utilisé","warn");
            const {_new,sallesStr,medStr,...rest}=mData;
            rest.bg=rest.color; // bg always equals color for consistent badge display
            if(_new)setActes(p=>[...p,rest]);else setActes(p=>p.map(a=>a.id===rest.id?rest:a));
            setModal(null);toast("Activité enregistrée");
          }}>Enregistrer</button>
        </Ov>
      )}

      {modal==="salleCfg"&&mData&&(
        <Ov onClose={()=>setModal(null)}>
          <div style={S.mHd}><div style={S.mTit2}>{mData._new?"➕ Nouvelle salle":"🏥 "+mData._origN}</div><button onClick={()=>setModal(null)} style={S.xBtn}>×</button></div>
          <div style={{padding:"4px 2px"}}>
            <label style={S.fl}>Nom de la salle</label>
            <input value={mData.n||""} onChange={e=>setMData(p=>({...p,n:e.target.value}))} style={{...S.fi,width:"100%",fontSize:14,padding:"8px"}} placeholder="ex : CHL-5"/>
            <label style={{...S.fl,marginTop:10,display:"block"}}>Onglet</label>
            <div style={{display:"flex",gap:6,flexWrap:"wrap"}}>
              {[["CHL","\ud83c\udfe5 CHL"],["CHB","\ud83c\udfe5 CHB"],["ANGIO","\ud83d\udd2c PT Angio"],["PLATEAU","\u2764\ufe0f PT Cardio"]].map(([v2,l2])=>(
                <button key={v2} onClick={()=>setMData(p=>{const cur=Array.isArray(p.s)?p.s:(p.s?[p.s]:[]);const nx=cur.includes(v2)?cur.filter(x=>x!==v2):cur.concat([v2]);return {...p,s:nx};})} style={{flex:"1 1 40%",padding:"9px 6px",borderRadius:8,border:"none",cursor:"pointer",fontWeight:700,fontSize:13,background:(Array.isArray(mData.s)?mData.s:[mData.s]).includes(v2)?"#1d4ed8":"var(--bg2)",color:(Array.isArray(mData.s)?mData.s:[mData.s]).includes(v2)?"#fff":"var(--txt2)"}}>{l2}</button>
              ))}
            </div>
            <div style={{marginTop:12}}>
              <label style={S.fl}>Activités possibles dans cette salle</label>
              {[["CHL","CHL"],["CHB","CHB"],["tous","Communes aux deux sites"]].map(([sv,sl2])=>{
                const grp=actes.filter(a=>a.hasSalle&&!a.isSystem&&(a.site||"tous")===sv);
                if(grp.length===0)return null;
                return(
              <div key={sv} style={{marginTop:6}}>
              <div style={{fontSize:9,fontWeight:800,color:"var(--txt3)",textTransform:"uppercase",marginBottom:3}}>{sl2}</div>
              <div style={{display:"flex",flexWrap:"wrap",gap:6}}>
                {grp.map(a=>{
                  const on=mData._new?(mData._acts||[]).includes(a.id):(a.salles||[]).includes(mData._origN);
                  return <button key={a.id} onClick={()=>{
                    if(mData._new){setMData(p=>({...p,_acts:on?(p._acts||[]).filter(x=>x!==a.id):(p._acts||[]).concat([a.id])}));return;}
                    setActes(p=>p.map(x=>x.id!==a.id?x:{...x,salles:on?(x.salles||[]).filter(s2=>s2!==mData._origN):(x.salles||[]).concat([mData._origN])}));}}
                    style={{fontSize:12,padding:"7px 12px",borderRadius:14,cursor:"pointer",fontWeight:700,border:on?"1.5px solid "+a.color:"1px solid var(--border)",background:on?a.color+"26":"var(--bg2)",color:on?"var(--txt)":"var(--txt3)"}} title={a.label}>{a.label.length<=16?a.label:a.short}</button>;
                })}
              </div>
              </div>);
              })}
            </div>
            {!mData._new&&<div style={{marginTop:12,display:"flex",gap:8,alignItems:"center"}}>
              <span style={{fontSize:12,color:"var(--txt2)"}}>Position dans l'onglet :</span>
              <button onClick={()=>setSalleReg(p=>{const idx=p.findIndex(x=>x.n===mData._origN);if(idx<=0)return p;let k2=idx-1;while(k2>=0&&p[k2].s!==p[idx].s)k2--;if(k2<0)return p;const n2=p.slice();const t2=n2[idx];n2[idx]=n2[k2];n2[k2]=t2;return n2;})} style={{...S.arr,fontSize:14}}>◀</button>
              <button onClick={()=>setSalleReg(p=>{const idx=p.findIndex(x=>x.n===mData._origN);if(idx<0)return p;let k2=idx+1;while(k2<p.length&&p[k2].s!==p[idx].s)k2++;if(k2>=p.length)return p;const n2=p.slice();const t2=n2[idx];n2[idx]=n2[k2];n2[k2]=t2;return n2;})} style={{...S.arr,fontSize:14}}>▶</button>
            </div>}
            <div style={{display:"flex",gap:8,marginTop:14}}>
              {!mData._new&&<button onClick={()=>{
                  if(!window.confirm("Supprimer la salle "+mData._origN+" du registre ?\n(Retirée aussi des activités ; les cases déjà posées la gardent.)"))return;
                  setSalleReg(p=>p.filter(x=>x.n!==mData._origN));
                  setActes(p=>p.map(a=>({...a,salles:(a.salles||[]).filter(s2=>s2!==mData._origN)})));
                  setModal(null);
                }} style={{padding:"9px 12px",borderRadius:8,border:"1px solid #dc2626",background:"rgba(220,38,38,.08)",color:"#dc2626",fontWeight:700,cursor:"pointer",fontSize:13}}>🗑 Supprimer</button>}
              <button onClick={()=>{
                  const nm=(mData.n||"").trim();
                  if(!nm)return toast("Nom requis","warn");
                  const sArr=Array.isArray(mData.s)?mData.s:(mData.s?[mData.s]:[]);
                  if(sArr.length===0)return toast("Choisissez au moins un onglet","warn");
                  if(mData._new){
                    if(salleReg.some(x=>x.n===nm))return toast("Cette salle existe déjà","warn");
                    setSalleReg(p=>[...p,{n:nm,s:sArr.length===1?sArr[0]:sArr}]);
                    if((mData._acts||[]).length>0)setActes(p=>p.map(a=>(mData._acts.includes(a.id)&&!(a.salles||[]).includes(nm))?{...a,salles:(a.salles||[]).concat([nm])}:a));
                    toast("Salle créée : "+nm,"info");
                  }else if(nm!==mData._origN){
                    if(salleReg.some(x=>x.n===nm))return toast("Ce nom existe déjà","warn");
                    setSalleReg(p=>p.map(x=>x.n===mData._origN?{...x,n:nm,s:mData.s}:x));
                    setActes(p=>p.map(a=>({...a,salles:(a.salles||[]).map(s2=>s2===mData._origN?nm:s2)})));
                    setPlan(p=>{const n2={};Object.keys(p).forEach(k=>{const dm={};Object.keys(p[k]).forEach(mid=>{const e=p[k][mid];const fx=(o)=>o&&o.salle===mData._origN?{...o,salle:nm}:o;dm[mid]=Array.isArray(e)?e.map(fx):fx(e);});n2[k]=dm;});return n2;});
                    toast("Salle renommée partout : "+mData._origN+" \u2192 "+nm,"info");
                  }else{
                    setSalleReg(p=>p.map(x=>x.n===mData._origN?{...x,s:mData.s}:x));
                  }
                  setModal(null);
                }} style={{flex:1,padding:"9px",borderRadius:8,border:"none",background:"#1d4ed8",color:"#fff",fontWeight:800,cursor:"pointer",fontSize:13}}>{mData._new?"Créer":"Enregistrer"}</button>
            </div>
          </div>
        </Ov>
      )}
      {modal==="editMed"&&mData&&(
        <Ov onClose={()=>setModal(null)}>
          <div style={S.mHd}><div style={S.mTit2}>{mData._new?"Ajouter":"Modifier"}</div><button onClick={()=>setModal(null)} style={S.xBtn}>×</button></div>
          <div style={S.fGrd}>
            <div style={{gridColumn:"1/-1",fontSize:10,fontWeight:800,color:"#388bfd",textTransform:"uppercase",letterSpacing:.5}}>👤 Identité & rôle</div>
            <FF l="Nom" v={mData.nom} c={v=>setMData(p=>({...p,nom:v}))}/>
            <FF l="Prénom" v={mData.prenom} c={v=>setMData(p=>({...p,prenom:v}))}/>
            <FF l="Initiales (max 4)" v={mData.init} c={v=>setMData(p=>({...p,init:v.toUpperCase().slice(0,4)}))}/>
            <div><label style={S.fl}>Couleur</label><input type="color" value={mData.color} onChange={e=>setMData(p=>({...p,color:e.target.value}))} style={{...S.fi,padding:2,height:32,cursor:"pointer"}}/></div>
            <div style={{gridColumn:"1/-1"}}><label style={S.fl}>Rôle</label>
              <div style={{display:"flex",gap:5}}>{[["medecin","Médecin"],["attache","Attaché"],["ide","IDE"]].map(([v,l])=><button key={v} onClick={()=>setMData(p=>({...p,role:v,garde:["attache","ide"].includes(v)?false:p.garde,tourMed:["attache","ide"].includes(v)?false:p.tourMed}))} style={{flex:1,padding:"6px",borderRadius:6,border:"none",cursor:"pointer",fontWeight:700,fontSize:12,background:(mData.role||"medecin")===v?"#1d4ed8":"var(--bg2)",color:(mData.role||"medecin")===v?"#fff":"var(--txt2)"}}>{l}</button>)}</div>
            </div>
            {(mData.role||"medecin")==="medecin"&&<div style={{gridColumn:"1/-1",borderTop:"1px solid var(--border)",marginTop:8,paddingTop:8,fontSize:10,fontWeight:800,color:"#388bfd",textTransform:"uppercase",letterSpacing:.5}}>✅ Participations</div>}
            {(mData.role||"medecin")==="medecin"&&<div style={{gridColumn:"1/-1",display:"flex",gap:16,flexWrap:"wrap"}}>
              <label style={{display:"flex",gap:6,alignItems:"center",color:"var(--txt2)",fontSize:13,cursor:"pointer"}}><input type="checkbox" checked={mData.garde} onChange={e=>setMData(p=>({...p,garde:e.target.checked}))} style={{width:14,height:14}}/>Gardes</label>
              <label style={{display:"flex",gap:6,alignItems:"center",color:"var(--txt2)",fontSize:13,cursor:"pointer"}}><input type="checkbox" checked={mData.tourMed} onChange={e=>setMData(p=>({...p,tourMed:e.target.checked}))} style={{width:14,height:14}}/>Tour médical</label>
              <label style={{display:"flex",gap:6,alignItems:"center",color:"var(--txt2)",fontSize:13,cursor:"pointer"}}><input type="checkbox" checked={!!mData.astreinte} onChange={e=>setMData(p=>({...p,astreinte:e.target.checked}))} style={{width:14,height:14}}/>Astreinte rythmo</label>
            </div>}
            {(mData.role||"medecin")==="medecin"&&<div style={{gridColumn:"1/-1",borderTop:"1px solid var(--border)",marginTop:8,paddingTop:8,fontSize:10,fontWeight:800,color:"#388bfd",textTransform:"uppercase",letterSpacing:.5}}>⚙️ Statut & options</div>}
            {(mData.role||"medecin")==="medecin"&&<div style={{gridColumn:"1/-1"}}>
              <label style={{fontSize:10,color:"var(--txt3)",fontWeight:700,textTransform:"uppercase",display:"block",marginBottom:4}}>Statut</label>
              <div style={{display:"flex",gap:4}}>
                {[["senior","Sénior"],["junior","Junior"]].map(([v,l])=><button key={v} onClick={()=>setMData(p=>({...p,statut:v}))} style={{padding:"4px 10px",borderRadius:6,border:"none",cursor:"pointer",fontWeight:700,fontSize:11,background:(mData.statut||"senior")===v?"#1d4ed8":"var(--bg2)",color:(mData.statut||"senior")===v?"#fff":"var(--txt2)"}}>{l}</button>)}
              </div>
              {mData.tourMed&&<div style={{display:"flex",gap:10,alignItems:"center",marginTop:8,flexWrap:"wrap"}}>
                <span style={{fontSize:13,color:"var(--txt2)"}}>2 semaines de tour consécutives :</span>
                <label style={{display:"flex",gap:5,alignItems:"center",color:"var(--txt2)",fontSize:13,cursor:"pointer"}}><input type="checkbox" checked={!!mData.pref2HC} onChange={e=>setMData(p=>({...p,pref2HC:e.target.checked}))} style={{width:14,height:14}}/>HC</label>
                <label style={{display:"flex",gap:5,alignItems:"center",color:"var(--txt2)",fontSize:13,cursor:"pointer"}}><input type="checkbox" checked={!!mData.pref2USIC} onChange={e=>setMData(p=>({...p,pref2USIC:e.target.checked}))} style={{width:14,height:14}}/>USIC</label>
              </div>}
              <div style={{display:"flex",gap:8,alignItems:"center",marginTop:8,flexWrap:"wrap"}}>
                <label style={{display:"flex",gap:5,alignItems:"center",color:"var(--txt2)",fontSize:13,cursor:"pointer"}}>
                  <input type="checkbox" checked={!!mData.partTime} onChange={e=>setMData(p=>({...p,partTime:e.target.checked}))} style={{width:14,height:14}}/>
                  Temps partiel
                </label>
                {mData.partTime&&<span style={{fontSize:12,color:"var(--txt3)"}}>Jours travaillés :</span>}
                {mData.partTime&&[["1","Lun"],["2","Mar"],["3","Mer"],["4","Jeu"],["5","Ven"]].map(([dk,lb])=>(
                  <label key={dk} style={{display:"flex",gap:3,alignItems:"center",color:"var(--txt2)",fontSize:12,cursor:"pointer"}}>
                    <input type="checkbox" checked={(mData.workDays||{})[dk]!==false}
                      onChange={e=>setMData(p=>({...p,workDays:{...(p.workDays||{}),[dk]:e.target.checked}}))} style={{width:13,height:13}}/>
                    {lb}
                  </label>
                ))}
              </div>
              {mData.garde&&<div style={{display:"flex",gap:10,alignItems:"center",marginTop:8,flexWrap:"wrap"}}>
                <span style={{fontSize:13,color:"var(--txt2)"}}>Volume de gardes :</span>
                <select value={mData.gardeFactor||"normal"} onChange={e=>setMData(p=>({...p,gardeFactor:e.target.value}))}
                  style={{padding:"5px 8px",borderRadius:6,border:"1px solid var(--border)",background:"var(--inp)",color:"var(--txt)",fontSize:13}}>
                  <option value="less">Moins de gardes</option>
                  <option value="normal">Gardes moyennes</option>
                  <option value="more">Plus de gardes</option>
                </select>
              </div>}
              {mData.garde&&<div style={{display:"flex",gap:8,alignItems:"center",marginTop:8,flexWrap:"wrap"}}>
                <span style={{fontSize:13,color:"var(--txt2)"}}>Jours de garde possibles :</span>
                {[["1","Lun"],["2","Mar"],["3","Mer"],["4","Jeu"],["5","Ven"],["6","Sam"],["0","Dim"]].map(([dk,lb])=>(
                  <label key={dk} style={{display:"flex",gap:3,alignItems:"center",color:"var(--txt2)",fontSize:12,cursor:"pointer"}}>
                    <input type="checkbox" checked={(mData.gardeDays||{})[dk]!==false}
                      onChange={e=>setMData(p=>({...p,gardeDays:{...(p.gardeDays||{}),[dk]:e.target.checked}}))} style={{width:13,height:13}}/>
                    {lb}
                  </label>
                ))}
              </div>}
            </div>}
            {mData.role==="attache"&&<div style={{gridColumn:"1/-1",display:"flex",gap:16,flexWrap:"wrap"}}>
              <label style={{display:"flex",gap:6,alignItems:"center",color:"var(--txt2)",fontSize:13,cursor:"pointer"}}><input type="checkbox" checked={!!mData.astreinte} onChange={e=>setMData(p=>({...p,astreinte:e.target.checked}))} style={{width:14,height:14}}/>Astreinte rythmo</label>
            </div>}

            {(mData.role||"medecin")==="medecin"&&<div style={{gridColumn:"1/-1",borderTop:"1px solid var(--border)",marginTop:8,paddingTop:8,fontSize:10,fontWeight:800,color:"#388bfd",textTransform:"uppercase",letterSpacing:.5}}>🎯 Surspécialité (tour médical)</div>}
            {(mData.role||"medecin")==="medecin"&&<div style={{gridColumn:"1/-1"}}>
              <label style={{...S.fl,display:"none"}}>Surspécialité (Tour médical)</label>
              <div style={{display:"flex",gap:6,flexWrap:"wrap",marginTop:4}}>
                {[["coro","Coro","#76a5af"],["pace","Pace","#e3b341"],["eep","EEP","#f97316"],["ett","ETT","#ea9999"]].map(([v,l,c])=>(
                  <button key={v} onClick={()=>setMData(p=>({...p,surSpec:p.surSpec===v?null:v}))}
                    style={{padding:"5px 12px",borderRadius:6,border:"1px solid "+c,cursor:"pointer",fontWeight:700,fontSize:12,
                      background:mData.surSpec===v?c:"var(--bg2)",color:mData.surSpec===v?"#fff":c}}>
                    {l}
                  </button>
                ))}
              </div>
            </div>}
          </div>
          <button style={{...S.btnP,width:"100%",marginTop:10}} onClick={()=>{
            if(!mData.nom||!mData.init)return toast("Nom et initiales requis","warn");
            const {_new,...rest}=mData;
            if(_new)setMedecins(p=>[...p,rest]);else setMedecins(p=>p.map(m=>m.id===rest.id?rest:m));
            setModal(null);toast("Médecin enregistré");
          }}>Enregistrer</button>
        </Ov>
      )}

      {modal==="editMedActivites"&&mData&&(
        <Ov onClose={()=>setModal(null)}>
          <div style={S.mHd}><div><div style={S.mTit2}>🎯 Activités — {mData.prenom} {mData.nom}</div><div style={{fontSize:11,color:"var(--txt3)",marginTop:2}}>Cochez pour autoriser.</div></div><button onClick={()=>setModal(null)} style={S.xBtn}>×</button></div>
          <div style={{display:"flex",flexDirection:"column",gap:4,maxHeight:400,overflowY:"auto"}}>
            {actes.filter(a=>!a.isSystem).map(a=>{
              const allowed=!(a.medecinsAutorise&&a.medecinsAutorise.length)||a.medecinsAutorise.includes(mData.init);
              return(
                <label key={a.id} style={{display:"flex",alignItems:"center",gap:9,padding:"7px 10px",borderRadius:7,background:allowed?"var(--nav-act)":"var(--bg2)",border:"1px solid var(--border)",cursor:"pointer"}}>
                  <input type="checkbox" checked={allowed} onChange={e=>{
                    setActes(prev=>prev.map(act=>{
                      if(act.id!==a.id)return act;
                      const cur=act.medecinsAutorise||[];
                      if(e.target.checked){if(cur.length===0)return act;return{...act,medecinsAutorise:[...cur,mData.init]};}
                      else{if(cur.length===0){const all=medecins.map(m=>m.init).filter(i=>i!==mData.init);return{...act,medecinsAutorise:all};}return{...act,medecinsAutorise:cur.filter(i=>i!==mData.init)};}
                    }));
                  }} style={{width:15,height:15,cursor:"pointer"}}/>
                  <div style={{padding:"2px 6px",borderRadius:4,
                  background:a.color,
                  color:(()=>{try{const r=parseInt(a.color.slice(1,3),16)/255,g=parseInt(a.color.slice(3,5),16)/255,b=parseInt(a.color.slice(5,7),16)/255;const l=0.2126*(r<=0.04045?r/12.92:Math.pow((r+0.055)/1.055,2.4))+0.7152*(g<=0.04045?g/12.92:Math.pow((g+0.055)/1.055,2.4))+0.0722*(b<=0.04045?b/12.92:Math.pow((b+0.055)/1.055,2.4));return l>0.35?"#111":"#fff";}catch{return"#fff";}})(),
                  fontSize:10,fontWeight:800,fontFamily:"'JetBrains Mono',monospace",flexShrink:0}}>{a.short}</div>
                  <span style={{fontSize:12,color:"var(--txt)",fontWeight:allowed?600:400,flex:1}}>{a.label}</span>
                  {!(a.medecinsAutorise&&a.medecinsAutorise.length)&&<span style={{fontSize:9,color:"var(--txt3)"}}>tous</span>}
                </label>
              );
            })}
          </div>
          <button style={{...S.btnP,width:"100%",marginTop:10}} onClick={()=>setModal(null)}>Fermer</button>
        </Ov>
      )}

    </div>
  );
}
