const { useState, useEffect, useCallback, useMemo, useRef } = React;
// Firebase injected via window (loaded separately in index.html)
// In CodeSandbox: data is kept in memory only (no persistence)
// In production (Netlify): Firebase syncs automatically
const db = typeof window !== "undefined" && window.firebaseDB ? window.firebaseDB : null;
const PLANNING_DOC = db && window.firebaseDoc ? window.firebaseDoc(db, "planning", "main") : null;
const setDoc = typeof window !== "undefined" && window.firebaseSetDoc ? window.firebaseSetDoc : null;
const onSnapshot = typeof window !== "undefined" && window.firebaseOnSnapshot ? window.firebaseOnSnapshot : null;
const updatePaths = typeof window !== "undefined" && window.firebaseUpdatePaths ? window.firebaseUpdatePaths : null;

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
const APP_VERSION="v10.114 — 25/08/2026";
/* ════ PÉRIODE GLOBALE (configurable dans Paramètres) ════ */
let PCFG={len:4,startM:6}; // défaut: 4 mois à partir de Juillet
/* v10.18 : les vacances scolaires deviennent une donnée SAISIE, plus téléchargée. Le
   téléchargement était instable (4 sources, souvent toutes en échec) et surtout ASYNCHRONE :
   faire dépendre les bornes de période d'une donnée qui arrive après coup les aurait rendues
   changeantes en cours d'usage — inacceptable pour un calcul qui décide aussi jusqu'où va
   un retrait sur période. Ici la liste est locale et immédiate, donc identique à chaque
   chargement. VAC_LIST est tenue à jour depuis l'état React, comme PCFG. */
let VAC_LIST=[];        // [{an,nom,d1,d2}] — d1/d2 au format AAAA-MM-JJ
let VAC_RULE=false;     // étendre la période jusqu'à la fin des vacances
const VAC_NOMS=["Toussaint","Noël","Hiver","Printemps","Été"];
function vacContient(dt){
  const k=dt.getFullYear()+"-"+String(dt.getMonth()+1).padStart(2,"0")+"-"+String(dt.getDate()).padStart(2,"0");
  return VAC_LIST.find(v=>v.d1&&v.d2&&k>=v.d1&&k<=v.d2)||null;
}
function perStart(y,m){
  const d=((m-PCFG.startM)%12+12)%12;
  const off=d%PCFG.len;
  let sm=m-off,sy=y;
  if(sm<0){sm+=12;sy--;}
  return{sy,sm};
}
function perNext(sy,sm){const t=sm+PCFG.len;return{sy:t>11?sy+1:sy,sm:t%12};}
function perPrev(sy,sm){const t=sm-PCFG.len;return{sy:t<0?sy-1:sy,sm:(t+12)%12};}
// ── Règle "semaines complètes" : la période s'étend jusqu'au dimanche qui clôt la dernière semaine,
//    puis inclut le lundi suivant s'il est férié (ex. 1er novembre). La période suivante démarre le lendemain.
function perEnd(sy,sm){
  const t=sm+PCFG.len-1;const em=t%12,ey=t>11?sy+1:sy;
  const dt=new Date(ey,em+1,0); // dernier jour du dernier mois
  while(dt.getDay()!==0)dt.setDate(dt.getDate()+1); // → dimanche
  const mon=new Date(dt);mon.setDate(mon.getDate()+1);
  if(isFerie(mon.getFullYear(),mon.getMonth(),mon.getDate()))dt=mon;
  /* v10.18 : si cette fin tombe AU MILIEU de vacances, on va jusqu'à leur dernier jour.
     La période suivante démarre le lendemain (perDaysList part de la fin précédente + 1),
     donc ni chevauchement ni trou. On n'étend jamais quand les vacances commencent APRÈS. */
  if(VAC_RULE){
    const v=vacContient(dt);
    if(v){
      const f=new Date(v.d2+"T00:00:00");
      /* Limite de 21 jours : les congés d'hiver ou de printemps durent 15 jours et sont
         donc absorbés, mais PAS l'été. Sans elle, une période finissant le 4 juillet —
         premier week-end des grandes vacances — s'étendrait jusqu'à fin août. */
      if(f>dt&&(f-dt)<=21*86400000)return f;
    }
  }
  return dt;
}
function perDaysList(sy,sm){
  const pv=perPrev(sy,sm);
  const start=new Date(perEnd(pv.sy,pv.sm));start.setDate(start.getDate()+1);
  const end=perEnd(sy,sm);
  const days=[];
  for(let dt=new Date(start);dt<=end;dt.setDate(dt.getDate()+1))days.push({y:dt.getFullYear(),m:dt.getMonth(),d:dt.getDate()});
  return days;
}
/* v10.109 — LES SEMAINES D'UNE PERIODE. Sa regle du 24/08/2026, deux decoupages
   assumes : une PERIODE va jusqu'au dernier dimanche, ou au lundi suivant s'il est
   ferie ; le PLANNING TYPE et le TOUR, eux, se repartissent en SEMAINES COMPLETES —
   du lundi qui precede ou egale le premier jour au dimanche qui precede ou egale le
   dernier. Quand un lundi ferie est rattache a la periode precedente (1er novembre
   2027), la semaine de ce lundi est donc la PREMIERE de la periode suivante : c'est
   ce qu'il veut, le lundi etant ferie — « la semaine de tour va commencer a se
   repartir le mardi ». Verifie sur 12 periodes (2026->2030) : aucune semaine
   partagee, aucune oubliee. Ecrit en ES5 pur : texte identique dans les 2 fichiers.
   La cle est celle de wKey — mois TECHNIQUE, sans zero de tete. */
function perWeeksList(sy,sm){
  var l=perDaysList(sy,sm);
  if(!l.length)return[];
  var a=new Date(l[0].y,l[0].m,l[0].d);
  var b=new Date(l[l.length-1].y,l[l.length-1].m,l[l.length-1].d);
  while(a.getDay()!==1)a.setDate(a.getDate()-1);
  while(b.getDay()!==0)b.setDate(b.getDate()-1);
  var out=[],cur=new Date(a);
  while(cur<=b){
    out.push({key:cur.getFullYear()+"-"+cur.getMonth()+"-"+cur.getDate(),label:cur.getDate()+" "+MOIS[cur.getMonth()].slice(0,4)});
    cur.setDate(cur.getDate()+7);
  }
  return out;
}
const SYS=["GARDE","REPOS_GARDE","TOUR_HC","TOUR_USIC","ABSENCE"];
/* v9.64 : activités EXCLUSIVES — jamais en cohabitation dans une case. Soit l'une
   d'elles est posée et c'est la seule entrée, soit elle n'y est pas. La liste est
   définie UNE FOIS ; sept protections divergentes l'utilisaient chacune à sa façon,
   et la Formation manquait dans plusieurs — c'est ainsi qu'une FMC a pu être écrasée
   par la réapplication du planning type et effacée par son retrait. */
const ABS_IDS=["ABSENCE","FORM","FORMATION"];   /* v9.86 : « absent ou en formation », défini UNE fois — 14 copies éparpillées dans 5 composants, la famille exacte qui avait fait disparaître une FMC */
const EXCL_IDS=["ABSENCE","FORM","FORMATION","GARDE","REPOS_GARDE","TP"];
const PROT_BASE=EXCL_IDS;                      // noyau protégé par TOUS les outils
const PROT_TOUR=EXCL_IDS.concat(["TOUR_HC","TOUR_USIC"]); // + tour réel (remplaçants)
const EXCL_LABEL={ABSENCE:"une absence",FORM:"une formation",FORMATION:"une formation",GARDE:"une garde",REPOS_GARDE:"un repos de garde",TP:"un temps partiel"};
/* v9.75 : ne jamais étaler un Set avec la syntaxe des trois points. Compilé pour la
   cible ES5 sans l'option downlevelIteration, cela devient __spreadArray([], new Set(x),
   true), qui rend un tableau VIDE — un ensemble n'ayant ni longueur ni index. Le fichier
   lisible marchait, le fichier exécuté renvoyait du vide, en silence. D'où ce helper. */
const uniqArr=(a)=>(a||[]).filter((v,i,arr)=>arr.indexOf(v)===i);
const BK_KEEP=45;   /* nombre de sauvegardes automatiques conservées */
const cellEs=c=>c?(Array.isArray(c)?c:[c]):[];
const cellHasAny=(c,ids)=>cellEs(c).some(e=>e&&ids.includes(e.acteId));
/* v9.73 : retire d'une case les seules entrées visées et rend ce qu'il reste (null si
   plus rien). Quinze endroits lisaient la PREMIÈRE entrée puis supprimaient la case
   ENTIÈRE : sûr tant qu'une garde ou un tour y est forcément seul, mais faux dès qu'une
   activité les accompagnerait — et la suppression emportait alors aussi cette activité. */
const cellDrop=(c,ids)=>{const r=cellEs(c).filter(e=>e&&!ids.includes(e.acteId));return r.length?(r.length===1?r[0]:r):null;};
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
/* v9.55 : les colonnes de PT Cardio sont TOUTES ordonnables. Les six historiques,
   jusque-là écrites en dur dans le rendu, deviennent des données porteuses d'une clé ;
   les autres prennent la clé de leur activité. L'ordre est un simple tableau de clés
   partagé par toute l'équipe (champ Firestore ptOrder) : ce qui n'y figure pas garde
   son rang naturel À LA FIN, donc une activité nouvellement cochée « PT Cardio »
   apparaît en dernier sans migration ni réglage. */
const PT_FIXED_ROWS=[
  {key:"ROW_STIM",label:"Salle-Stim",ids:["STIM","STIM_AG","EEP_AG"],color:"#e3b341",salle:S_STIM,multiActe:true},
  {key:"ROW_EEP",label:"Salle-EEP",ids:["EEP"],color:"#f472b6",salle:S_EEP,multiActe:true},
  {key:"ROW_DOBU",label:"Dobu",ids:["DOBU"],color:"#60a5fa",salle:null,hasSalleChoice:true,sallesDisp:["CHL-4","CHL-5"]},
  {key:"ROW_ETO",label:"ETO",ids:["ETO_CHL"],color:"#2dd4bf",salle:null,hasSalleChoice:true,sallesDisp:SALLES_CHL},
  {key:"ROW_REVEAL",label:"Reveal",ids:["REVEAL"],color:"#818cf8",salle:null,hasSalleChoice:true,sallesDisp:SALLES_CHL},
  {key:"ROW_EECHL",label:"EE CHL",ids:["EE_CHL"],color:"#4ade80",salle:S_EE_CHL},
];

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
  {id:"CS_CHL",label:"Consultation CHL",short:"CsL",color:"#c9daf8",bg:"#388bfd",hasSalle:true,salles:SALLES_CHL,isSystem:false,site:"CHL",medecinsAutorise:["MP","VA","BS","HV","TOM","NH","CV","TH","CBV","JSL","TD","ND","JSS","PM","MG","CB","AB","SD","YL","MCD","BF"],csReport:true,adminOk:true,maxParSalle:1},
  {id:"ETT_CHL",label:"ETT",short:"ETT",color:"#ea9999",bg:"#ea9999",hasSalle:true,salles:SALLES_CHL,isSystem:false,site:"CHL",medecinsAutorise:["MP","VA","BS","HV","TOM","NH","CV","TH","CBV","JSL","TD","ND","JSS","PM","MG","CB","AB"],maxParSalle:1},
  {id:"ETO_CHL",label:"ETO",short:"ETO",color:"#46bdc6",bg:"#46bdc6",hasSalle:true,salles:SALLES_CHL,isSystem:false,site:"CHL",medecinsAutorise:GRP.ETO,csReport:true,adminOk:true,maxParSalle:1},
  {id:"DOBU",label:"Dobutamine",short:"Dobu",color:"#46bdc6",bg:"#46bdc6",hasSalle:true,salles:["CHL-4","CHL-5"],isSystem:false,site:"CHL",medecinsAutorise:GRP.DOBU,csReport:true,adminOk:true,maxParSalle:1},
  {id:"PM_CS",label:"Cs Pacemaker",short:"CsPM",color:"#c9daf8",bg:"#c9daf8",hasSalle:true,salles:SALLES_CHL,isSystem:false,site:"CHL",medecinsAutorise:GRP.PM_CS,csReport:true,adminOk:true,maxParSalle:1},
  {id:"DEFIB_CS",label:"Cs DAI",short:"CsDAI",color:"#c9daf8",bg:"#c9daf8",hasSalle:true,salles:SALLES_CHL,isSystem:false,site:"CHL",medecinsAutorise:GRP.DEFIB,csReport:true,adminOk:true,maxParSalle:1},
  {id:"REVEAL",label:"Reveal",short:"Reveal",color:"#e3b341",bg:"#e3b341",hasSalle:true,salles:SALLES_CHL,isSystem:false,site:"CHL",medecinsAutorise:GRP.REVEAL,maxParSalle:1},
  {id:"VASC_CHL",label:"Vasculaire CHL",short:"Vasc",color:"#94a3b8",bg:"#94a3b8",hasSalle:true,salles:SALLES_CHL,isSystem:false,site:"CHL",medecinsAutorise:GRP.VASC_CHL,maxParSalle:1},
  {id:"EE_CHL",label:"Épreuve effort CHL",short:"EE",color:"#4ade80",bg:"#4ade80",hasSalle:true,salles:[S_EE_CHL],isSystem:false,site:"CHL",medecinsAutorise:["VA","BS","HV","TOM","NH","CV","TH","CBV","JSL","TD","ND","JSS","PM","MG","CB","AB","BL"],fixedSalle:S_EE_CHL,maxParSalle:1},
  {id:"CS_CHB",label:"Consultation CHB",short:"CsB",color:"#b4a7d6",bg:"#b4a7d6",hasSalle:true,salles:["CHB-1","CHB-2","CHB-3"],isSystem:false,site:"CHB",medecinsAutorise:["BS","HV","TOM","NH","CV","TH","CBV","JSL","TD","ND","JSS","PM","MG","CB","AB"],csReport:true,adminOk:true,maxParSalle:1},
  {id:"CARDIOPEDS",label:"Cardiopédiatrie",short:"Pédia",color:"#f9a8d4",bg:"#f9a8d4",hasSalle:true,salles:["CHB-1","CHB-2","CHB-3"],isSystem:false,site:"CHB",medecinsAutorise:GRP.CARDIOPEDS,maxParSalle:1},
  {id:"VASC_CHB2",label:"Vasculaire CHB",short:"Vasc",color:"#64748b",bg:"#64748b",hasSalle:true,salles:["CHB-VASC","CHB-3"],isSystem:false,site:"CHB",medecinsAutorise:GRP.VASC_CHL,fixedSalle:"CHB-VASC",maxParSalle:1},
  {id:"EE_CHB",label:"Réadaptation cardiaque",short:"Réab",color:"#b4a7d6",bg:"#b4a7d6",hasSalle:true,salles:[S_EE_CHB],isSystem:false,site:"CHB",medecinsAutorise:GRP.EE_CHB,fixedSalle:S_EE_CHB,maxParSalle:1},
  {id:"RYTHMO_CHB",label:"Rythmologie CHB",short:"CsPM",color:"#b4a7d6",bg:"#b4a7d6",hasSalle:true,salles:["Rythmo-CHB"],isSystem:false,site:"CHB",medecinsAutorise:GRP.RYTHMO,csReport:true,adminOk:true,maxParSalle:1},
  {id:"DOBU_CHB",label:"Dobu/ETO CHB",short:"Dobu",color:"#6db8c4",bg:"#6db8c4",hasSalle:true,salles:["CHB-1","CHB-2"],isSystem:false,site:"CHB",medecinsAutorise:["JSS","PM","CB","AB"],csReport:true,adminOk:true,maxParSalle:1},
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
/* v9.79 : une salle portait UNE seule étiquette servant à la fois de LIEU (CHL, CHB) et
   d'ONGLET d'affichage (PT Angio, PT Cardio) — deux notions de nature différente au même
   endroit. Conséquence : la liste des salles d'une activité, filtrée par le site, masquait
   toute salle étiquetée PT Angio ou PT Cardio. D'où sept activités (Coro, Tavi, FOP/FAG,
   Stim, StimAG, EEP, EEP AG) dont les salles existaient sans être modifiables.
   Désormais : `site` = lieu physique (CHL ou CHB), `s` = onglets d'apparition. */
const salleSite=(x)=>{
  if(!x)return "CHL";
  if(x.site==="CHL"||x.site==="CHB")return x.site;
  const t=Array.isArray(x.s)?x.s:(x.s?[x.s]:[]);
  return t.indexOf("CHB")>=0?"CHB":"CHL";   // Angio, Stim et EEP sont à Lens
};
const HDR_H=50;   /* v9.87 : hauteur de la barre de navigation — les en-têtes des tableaux se figent juste en dessous, par rapport à l'écran */
const SPEC_COLORS_DEF={coro:"#76a5af",pace:"#e3b341",eep:"#8b5cf6",ett:"#ec4899"};
const SPEC_LIST=[["coro","Coro"],["pace","Pace"],["eep","EEP"],["ett","ETT"]];
const acteRecapIn=(a,site)=>{if(!a)return false;const arr=a.recapSites||[];return arr.includes(site)||a.recapSite===site||(site==="PLATEAU"&&!!a.ptCardio);};
/* ════ THEME ════ */
function applyTheme(dark){
  const r=document.documentElement;
  if(dark){
    r.style.setProperty("--bg","#1a1f2e");r.style.setProperty("--bg2","#242938");
    r.style.setProperty("--bg-n","#141720");r.style.setProperty("--bg-we","#1f1a0e");
    r.style.setProperty("--vac-bg","#2a3040");r.style.setProperty("--garde-bg","#0f2318");
    r.style.setProperty("--ast-bg","#173a24");r.style.setProperty("--ast-bord","#4ade80");
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
/* ── v9.38 : porteur réservé des activités sans médecin (holters, télé-suivi).
   Ce n'est pas un membre de l'équipe : il ne figure pas dans `medecins`, il sert
   uniquement de clé de rangement dans le plan, ce qui fait hériter ces activités
   de la synchro delta, du journal et des sauvegardes sans code supplémentaire. */
/* ── v9.42 : dans PT Cardio, une case se lit PAR SALLE. Le nombre d'IDE et le
   départ différé qualifient la salle, pas le médecin qui l'occupe : deux
   médecins dans la même salle ne réclament donc qu'un seul effectif. */
const salleGroups=(row,occ)=>{
  const groups=[],idx={};
  (occ||[]).forEach(o=>{
    const k=(o.salle||"")+"|"+((o.acte&&o.acte.id)||"");
    if(idx[k]===undefined){idx[k]=groups.length;groups.push({salle:o.salle||null,acte:o.acte||{},meds:[],dif:null,n:null});}
    const g=groups[idx[k]];
    g.meds.push(o.med);
    if(o.dif&&!g.dif)g.dif=o.dif;
    if(o.n!==null&&o.n!==undefined)g.n=o.n;
  });
  return groups;
};

const IDE_MED={id:"IDE_STAFF",init:"🩺",nom:"IDE",prenom:"",color:"#3fb950"};
/* v9.41 : Firestore REFUSE tout nom de champ de la forme __xxx__ (motif réservé),
   y compris pour les clés de map imbriquées. Comme les identifiants de médecin
   servent de clés dans planV2, un identifiant ainsi encadré faisait échouer
   l'écriture de TOUTE la case — et le repli échouait pareil, sans bruit.
   Ce garde-fou renomme au vol une éventuelle clé réservée avant l'envoi. */
const fbSafeCell=(cell)=>{
  if(!cell||typeof cell!=="object")return cell;
  let ch=false;const o={};
  Object.keys(cell).forEach(k=>{
    const k2=/^__.+__$/.test(k)?(k==="__IDE__"?"IDE_STAFF":k.slice(2,-2)):k;
    if(k2!==k)ch=true;
    o[k2]=cell[k];
  });
  return ch?o:cell;
};

/* ── v9.40 : impression d'une semaine ──
   On n'imprime pas un rendu parallèle mais LES VRAIES VUES, filtrées sur la
   semaine choisie : la règle de calcul des IDE n'est ainsi écrite qu'une fois. */
const inPrintWeek=(pw,y,m,d)=>{
  if(!pw)return true;
  const a=new Date(pw.y,pw.m,pw.d);a.setHours(0,0,0,0);
  const b=new Date(y,m,d);b.setHours(0,0,0,0);
  const k=Math.round((b-a)/86400000);
  return k>=0&&k<=6;
};
/* v9.48 : la portée d'impression n'est plus seulement une semaine.
   {k:"w",y,m,d} une semaine · {k:"m",y,m} un mois · {k:"p"} la période entière. */
const inPrintRange=(pr,y,m,d)=>{
  if(!pr)return true;
  if(pr.k==="m")return y===pr.y&&m===pr.m;
  if(pr.k==="p")return true;
  return inPrintWeek(pr,y,m,d);
};
const mondayOf=(y,m,d)=>{const t=new Date(y,m,d);const mo=new Date(y,m,d-((t.getDay()+6)%7));return{y:mo.getFullYear(),m:mo.getMonth(),d:mo.getDate()};};
const printWeekList=(y,m)=>{
  const p=perStart(y,m),out=[],seen={};
  perDaysList(p.sy,p.sm).forEach(o=>{
    const w=mondayOf(o.y,o.m,o.d),k=w.y+"-"+w.m+"-"+w.d;
    if(!seen[k]){seen[k]=1;out.push(w);}
  });
  return out;
};

const S={
  app:{minHeight:"100vh",background:"var(--bg)",fontFamily:"'Sora','Segoe UI',sans-serif",color:"var(--txt)"},
  hdr:{background:"var(--hdr)",borderBottom:"1px solid var(--border)",padding:"0 10px",display:"flex",alignItems:"center",height:HDR_H,position:"sticky",top:0,zIndex:100,gap:6},
  nav:{display:"flex",gap:1,flex:1,overflowX:"auto",flexWrap:"nowrap",WebkitOverflowScrolling:"touch"},
  nb:{padding:"4px 9px",borderRadius:6,border:"none",background:"transparent",cursor:"pointer",fontSize:11,fontWeight:500,color:"rgba(255,255,255,.65)",whiteSpace:"nowrap",flexShrink:0},
  nba:{background:"var(--nav-act)",color:"var(--nav-act-c)",fontWeight:700},
  mTit:{fontSize:16,fontWeight:800,margin:0,color:"var(--txt)"},
  arr:{width:26,height:26,borderRadius:6,border:"1px solid var(--border)",background:"var(--bg2)",cursor:"pointer",fontSize:14,color:"var(--txt2)"},
  oriTog:{display:"flex",background:"var(--bg2)",borderRadius:6,padding:2,gap:1,border:"1px solid var(--border)"},
  oriB:{padding:"3px 7px",borderRadius:4,border:"none",background:"transparent",color:"var(--txt2)",cursor:"pointer",fontSize:10,fontWeight:600},
  oriBa:{background:"#1d4ed8",color:"#fff"},
  main:{padding:"10px 10px 110px",maxWidth:1900,margin:"0 auto"}   /* v10.45 : le bandeau du PIN ne masque plus le bas */,
  bar:{display:"flex",alignItems:"center",marginBottom:10,gap:7},
  thFix:{padding:"5px 9px",background:"var(--th)",fontWeight:700,fontSize:10,color:"var(--txt2)",textTransform:"uppercase",letterSpacing:.4,borderRight:"2px solid var(--border)",whiteSpace:"nowrap"},
  th:{padding:"3px 2px",textAlign:"center",background:"var(--th)",fontSize:10,color:"var(--txt2)",minWidth:30,borderRight:"1px solid var(--border)",borderBottom:"1px solid var(--border)"},
  thWE:{background:"var(--bg-weh)"},thTD:{background:"var(--bg-td)",color:"var(--today-c)"},
  thN:{fontSize:12,fontWeight:800,color:"var(--txt)"},thJ:{fontSize:7,color:"var(--txt3)",textTransform:"uppercase"},
  tdFix:{padding:"3px 8px",background:"var(--td-fix)",borderRight:"2px solid var(--border)",verticalAlign:"middle"},
  td:{padding:"0",textAlign:"center",verticalAlign:"top",minWidth:30,borderRight:"1px solid var(--border2)",background:"var(--bg2)",position:"relative"},
  tdWE:{background:"var(--bg-we)",height:28,maxHeight:28,overflow:"hidden"},tdN:{background:"var(--bg-n)"},
  tdConfl:{background:"#fee2e2",outline:"1px solid #ef4444"},
  av:{width:28,height:28,borderRadius:"50%",display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:10,fontWeight:800,flexShrink:0},
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
/* v9.54 : pastille d'activité BORDÉE des 4 onglets salles (CHL, CHB, PT Cardio, PT Angio).
   Bord = couleur de l'activité assombrie de 12 %, texte = la même assombrie de 62 % ;
   en mode nuit, fond très sombre teinté et texte éclairci de 55 %. Le fond est OPAQUE :
   posé sur une case rouge il ne vire pas, contrairement à un rgba.
   L'onglet Planning et l'onglet Attachés gardent volontairement leurs pastilles PLEINES. */
const _hx=c=>{c=String(c||"#888888").replace("#","");return [parseInt(c.slice(0,2),16)||0,parseInt(c.slice(2,4),16)||0,parseInt(c.slice(4,6),16)||0];};
const mixC=(c,t,k)=>{const a=_hx(c),b=_hx(t);return "#"+[0,1,2].map(i=>Math.round(a[i]+(b[i]-a[i])*k).toString(16).padStart(2,"0")).join("");};
const pillCols=(c,night)=>{
  /* v10.14 : pastille PLEINE, comme dans l'onglet Planning — la couleur se lit d'un coup
     d'œil au lieu de demander à l'œil de s'arrêter sur un contour. La couleur du texte
     suit la LUMINOSITÉ du fond (fonction hexToLum déjà utilisée pour le choix des
     activités), donc elle reste lisible quelles que soient les couleurs choisies. */
  const bg=night?mixC(c,"#0d1117",.30):c;
  /* on ne fixe pas un seuil arbitraire : on retient des deux textes possibles celui qui
     CONTRASTE le mieux avec le fond, ce qui reste juste quelles que soient les couleurs */
  const L=hexToLum(bg), sombre=mixC(bg,"#000000",.80);
  const ct=(a,b)=>(Math.max(a,b)+0.05)/(Math.min(a,b)+0.05);
  const txt=ct(L,hexToLum("#ffffff"))>=ct(L,hexToLum(sombre))?"#ffffff":sombre;
  return {border:"1px solid "+mixC(bg,"#000000",.18),background:bg,color:txt};
};
/* fond rouge des cases à deux activités : le pointillé y prend sa couleur propre,
   celle de bordure générale étant invisible sur ce fond (surtout en mode nuit) */
const conflBg=night=>({background:night?"rgba(239,68,68,.16)":"#fee2e2",outline:"1px solid #ef4444"});
const conflSep=night=>night?"#f87171":"#b91c1c";
/* v9.56 — CHOIX OUVERT (étape 1/4).
   Une case de planning type porte soit UNE activité ferme, soit 2 à 3 branches
   entre lesquelles le choix n'est pas encore fait. À l'application, chaque branche
   d'un choix ouvert est marquée `cond:1` — un champ porté par l'entrée, donc qui
   hérite de la synchro en delta, du journal et des sauvegardes sans code.
   Affichage : cadre pointillé violet, branches EMPILÉES. En grille, la largeur se
   paie sur toutes les colonnes de médecins ; la hauteur, seulement sur les rares
   lignes concernées. Violet fixe et non variable de thème : il tient sur les deux. */
const COND_C="#a371f7", COND_BG="rgba(163,113,247,.12)";
/* v9.57 — CHOIX OUVERT (étape 2/4) : les branches non tranchées d'un créneau.
   Un praticien en choix ouvert reste DISPONIBLE, mais seulement pour ses propres
   branches — et ses branches n'occupent aucune salle et ne consomment aucune IDE
   tant que le choix n'est pas fait. */
const condOn=(getEntries,medId,y,m,d,slot)=>{
  const check=slot==="N"?["N","JOUR"]:slot==="JOUR"?["JOUR","M","AM"]:[slot,"JOUR"];
  const out=[];
  check.forEach(sl=>(getEntries(medId,y,m,d,sl)||[]).forEach(e=>{
    if(e&&e.acteId&&e.cond&&out.indexOf(e.acteId)<0)out.push(e.acteId);
  }));
  return out;
};

const ptCell=(a1,s1,a2,s2,a3,s3,c1)=>{
  const brs=[[a1,s1],[a2,s2],[a3,s3]].filter(b=>b[0]);
  if(!brs.length)return null;
  /* v9.68 : c1 (7e élément du planning type) marque une activité SEULE comme choix
     ouvert « en attente » — même comportement qu'à 2 ou 3 branches (v9.62). */
  if(brs.length===1)return c1?{acteId:brs[0][0],salle:brs[0][1]||null,cond:1}:{acteId:brs[0][0],salle:brs[0][1]||null};
  return brs.map(b=>({acteId:b[0],salle:b[1]||null,cond:1}));
};
function CondBadges({es,acteById,noteT}){
  const firm=(es||[]).filter(e=>e&&e.acteId&&!e.cond);
  const cond=(es||[]).filter(e=>e&&e.acteId&&e.cond);
  return(<>
    {firm.map((e,i)=>{const a=acteById(e.acteId);return a?<Badge key={"f"+i} a={a} salle={e.salle} hideSalle={true} hasNote={!!noteT}/>:null;})}
    {cond.length>0&&<span title={"Choix ouvert — "+cond.map(e=>{const a=acteById(e.acteId);return a?a.short:e.acteId;}).join(" ou ")}
      style={{display:"inline-flex",flexDirection:"column",alignItems:"center",gap:1,border:"1.5px dashed "+COND_C,borderRadius:6,padding:"2px 3px",background:COND_BG}}>
      {cond.map((e,i)=>{const a=acteById(e.acteId);if(!a)return null;
        return <span key={"c"+i} style={{display:"inline-flex",flexDirection:"column",alignItems:"center",gap:1}}>
          {i>0&&<span style={{fontSize:8,fontWeight:800,color:COND_C,lineHeight:1}}>ou</span>}
          <Badge a={a} salle={e.salle} hideSalle={true} hasNote={!!noteT}/>
        </span>;})}
    </span>}
  </>);
}

/* v10.15 : l'étiquette de SALLE. Elle était rendue à trois endroits avec des styles
   différents — fond blanc dans PT Angio et dans la colonne BIP, couleur de l'activité
   dans PT Cardio, et une taille plus petite pour le BIP. Un seul composant désormais :
   la salle prend TOUJOURS la couleur de l'activité qui l'occupe, à la même taille que
   la pastille d'activité. */
function SallePill({nom,acte,night}){
  if(!nom)return null;
  return(
    <span style={{...pillCols((acte&&acte.color)||"#888888",night),
      fontSize:10,fontWeight:800,fontFamily:"'JetBrains Mono',monospace",borderRadius:4,
      padding:"2px 3px",lineHeight:1.3,textAlign:"center",display:"inline-block",
      /* v10.16 : largeur ADAPTATIVE. Les 48 px figés dataient d'une police plus petite et ne
   tenaient plus que 6 caractères — « Angio-1 » et « CHB-BIP » se retrouvaient tronqués.
   On garde un minimum pour que les pastilles restent alignées entre elles, mais le nom
   long fait grandir la pastille au lieu d'être coupé. Vaut pour les 4 onglets et pour
   toute salle ou activité future au nom plus long. */
minWidth:48,maxWidth:"100%",overflow:"hidden",whiteSpace:"nowrap",textOverflow:"ellipsis"}}>{nom}</span>
  );
}

/* v10.18 : petits utilitaires du panneau « Vacances scolaires ». */
const fmtLong=(iso)=>{ if(!iso)return "—";
  const d=new Date(iso+"T00:00:00");
  return d.toLocaleDateString("fr-FR",{weekday:"long",day:"numeric",month:"long",year:"numeric"}); };
const fmtLongD=(d)=>d?d.toLocaleDateString("fr-FR",{weekday:"long",day:"numeric",month:"long",year:"numeric"}):"—";
const vacAnSuivante=(list)=>{
  const ans=list.map(v=>v.an).filter(Boolean).sort();
  if(!ans.length){const y=new Date().getFullYear();return y+"-"+(y+1);}
  const d=parseInt(String(ans[ans.length-1]).slice(0,4),10)+1;
  return d+"-"+(d+1);
};
const vacTerminee=(an)=>{
  /* une année scolaire est terminée quand son 31 août est passé */
  const d=parseInt(String(an||"").slice(0,4),10);
  if(!d)return false;
  return new Date()>new Date(d+1,7,31);
};
const vacOuvert=(o,an)=>o[an]!==undefined?o[an]:!vacTerminee(an);

const vacGroupes=(list)=>{
  const g={};
  list.forEach((v,idx)=>{(g[v.an||"?"]=g[v.an||"?"]||[]).push({v,idx});});
  return Object.keys(g).sort().map(an=>[an,g[an]]);
};

function ActPill({a,night,hasNote}){
  if(!a)return null;
  return(
    <div style={{position:"relative",display:"inline-block",margin:"1px"}}>
      <div style={{...pillCols(a.color||"#888888",night),fontSize:10,fontWeight:800,fontFamily:"'JetBrains Mono',monospace",
        borderRadius:4,padding:"2px 6px",lineHeight:1.3,textAlign:"center",
        /* v10.16 : largeur ADAPTATIVE. Les 48 px figés dataient d'une police plus petite et ne
   tenaient plus que 6 caractères — « Angio-1 » et « CHB-BIP » se retrouvaient tronqués.
   On garde un minimum pour que les pastilles restent alignées entre elles, mais le nom
   long fait grandir la pastille au lieu d'être coupé. Vaut pour les 4 onglets et pour
   toute salle ou activité future au nom plus long. */
minWidth:48,maxWidth:"100%",overflow:"hidden",whiteSpace:"nowrap",textOverflow:"ellipsis"}}>{a.short}</div>
      {hasNote&&<div style={{position:"absolute",top:-1,right:-1,width:6,height:6,borderRadius:"50%",background:"#f59e0b"}}/>}
    </div>
  );
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
/* v9.50 : bandeau des problèmes — partagé par le Planning et les Attachés,
   chacun avec SON propre relevé. Chaque ligne ouvre la case concernée. */
function IssuePanel({iss,open,setOpen,onGo}){
  if(!iss||(!iss.list.length&&!(iss.condList||[]).length))return null;
  const n=iss.list.length;
  const cL=iss.condList||[];
  const row=(it,i,col)=>(
    <button key={i} onClick={()=>onGo&&onGo(it)} title="Ouvrir cette case"
      style={{textAlign:"left",background:"none",border:"none",borderBottom:"1px dotted var(--border)",padding:"3px 2px",cursor:"pointer",fontSize:11,color:col||"var(--txt)",fontFamily:"inherit"}}>
      <b>{it.dw+" "+String(it.d).padStart(2,"0")+"/"+String(it.m+1).padStart(2,"0")+" "+it.sl}</b>{" — "}
      <b style={{color:it.med.color}}>{it.med.init}</b>{" — "+it.label}
    </button>
  );
  return(
  <>
    {cL.length>0&&(
      <div style={{background:COND_BG,border:"1.5px dashed "+COND_C,borderRadius:8,padding:"7px 11px",marginBottom:8}}>
        <div style={{display:"flex",alignItems:"center",gap:8,cursor:"pointer"}} onClick={()=>setOpen(v=>!v)}>
          <span style={{color:COND_C,fontWeight:800,fontSize:12}}>{"◇ "+cL.length+" choix ouvert"+(cL.length>1?"s":"")+" à trancher"}</span>
          <span style={{marginLeft:"auto",color:COND_C,fontSize:11,fontWeight:700}}>{open?"▲ replier":"▼ détail"}</span>
        </div>
        {open&&<div style={{marginTop:6,display:"flex",flexDirection:"column",gap:2}}>{cL.map((it,i)=>row(it,i,COND_C))}</div>}
      </div>
    )}
    {n>0&&
    <div style={{background:"rgba(248,81,73,.12)",border:"1px solid #f85149",borderRadius:8,padding:"7px 11px",marginBottom:8}}>
      <div style={{display:"flex",alignItems:"center",gap:8,cursor:"pointer"}} onClick={()=>setOpen(v=>!v)}>
        <span style={{color:"#f85149",fontWeight:800,fontSize:12}}>{"⚠ "+n+" créneau"+(n>1?"x":"")+" à revoir — "+iss.counts.salle+" sans salle · "+iss.counts.double+" double(s) · "+iss.counts.abs+" sur absence/repos"+(iss.counts.hop?" · "+iss.counts.hop+" sur deux hôpitaux":"")}</span>
        <span style={{marginLeft:"auto",color:"#f85149",fontSize:11,fontWeight:700}}>{open?"▲ replier":"▼ détail"}</span>
      </div>
      {open&&<div style={{marginTop:6,display:"flex",flexDirection:"column",gap:2}}>{iss.list.map((it,i)=>(
        <button key={i} onClick={()=>onGo&&onGo(it)} title="Ouvrir cette case"
          style={{textAlign:"left",background:"none",border:"none",borderBottom:"1px dotted var(--border)",padding:"3px 2px",cursor:"pointer",fontSize:11,color:"var(--txt)",fontFamily:"inherit"}}>
          <b>{it.dw+" "+String(it.d).padStart(2,"0")+"/"+String(it.m+1).padStart(2,"0")+" "+it.sl}</b>{" — "}
          <b style={{color:it.med.color}}>{it.med.init}</b>{" — "+it.label}
        </button>
      ))}</div>}
    </div>}
  </>
  );
}
function Av({med}){return <div style={{...S.av,background:med.color}}>{med.init}</div>;}
function Chp({bg,c,children}){return <span style={{fontSize:9,background:bg,color:c,padding:"1px 4px",borderRadius:3,fontWeight:700}}>{children}</span>;}
function Ov({children,onClose}){return <div style={S.ov} onClick={e=>{if(e.target===e.currentTarget)onClose();}}><div style={S.mb}>{children}</div></div>;}
function FF({l,v,c}){return <div><label style={S.fl}>{l}</label><input value={v} onChange={e=>c(e.target.value)} style={{...S.fi,width:"100%"}}/></div>;}
/* ════ GRID H ════ */
/* v10.12 : ces deux variables servent à distinguer un APPUI LONG (téléphone) d'un clic.
   Elles étaient utilisées sans avoir jamais été déclarées. Sur téléphone, `onTouchStart`
   s'exécute en premier et les crée implicitement, donc tout fonctionnait ; sur ORDINATEUR
   aucun événement tactile ne se produit, et `onClick` lisait une variable inexistante —
   ce qui interrompait le clic (ReferenceError) sans rien afficher. D'où : téléphone
   parfait, ordinateur muet, et clic droit intact puisqu'il ne les consulte pas. */
let _gvLpF=false,_gvLpT=null;

function GridV({onRemoveGarde=null,planIssues={},allDays,year,month,meds,getEntries,acteById,onCell,isEdit,notes={},isVac,applyGarde,allMeds,viewPeriod,allDays4,showFull,showGarde=true,intGarde=null,gardeLocked=false,onCellHistory=null,getAstreinteForDay,prefFor=null,gardePref=null,printWk=null}){
  /* v10.41 : désactivation. Couvert sur TOUTE la période affichée → la colonne
     disparaît (sa règle : « cela simplifie l'affichage ») ; couvert sur une
     partie → la case du jour est hachurée et verrouillée, et la personne
     redevient disponible le jour de son retour. Des dates, jamais une période. */
  meds=(meds||[]).filter(m=>offEtat(m,allDays4||[])!=="off");
  const today=new Date();
  const C0=42,C1=24,CG=44;
  // Find garde med for a given day (slot N)
  const [pickGardeDayFull,setPickGardeDayFull]=useState(null);
  const pickGardeDay=pickGardeDayFull?pickGardeDayFull.d:null;
  const setPickGardeDay=(v)=>setPickGardeDayFull(v?{d:v,y:year,m:month}:null);
  const [gardeSearch,setGardeSearch]=useState("");
  const gardePickMeds=(allMeds||meds).filter(m=>m.garde===true&&!(pickGardeDayFull&&offOn(m,pickGardeDayFull.y,pickGardeDayFull.m,pickGardeDayFull.d)));
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
    const days=perDaysList(sy,sm).map(o=>({y:o.y,m:o.m,d:o.d,label:null}));
    if(!showFull){const tod=new Date();tod.setHours(0,0,0,0);return days.filter(({y:ey,m:em,d})=>new Date(ey,em,d)>=tod);}
    return days;
  },[viewPeriod,allDays,year,month,showFull,PCFG.len,PCFG.startM]);
  const printDays=printWk?effectiveDays.filter(o=>inPrintRange(printWk,o.y,o.m,o.d)):effectiveDays;
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
    return sls.some(sl=>getEntries(mid,y2,m2,d2,sl).some(e=>ABS_IDS.includes(e.acteId)));
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
        {/* v9.82 : même présentation que la modale de l'onglet Gardes — échange et retrait
            visibles d'emblée, un seul clic chacun. Une seule façon de faire dans les deux écrans. */}
        <div style={{color:"var(--txt2)",fontSize:12,marginTop:-6,marginBottom:8}}>Le repos post-garde est posé automatiquement.</div>
        {(()=>{const pgf2=pickGardeDayFull||{d:pickGardeDay,y:year,m:month};const cgm=getGardeMed2(pgf2.y,pgf2.m,pgf2.d);return cgm?(
          <div style={{marginBottom:12,padding:"8px 10px",background:"var(--garde-bg)",borderRadius:7,border:"1px solid #86efac"}}>
            <div style={{fontSize:10,color:"#16a34a",fontWeight:700,marginBottom:5}}>✓ Garde assignée</div>
            <div style={{display:"flex",alignItems:"center",gap:7,marginBottom:8}}>
              <div style={{width:28,height:28,borderRadius:"50%",background:cgm.color,display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:10,fontWeight:800}}>{cgm.init}</div>
              <span style={{color:"var(--txt)",fontSize:13,fontWeight:700}}>{cgm.prenom} {cgm.nom}</span>
            </div>
            <button onClick={()=>setGardeSwapOpen(v=>!v)} style={{width:"100%",padding:"6px",borderRadius:6,border:"1.5px solid #388bfd",background:"rgba(56,139,253,.10)",color:"#388bfd",fontWeight:800,cursor:"pointer",fontSize:11,marginBottom:6}}>⇄ Échanger cette garde…</button>
            <button style={{width:"100%",padding:"6px",borderRadius:6,border:"none",background:"#fef2f2",color:"#dc2626",cursor:"pointer",fontSize:11,fontWeight:700}}
              onClick={()=>{const pgf3=pickGardeDayFull||{d:pickGardeDay,y:year,m:month};if(onRemoveGarde)onRemoveGarde(pgf3.y,pgf3.m,pgf3.d);setPickGardeDay(null);}}>
              Retirer la garde + repos
            </button>
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
                  <span style={{width:26,height:26,borderRadius:"50%",background:o.mB.color,color:"#fff",fontSize:10,fontWeight:800,display:"inline-flex",alignItems:"center",justifyContent:"center"}}>{o.mB.init}</span>
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
          const onEnter=e=>{if(e.key==="Enter"&&filteredGM.length===1){const pgf=pickGardeDayFull||{d:pickGardeDay,y:year,m:month};if(isAbsOn(filteredGM[0].id,pgf.y,pgf.m,pgf.d)){toast("Absent / FMC ce jour — utilisez « Assigner quand même »","warn");return;}applyGarde(filteredGM[0].id,pgf.y,pgf.m,pgf.d);setPickGardeDayFull(null);}};
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
        <GardeCandidateList
          meds={filteredGM}
          isAbsDay={mid=>{const p2=pickGardeDayFull||{d:pickGardeDay,y:year,m:month};return isAbsOn(mid,p2.y,p2.m,p2.d);}}
          isAbsNext={mid=>{const p2=pickGardeDayFull||{d:pickGardeDay,y:year,m:month};const nx=new Date(p2.y,p2.m,p2.d+1);return isAbsOn(mid,nx.getFullYear(),nx.getMonth(),nx.getDate());}}
          tourNext={mid=>{const p2=pickGardeDayFull||{d:pickGardeDay,y:year,m:month};const nx=new Date(p2.y,p2.m,p2.d+1);const ny=nx.getFullYear(),nm=nx.getMonth(),nd=nx.getDate();if(isWE(ny,nm,nd))return null;const t=["M","AM"].flatMap(sl=>getEntries(mid,ny,nm,nd,sl)||[]).find(e=>e&&(e.acteId==="TOUR_HC"||e.acteId==="TOUR_USIC"));return t?(t.acteId==="TOUR_HC"?"HC":"USIC"):null;}}
          prefOf={mid=>{const p2=pickGardeDayFull||{d:pickGardeDay,y:year,m:month};return gardePref?gardePref(mid,p2.y,p2.m,p2.d):null;}}
          currentId={(()=>{const p2=pickGardeDayFull||{d:pickGardeDay,y:year,m:month};const gm=getGardeMed2(p2.y,p2.m,p2.d);return gm?gm.id:null;})()}
          onPick={mid=>{const p2=pickGardeDayFull||{d:pickGardeDay,y:year,m:month};applyGarde(mid,p2.y,p2.m,p2.d);setPickGardeDayFull(null);}}
          maxHeight={320}/>
        </>);})()}
      </div>
    </Ov>}
    <TableScroll jours fit>
      <table style={{borderCollapse:"collapse",tableLayout:"fixed"}}>
        <thead>
          <tr>
            <th style={{...S.thFix,position:"sticky",top:0,left:0,zIndex:40,minWidth:C0}}>Jour</th>
            <th style={{...S.thFix,position:"sticky",top:0,left:C0,zIndex:40,minWidth:C1}}>Sl</th>
            {showGarde&&<th style={{...S.thFix,position:"sticky",top:0,zIndex:20,minWidth:CG,borderRight:"2px solid var(--border)",fontSize:9,color:"#93c47d"}}>Garde</th>}
            {intGarde&&<th title="Garde des internes (lecture seule)" style={{...S.thFix,position:"sticky",top:0,zIndex:20,minWidth:CG,borderRight:"2px solid var(--border)",fontSize:9,color:"#1d4ed8"}}>🎓 Int.</th>}
            {meds.map(m=><th key={m.id} style={{...S.th,minWidth:46,position:"sticky",top:0,zIndex:20}} title={`Dr. ${m.prenom} ${m.nom}`}>
              <div style={{...S.avT,background:m.color,margin:"0 auto"}}>{m.init}</div>
            </th>)}
          </tr>
        </thead>
        <tbody>
          {printDays.map(({y:ey,m:em,d},di)=>{
            const prevDay=di>0?printDays[di-1]:null;
            const isNewMonth=viewPeriod&&(!prevDay||prevDay.m!==em||prevDay.y!==ey);
            const we=isWE(ey,em,d),isT=d===today.getDate()&&em===today.getMonth()&&ey===today.getFullYear();
            const slots=we?["JOUR"]:["M","AM"];
            const isMonGV=!we&&dow(ey,em,d)===1;
            const gardeMed=getGardeMed2(ey,em,d);
            return slots.map((sl,si)=>(
              <tr key={ey+"-"+em+"-"+d+sl} data-day={ey+"-"+em+"-"+d} style={{height:28,borderBottom:si===slots.length-1?"1px solid var(--border)":"1px solid var(--border2)",...(we?{background:"var(--bg-we)"}:{}),...(isT?{background:"var(--bg-td)"}:{}),...(si===0&&isMonGV?{boxShadow:"0 -2px 0 0 var(--border)"}:{})}}>
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
                  onClick={()=>{ if(!isEdit||gardeLocked)return; setGardeSearch(""); setPickGardeDayFull({d,y:ey,m:em}); }}>
                  {gardeMed&&<div style={{display:"flex",flexDirection:"column",alignItems:"center",gap:2}}>
                    <div style={{width:26,height:26,borderRadius:"50%",background:gardeMed.color,display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:10,fontWeight:800}}>{gardeMed.init}</div>
                  </div>}
                </td>}
                {si===0&&intGarde&&(()=>{ /* v10.61 lot 3b : garde des internes, lecture seule */
                  const gi=intGarde(ey,em,d);
                  return <td rowSpan={slots.length} title={gi?(gi.ext?(gi.ext+" (interne extérieur)"):("Interne de garde : "+gi.med.nom)):"Aucun interne de garde"}
                    style={{...S.tdFix,borderRight:"2px solid var(--border)",minWidth:CG,padding:"2px",verticalAlign:"middle",
                      background:gi?(we?"var(--bg-we)":"var(--garde-bg)"):"rgba(248,81,73,.16)"}}>
                    {gi&&gi.med&&<div style={{width:26,height:26,borderRadius:"50%",background:gi.med.color,display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:10,fontWeight:800,margin:"0 auto"}}>{gi.med.init}</div>}
                    {gi&&gi.ext&&<div style={{fontSize:8,fontWeight:800,color:"var(--txt2)",background:"var(--bg2)",border:"1px dashed var(--border)",borderRadius:5,padding:"2px 2px",textAlign:"center",overflow:"hidden",textOverflow:"ellipsis",whiteSpace:"nowrap"}}>{gi.ext}</div>}
                  </td>;})()}
                {meds.map(med=>{
                  const es=getEntries(med.id,ey,em,d,sl);
                  const bl=es[0]&&es[0]._blocked;
                  const noteT=notes[nk(med.id,ey,em,d,sl)];const issueT=planIssues[med.id+"|"+ey+"|"+em+"|"+d+"|"+sl];
                  const offC=offOn(med,ey,em,d);   /* v10.41 : indisponible ce jour-là */
                  const astId=getAstreinteForDay?getAstreinteForDay(ey,em,d):null;
                  const isAst=astId!==null&&String(astId)===String(med.id);
                  let astSh=null;
                  if(isAst){
                    const pdV=new Date(ey,em,d-1),ndV=new Date(ey,em,d+1);
                    const paV=getAstreinteForDay(pdV.getFullYear(),pdV.getMonth(),pdV.getDate()),naV=getAstreinteForDay(ndV.getFullYear(),ndV.getMonth(),ndV.getDate());
                    const contPrev=paV!==null&&String(paV)===String(med.id),contNext=naV!==null&&String(naV)===String(med.id);
                    const parts=["inset 1px 0 0 var(--ast-bord)","inset -1px 0 0 var(--ast-bord)"];
                    if(si===0&&!contPrev)parts.push("inset 0 1px 0 var(--ast-bord)");
                    if(si===slots.length-1&&!contNext)parts.push("inset 0 -1px 0 var(--ast-bord)");
                    astSh=parts.join(", ");
                  }
                  /* v10.81 : preferences de tour (bande lun-ven) et de garde (icone du jour) */
                  const pf=prefFor?prefFor(med.id,ey,em,d):null;
                  const prefBg=pf&&pf.tour?(pf.tour==="wish"?"rgba(56,139,253,.20)":"rgba(248,81,73,.18)"):null;
                  return <td key={med.id} title={offC?("Indisponible — désactivé "+medOffL(med).map(r=>"du "+offFr(r.du)+" au "+offFr(r.au)).join(", ")):((issueT?issueT+(noteT?" | "+noteT:""):noteT)||undefined)}
                    style={{...S.td,...(we?S.tdWE:{}),...(isAst?{background:"var(--ast-bg)",boxShadow:astSh}:{}),...(prefBg?{background:prefBg}:{}),...(bl?{background:"var(--bg)",opacity:.4,cursor:"default"}:{cursor:isEdit?"pointer":"default"}),...(offC?{background:"repeating-linear-gradient(45deg,transparent,transparent 5px,rgba(120,130,150,.20) 5px,rgba(120,130,150,.20) 10px)",opacity:.55,cursor:"default"}:{}),display:"table-cell",verticalAlign:"middle",position:"relative"}}
                    onContextMenu={onCellHistory?e=>{e.preventDefault();onCellHistory(med.id,ey,em,d,sl);}:undefined}
                    onTouchStart={onCellHistory?()=>{_gvLpF=false;clearTimeout(_gvLpT);_gvLpT=setTimeout(()=>{_gvLpF=true;onCellHistory(med.id,ey,em,d,sl);},600);}:undefined}
                    onTouchEnd={onCellHistory?()=>clearTimeout(_gvLpT):undefined}
                    onTouchMove={onCellHistory?()=>clearTimeout(_gvLpT):undefined}
                    onClick={bl||offC||!isEdit?undefined:()=>{if(_gvLpF){_gvLpF=false;return;}onCell(med.id,ey,em,d,sl);}}>
                    {pf&&pf.garde&&si===0&&<div style={{position:"absolute",top:1,left:1,zIndex:6,width:14,height:14,borderRadius:"50%",background:"#fff",boxShadow:"0 0 0 1px rgba(0,0,0,.28)",display:"flex",alignItems:"center",justifyContent:"center",fontSize:9,lineHeight:1,pointerEvents:"none"}}>{pf.garde==="wish"?"⭐":"🚫"}</div>}
                    {issueT&&<div style={{position:"absolute",top:0,right:0,width:0,height:0,borderTop:"9px solid #f85149",borderLeft:"9px solid transparent"}}/>}{!bl&&<div style={{display:"flex",flexWrap:"wrap",justifyContent:"center",alignItems:"center",gap:1}}>
                      <CondBadges es={es} acteById={acteById} noteT={noteT}/>
                    </div>}
                  </td>;
                })}
              </tr>
            ))
          })}
        </tbody>
      </table>
    </TableScroll>
    </>
  );
}

/* ════ SITE VIEW (CHL/CHB) ════ */
/* v9.87 : LE CADRE DE DÉFILEMENT DES TABLEAUX, écrit 10 fois dans 7 composants.
   Défaut corrigé au passage : DEUX défilements imbriqués — celui de la page et celui de
   ce cadre. Les en-têtes (initiales, salles, dates) étaient figés par rapport au CADRE ;
   or, en faisant défiler le tableau d'abord, la page se mettait ensuite à monter en
   emportant le cadre, en-têtes compris. D'où des en-têtes qui s'échappaient — et
   invisibles sur un écran où le bandeau du haut est plus grand, les 110px n'étant qu'une
   estimation. Correction : le cadre ne défile plus verticalement (rendu à la page) et ses
   en-têtes se figent par rapport à L'ÉCRAN, sous la barre de navigation. Les bandeaux et
   les filtres remontent donc toujours, mais les en-têtes ne peuvent plus partir. */
/* v9.87.3 : le seul réglage qui restait à ajuster. Le cadre était trop haut de quelques
   dizaines de pixels : arrivé en bas de page, son sommet passait DERRIÈRE la barre de
   navigation, emportant la ligne des initiales avec lui. En le raccourcissant, son sommet
   se pose juste en dessous et les en-têtes restent lisibles jusqu'à la dernière ligne.
   Valeur unique et facile à retoucher : c'est tout l'intérêt du composant partagé. */
/* v9.98 : mémoire de défilement. Deux comportements, selon sa demande :
   — les onglets qui affichent les JOURS partagent une même date : si on regarde le
     12 août dans Planning, on arrive au 12 août dans CHL, CHB, PT Cardio, PT Angio et
     Attachés. C'est la date qui suit, pas une position en pixels — les lignes n'ont pas
     la même hauteur d'un onglet à l'autre ;
   — les autres onglets retrouvent simplement l'endroit où ils étaient.
   Rien ne survit au rechargement : on revient alors au jour courant, ce qui convient. */
const SCROLL_MEM={jour:null,pos:{}};
/* v10.49 : demi-journées off (onglet Reports) — participation des salles.
   `offOuv` vit sur la fiche de salle ; non renseigné = par défaut les salles où
   une consultation (CS_CHL / CS_CHB) peut se dérouler — son précochage. */
const OFF_CS_IDS=["CS_CHL","CS_CHB"];
function offOuvOn(entry,actes){
  if(!entry)return false;
  if(entry.offOuv!==undefined)return !!entry.offOuv;
  const nom=entry._origN||entry.n;
  return !!nom&&(actes||[]).some(a=>OFF_CS_IDS.indexOf(a.id)>=0&&(a.salles||[]).indexOf(nom)>=0);
}
/* v10.46 : les onglets dont la grille occupe l'écran en entier — leur cadre
   passe en « fit », et le bas de page n'y garde qu'une petite marge. */
const GRID_FIT=["planning","chl","chb","plateau","angio","attache","internes"]; /* v10.80 : « internes » manquait — l'onglet est né en v10.54, APRÈS cette liste écrite en v10.46. Sa grille passait bien en « fit », mais la page gardait les 110 px de marge basse : la boucle de mesure voyait la page déborder de cette marge et rendait la hauteur correspondante. D'où un tableau qui s'arrêtait ~110 px trop haut, sur cet onglet seulement. */
/* v10.47 : Tour et Gardes vivent dans Construire (tuiles 2 et 3) — leurs
   boutons sont retirés pour tous, à sa demande. Les onglets restent dans le
   code : Construire les embarque, les supprimer le casserait. */
const HIDDEN_TABS=["tourmedical","garde"];
function TableScroll({children,style,mh=150,jours=false,memId=null,fit=false}){
  const ref=React.useRef(null);
  React.useLayoutEffect(()=>{
    const el=ref.current; if(!el)return;
    if(jours&&SCROLL_MEM.jour){
      const t=el.querySelector('[data-day="'+SCROLL_MEM.jour+'"]');
      if(t){el.scrollTop=Math.max(0,t.offsetTop-el.offsetTop);return;}
    }
    if(!jours&&memId&&SCROLL_MEM.pos[memId])el.scrollTop=SCROLL_MEM.pos[memId];
  },[jours,memId]);
  const onScroll=()=>{
    const el=ref.current; if(!el)return;
    if(jours){
      const rows=el.querySelectorAll("[data-day]");
      for(let i=0;i<rows.length;i++){
        if(rows[i].offsetTop-el.offsetTop>=el.scrollTop-2){SCROLL_MEM.jour=rows[i].getAttribute("data-day");break;}
      }
      return;
    }
    if(memId)SCROLL_MEM.pos[memId]=el.scrollTop;
  };
  /* v10.46 : le vrai remède au chantier v9.87, sur SON diagnostic (deux barres
     à droite, la seconde emporte le haut de la page, la première s'arrête avant
     la fin du tableau) : le cadre MESURE sa position et prend exactement le
     reste de la fenêtre. La page n'a plus rien à faire défiler, l'en-tête ne
     peut plus partir, et la barre interne va jusqu'au bout. Recalculé à chaque
     rendu (les bandeaux au-dessus vont et viennent) et au redimensionnement. */
  const doFit=React.useCallback(()=>{
    if(!fit)return;
    const el=ref.current;if(!el)return;
    /* v10.47, ses deux retours de test :
       (1) TÉLÉPHONE (fenêtre étroite ou place trop petite) : l'ANCIEN
       comportement, voulu — les bandeaux du haut doivent pouvoir partir au
       défilement, sinon la grille devient « un petit carré peu lisible ».
       (2) ORDINATEUR : la mesure géométrique laissait encore déborder
       CHL/CHB/PT alors que le Planning était bon — cause invisible d'ici.
       Donc boucle fermée : on pose la hauteur, on RELIT le débordement réel
       de la page et on l'absorbe, quelle qu'en soit l'origine.
       Ne jamais VIDER maxHeight : React croirait sa valeur inchangée et ne
       la réécrirait pas. On pose toujours soit la hauteur calculée, soit la
       valeur d'origine. */
    const legacy="calc(100vh - "+mh+"px)";
    if(window.innerWidth<760){if(el.style.maxHeight!==legacy)el.style.maxHeight=legacy;return;}
    /* v10.48, son retour Edge : « on perd de la place en bas ». Plus de marges
       au doigt mouillé — les bandeaux fixés en bas (hors-ligne, PIN médecin ou
       administratif) sont MESURÉS, et la boucle devient symétrique : elle
       absorbe le débordement de la page ET reprend la place inutilisée tant
       que le tableau a encore des lignes à montrer. Le tableau ne peut donc
       qu'y gagner, jamais rétrécir. */
    const de=document.documentElement;
    let barH=0;document.querySelectorAll('[data-botbar="1"]').forEach(b=>{barH=Math.max(barH,b.offsetHeight||0);});
    const top=el.getBoundingClientRect().top+(window.scrollY||window.pageYOffset||0);
    let h=window.innerHeight-top-barH-14;
    const v0=Math.max(260,h)+"px";
    if(el.style.maxHeight!==v0)el.style.maxHeight=v0;
    const over=de.scrollHeight-de.clientHeight;   /* lu APRÈS la pose : la mise en page vient d'être refaite */
    if(over>0)h-=over;                                          /* la page déborde encore : absorber */
    else if(over<0&&el.scrollHeight-el.clientHeight>1){const gain=(-over)-barH-2;if(gain>0)h+=gain;} /* place perdue ET tableau coupé : la reprendre, en s'arrêtant AU-DESSUS des bandeaux fixés (ils ne pèsent pas dans la hauteur de page) */
    if(h<380){if(el.style.maxHeight!==legacy)el.style.maxHeight=legacy;return;}
    const v=h+"px";
    if(el.style.maxHeight!==v)el.style.maxHeight=v;
  },[fit,mh]);
  React.useLayoutEffect(()=>{doFit();});
  React.useEffect(()=>{
    if(!fit)return;
    window.addEventListener("resize",doFit);
    return ()=>window.removeEventListener("resize",doFit);
  },[fit,doFit]);
  /* v9.87.2 : RETOUR au comportement d'avant la v9.87, à sa demande.
     Mes deux tentatives ont empiré les choses : la première laissait les en-têtes partir,
     la seconde a créé DEUX barres de défilement à droite dans un ordre inversé, réduisant
     la zone visible. Le cadre retrouve donc exactement ses réglages d'origine.
     Le composant unique est conservé : il n'y a plus qu'un seul endroit à modifier si on
     reprend ce sujet, au lieu des dix cadres identiques d'avant. */
  return(
    <div ref={ref} onScroll={onScroll} style={{overflowX:"auto",overflowY:"auto",maxHeight:"calc(100vh - "+mh+"px)",
      borderRadius:8,border:"1px solid var(--border)",...(style||{})}}>
      {children}
    </div>
  );
}
function SiteView({issMap={},printWk=null,onPrint=null,site,year,month,prevM,nextM,actes,medecins,getEntries,salleOcc,allDays,isEdit,onPickSite,notes={},salleReg=[],darkMode,setDarkMode,showFull,setShowFull,viewPeriod,allDays4,setViewPeriod,colOrder=null,onOrder=null,intCfg=null}){
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
  const _legacy=site==="ANGIO"?siteActes.flatMap(a=>a.salles||[]).filter(s=>String(s).startsWith("Angio")):(_robustSalles||uniqArr(siteActes.filter(a=>a.id!=="BIP").flatMap(a=>a.salles||[])));
  /* v9.89 : les salles écrites dans le code étaient AJOUTÉES au registre, pas seulement
     un repli — supprimer une salle du registre ne la faisait donc pas disparaître de
     l'onglet. Désormais le registre FAIT FOI dès qu'il contient quelque chose ; les
     valeurs d'amorçage ne servent plus qu'à une installation vierge. Vider un site
     signifie « ce site n'a plus de salles », et non « pas encore configuré ». */
  const _regVide=!(salleReg&&salleReg.length);
  const _allSallesBase=_uniq((_regVide?_legacy:_regS).filter(s=>s!=="CHB-BIP"));
  /* v9.74 : ordre des colonnes réglable, comme dans PT Cardio (les 4 onglets traités
     pareil). Une colonne absente de l'ordre enregistré garde sa place d'origine, à la
     fin — une salle ajoutée plus tard n'est donc jamais perdue. */
  const _allCols=_allSallesBase.concat(_recapCols);
  const allSalles=(()=>{
    const ord=colOrder||[];
    if(!ord.length)return _allCols;
    const rank=k=>{const i=ord.indexOf(k);return i<0?9999:i;};
    return _allCols.map((c,i)=>({c,i})).sort((a,b)=>(rank(a.c)-rank(b.c))||(a.i-b.i)).map(x=>x.c);
  })();
  const wdays=printWk?svEffDays.filter(o=>inPrintRange(printWk,o.y,o.m,o.d)):svEffDays; // keep full {y,m,d} objects
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
        /* v9.57.1 : une branche non tranchée ne figure pas dans la colonne de reprise */
        return es.filter(e=>e.acteId===_rId&&!e.cond).map(e=>({med,acte:bipActe,rs:e.salle}));
      });
      /* v10.62 : internes posés sur cette activité — affichés, jamais comptés */
      const semJb=intMedsDuJour(intCfg,ry,rm,d);
      const bipInt=semJb?semJb.meds.flatMap(im=>getEntries(im.id,ry,rm,d,sl).filter(e=>e&&e.acteId===_rId&&!e.cond).map(e=>({med:im,acte:bipActe,rs:e.salle,isInt:true}))):[];
      const bipAll=bipOcc2.concat(bipInt);
      return(
        <td key={"bip"+d+sl} style={{...S.td,borderLeft:"3px solid var(--border)",cursor:isEdit?"pointer":"default",padding:2,verticalAlign:"middle",textAlign:"center"}}
          onClick={()=>isEdit&&onPickSite({salle,siteActes:[bipActe],d,sl,y:ry,m:rm})}>
          {bipAll.map(({med,acte,rs,isInt},i)=>(
            <div key={i} style={{display:"flex",alignItems:"center",gap:3,margin:"1px 0"}}>
              <div title={isInt?med.nom:((med.prenom||"")+" "+(med.nom||"")).trim()} style={{width:26,height:26,borderRadius:"50%",background:med.color,display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:10,fontWeight:800,flexShrink:0,border:isInt?"1.5px dashed rgba(255,255,255,.95)":"none"}}>{med.init}</div>
              {rs?<SallePill nom={rs} acte={acte} night={darkMode}/>
                :(bipActe.hasSalle?<span style={{fontSize:9,fontWeight:800,background:"#fff3cd",color:"#8a6100",border:"1px solid #f59e0b88",borderRadius:4,padding:"1px 4px",whiteSpace:"nowrap"}}>⚠ sans salle</span>:null)}
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
    /* v9.54 : une case se lit PAR ACTIVITÉ — les praticiens d'une même activité
       s'empilent et l'activité n'est écrite qu'une fois. Le fond rouge ne signale
       plus deux praticiens ensemble (c'est fréquent et normal dans ces salles)
       mais DEUX ACTIVITÉS DIFFÉRENTES sur le même créneau. */
    const grps=[];
    occ.forEach(({med,acte})=>{
      const k=(acte&&acte.id)||"";
      let g=grps.find(x=>x.k===k);
      if(!g){g={k,acte,meds:[]};grps.push(g);}
      g.meds.push(med);
    });
    const conflict=grps.length>1;
    /* v10.62 : les internes s'affichent dans la case (rond pointillé) SANS entrer
       dans l'occupation ni dans le conflit — supervision volontaire, sa règle. */
    const semJ=intMedsDuJour(intCfg,ry,rm,d);
    if(semJ)semJ.meds.forEach(im=>{
      getEntries(im.id,ry,rm,d,sl).forEach(e=>{
        if(!(e&&e.acteId&&!e.cond&&e.salle===salle))return;
        const a2=salleActes.find(a=>a.id===e.acteId);
        if(!a2)return;
        let g=grps.find(x=>x.k===a2.id);
        if(!g){g={k:a2.id,acte:a2,meds:[]};grps.push(g);}
        g.imeds=(g.imeds||[]);
        if(!g.imeds.find(x=>x.id===im.id))g.imeds.push(im);
      });
    });
    /* v10.53 : initiales devant chaque note — deux occupants ne se confondent plus */
    const noteTips=occ.map(({med})=>{const n=notes[nk(med.id,ry,rm,d,sl)];return n?(med.init+" : "+n):null;}).filter(Boolean).join("  |  ");
    return(
      <td key={`${salle}-${d}-${sl}`} title={noteTips||undefined}
        style={{...S.td,...(conflict?conflBg(darkMode):{}),...(isTdRC?{background:"var(--bg-td)"}:{}),padding:2,cursor:isEdit?"pointer":"default"}}
        onClick={isEdit?()=>onPickSite({salle,siteActes:salleActes,d,sl,y:ry,m:rm}):undefined}>
        <div style={{display:"flex",flexDirection:"column"}}>
        {grps.map((g,gi)=>(
          <div key={gi} style={{display:"flex",alignItems:"center",justifyContent:"center",gap:3,padding:"2px 0",
            borderTop:gi?"1px dashed "+(conflict?conflSep(darkMode):"var(--border)"):"none"}}>
            <div style={{display:"flex",flexDirection:"column",gap:2}}>
              {g.meds.map((m,mi)=>{
                /* v10.74 : meme alerte que le triangle du Planning, sur le rond de l'occupant */
                const iss=issMap[m.id+"|"+ry+"|"+rm+"|"+d+"|"+sl];
                return <div key={mi} title={((m.prenom||"")+" "+(m.nom||"")).trim()+(iss?" — "+iss:"")} style={{position:"relative",width:24,height:24,borderRadius:"50%",background:m.color,display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:9,fontWeight:800,flexShrink:0}}>{m.init}
                  {iss&&<span style={{position:"absolute",top:-2,left:-2,width:8,height:8,borderRadius:"50%",background:"#f85149",border:"1.5px solid var(--bg2)"}}/>}
                </div>;
              })}
              {(g.imeds||[]).map((m,mi)=>(
                <div key={"i"+mi} title={m.nom} style={{width:24,height:24,borderRadius:"50%",background:m.color,display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:9,fontWeight:800,flexShrink:0,border:"1.5px dashed rgba(255,255,255,.95)"}}>{m.init}</div>
              ))}
            </div>
            <ActPill a={g.acte} night={darkMode} hasNote={g.meds.some(m=>!!notes[nk(m.id,ry,rm,d,sl)])}/>
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
        {onOrder&&isEdit&&<button onClick={()=>onOrder(allSalles)} title="Ordre des colonnes" style={{...S.arr,fontSize:13,width:30}}>↔</button>}
        {onPrint&&<button onClick={onPrint} title="Imprimer" style={{...S.arr,fontSize:13,width:30}}>🖨️</button>}
        <button onClick={()=>setDarkMode(d=>!d)} style={{...S.arr,fontSize:13,width:30}}>{darkMode?"☀️":"🌓"}</button>
        <button onClick={()=>setShowFull(f=>!f)} title={showFull?"Depuis aujourd'hui":"Mois complet"} style={{...S.arr,fontSize:16,width:32,color:showFull?"var(--today-c)":"var(--txt2)",border:`1px solid ${showFull?"var(--today-c)":"var(--border)"}`}}>{showFull?"📅":"🗓️"}</button>
      </div>
    </div>
  );

    return(
    <div>{hdr}
      <TableScroll jours fit>
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
                <tr key={wY+"-"+wM+"-"+d+"we"} data-day={wY+"-"+wM+"-"+d} style={{background:"var(--bg-we)",borderBottom:"1px solid var(--border)",height:28}}>
                  <td colSpan={2} style={{...S.tdFix,position:"sticky",left:0,zIndex:10,background:"var(--bg-we)"}}>
                    <div style={{fontWeight:800,color:"#92400e",fontSize:11,fontFamily:"'JetBrains Mono',monospace",textAlign:"center"}}>{d}{viewPeriod&&<span style={{fontSize:7,color:"#92400e",fontWeight:600,marginLeft:2}}>{MOIS[wM].slice(0,4)}</span>} {JOURSC[dSV]}</div>
                  </td>
                  {allSalles.map(s=><td key={s} style={{...S.td,...S.tdWE}}/>)}
                </tr>
              );
              return["M","AM"].map((sl,si)=>(
                <tr key={wY+"-"+wM+"-"+d+sl} data-day={wY+"-"+wM+"-"+d} style={{borderBottom:si===1?"1px solid var(--border)":"1px solid var(--border2)",...(isT?{background:"var(--bg-td)"}:{}),...(isMonSV&&si===0?{borderTop:"3px solid var(--border)"}:{})}}>
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
      </TableScroll>
    </div>
  );
}

/* ════ ACT TAB VIEW (PT Cardio / PT Angio) ════ */
function ActTabView({issMap={},title,titleColor,rows,year,month,prevM,nextM,medecins,actes,getEntries,notes={},allDays,isEdit,onPickAct,darkMode,setDarkMode,showFull,setShowFull,viewPeriod,allDays4,setViewPeriod,ideFeature,ideOn,setIdeOn,ideCfg,setIdeCfg,canIde,orderCtl,onOrder,printWk,onPrint,intCfg=null}){
  const today=new Date();
  const atvEffDays2=useMemo(()=>{
    const p=perStart(year,month);
    const base=perDaysList(p.sy,p.sm);
    if(!showFull){const tod=new Date();tod.setHours(0,0,0,0);return base.filter(({y:ey3,m:em3,d})=>new Date(ey3,em3,d)>=tod);}
    return base;
  },[year,month,showFull,PCFG.len,PCFG.startM]);
  const wdays=printWk?atvEffDays2.filter(o=>inPrintRange(printWk,o.y,o.m,o.d)):atvEffDays2; // keep full objects

  function getOcc(row,d,sl,ry,rm){
    if(!ry)ry=year; if(!rm&&rm!==0)rm=month;
    const occ=[];
    row.ids.forEach(acteId=>{
      medecins.forEach(med=>{
        getEntries(med.id,ry,rm,d,sl).forEach(e=>{
          const match=(!e.cond)&&(row.salle?(e.acteId===acteId&&e.salle===row.salle):e.acteId===acteId);
          if(match&&!occ.find(x=>x.med.id===med.id&&x.acteId===acteId)){
            const acte=actes.find(a=>a.id===acteId)||{short:acteId,color:row.color,bg:"#111"};
            occ.push({med,acte,salle:e.salle||null,dif:e.dif||null,n:null});
          }
        });
      });
      getEntries(IDE_MED.id,ry,rm,d,sl).forEach(e=>{
        const match=row.salle?(e.acteId===acteId&&e.salle===row.salle):e.acteId===acteId;
        if(match&&!occ.find(x=>x.med.id===IDE_MED.id&&x.acte&&x.acte.id===acteId)){
          const acte=actes.find(a=>a.id===acteId)||{id:acteId,short:acteId,color:row.color,bg:"#111"};
          occ.push({med:IDE_MED,acte,salle:e.salle||null,dif:e.dif||null,n:(e.n===undefined||e.n===null)?null:e.n});
        }
      });
    });
    return occ;
  }

  /* ── v9.35 : volet IDE (PT Cardio) ── */
  const [idePanel,setIdePanel]=useState(false);
  const [ideEdit,setIdeEdit]=useState(null);
  const ideDef=(ideCfg&&ideCfg.def)||{};
  const ideOv=(ideCfg&&ideCfg.ov)||{};
  const ideDispo=(y3,m3,d3,sl)=>{const o=ideOv[sk(y3,m3,d3,sl)];if(o!==undefined&&o!==null)return o;const v=ideDef[dow(y3,m3,d3)+"|"+sl];return (v===undefined||v===null)?0:v;};
  const ideActive=!!(ideFeature&&ideOn);
  const ideMap=useMemo(()=>{
    if(!ideActive)return {};
    const M={};
    wdays.forEach(({y:wY,m:wM,d})=>{
      if(isWE(wY,wM,d))return;
      const semJd=intMedsDuJour(intCfg,wY,wM,d); /* v10.63 : internes du jour pour les IDE */
      ["M","AM"].forEach(sl=>{
        let tot=0,totD=0;
        rows.forEach(row=>{
          const inst={};
          getOcc(row,d,sl,wY,wM).forEach(o=>{
            const k2=o.acte.id+"|"+(o.salle||row.salle||"");
            if(!inst[k2])inst[k2]={n:((o.n===null||o.n===undefined)?(o.acte.ideN||0):o.n),dif:false};
            if(o.dif)inst[k2].dif=true;
          });
          /* v10.63 : un interne mobilise les IDE de son activité, même seul dans la salle */
          if(semJd)semJd.meds.forEach(im=>{
            row.ids.forEach(aid=>{
              getEntries(im.id,wY,wM,d,sl).forEach(e=>{
                if(!(e&&e.acteId===aid&&!e.cond&&(row.salle?e.salle===row.salle:true)))return;
                const acte=actes.find(a=>a.id===aid);if(!acte)return;
                const k2=aid+"|"+(e.salle||row.salle||"");
                if(!inst[k2])inst[k2]={n:(acte.ideN||0),dif:false};
              });
            });
          });
          let n=0,nd=0;
          Object.keys(inst).forEach(k2=>{const it=inst[k2];if(it.dif)nd+=it.n;else n+=it.n;});
          if(n>0)M[row.label+"|"+wY+"-"+wM+"-"+d+"|"+sl]=n;
          tot+=n;totD+=nd;
        });
        M["#|"+wY+"-"+wM+"-"+d+"|"+sl]=tot;
        M["$|"+wY+"-"+wM+"-"+d+"|"+sl]=totD;
      });
    });
    return M;
  },[ideActive,wdays,rows,medecins,actes,getEntries,intCfg]);
  const ideCell=(row,d,sl,ry,rm)=>ideActive?(ideMap[row.label+"|"+ry+"-"+rm+"-"+d+"|"+sl]||0):0;
  const setIdeDefV=(dw3,sl,v)=>{if(setIdeCfg)setIdeCfg(p=>{const q={...(p||{})};q.def={...(q.def||{})};q.def[dw3+"|"+sl]=v;return q;});};
  const setIdeOvV=(y3,m3,d3,sl,v)=>{if(setIdeCfg)setIdeCfg(p=>{const q={...(p||{})};q.ov={...(q.ov||{})};const k=sk(y3,m3,d3,sl);if(v===null)delete q.ov[k];else q.ov[k]=v;return q;});};
  const idePill=(y3,m3,d3,sl)=>{
    const need=ideMap["#|"+y3+"-"+m3+"-"+d3+"|"+sl]||0;
    const difN=ideMap["$|"+y3+"-"+m3+"-"+d3+"|"+sl]||0;
    const dispo=ideDispo(y3,m3,d3,sl);
    const ovv=ideOv[sk(y3,m3,d3,sl)];
    const isOv=(ovv!==undefined&&ovv!==null);
    const ok=need<=dispo;
    return <span title={(isOv?"Effectif corrigé pour ce jour":"Effectif par défaut")+" — besoin simultané "+need+", disponible "+dispo+(difN>0?" — "+difN+" IDE en départ différé (activité qui démarre plus tard, donc non simultanée)":"")} onClick={canIde?(e=>{e.stopPropagation();setIdeEdit({y:y3,m:m3,d:d3,sl});}):undefined} style={{display:"inline-flex",flexDirection:"column",alignItems:"center",lineHeight:1.1,fontSize:12,fontWeight:800,fontFamily:"'JetBrains Mono',monospace",borderRadius:6,padding:"2px 5px",whiteSpace:"nowrap",cursor:canIde?"pointer":"default",background:need===0?"transparent":(ok?"rgba(63,185,80,.15)":"rgba(248,81,73,.15)"),color:need===0?"var(--txt3)":(ok?"#3fb950":"#f85149"),border:isOv?"1px dashed var(--txt3)":"1px solid transparent"}}><span>{need+"/"+dispo}</span>{difN>0&&<span style={{fontSize:9,marginTop:1}}>🕙</span>}</span>;
  };
  const ideExtra=(ideActive?<div>
    {canIde&&idePanel&&<div style={{...S.card,marginBottom:8}}>
      <div style={{fontSize:12,fontWeight:800,marginBottom:6,color:"#3fb950"}}>🩺 IDE disponibles — valeurs par défaut</div>
      <div style={{display:"grid",gridTemplateColumns:"auto 1fr 1fr",gap:4,maxWidth:280,alignItems:"center"}}>
        <div/><div style={{...S.fl,textAlign:"center",marginBottom:0}}>Matin</div><div style={{...S.fl,textAlign:"center",marginBottom:0}}>Après-midi</div>
        {[1,2,3,4,5].map(dw3=><React.Fragment key={dw3}>
          <div style={{fontSize:11,fontWeight:700,color:"var(--txt2)"}}>{JOURSC[dw3]}</div>
          {["M","AM"].map(sl=><input key={sl} type="number" min={0} max={99} value={ideDef[dw3+"|"+sl]===undefined?0:ideDef[dw3+"|"+sl]} onChange={e=>setIdeDefV(dw3,sl,Math.max(0,Math.min(99,parseInt(e.target.value||"0",10)||0)))} style={{...S.fi,width:"100%",textAlign:"center",padding:"4px 2px",fontSize:12}}/>)}
        </React.Fragment>)}
      </div>
      <div style={{fontSize:9,color:"var(--txt3)",marginTop:6}}>Ces valeurs valent pour toutes les semaines. Pour un jour particulier, touchez sa pastille dans le tableau.</div>
    </div>}
    {ideEdit&&<div style={S.ov} onClick={()=>setIdeEdit(null)}>
      <div style={{...S.mb,width:300}} onClick={e=>e.stopPropagation()}>
        <div style={S.mHd}><div style={S.mTit2}>{"🩺 IDE — "+JOURSC[dow(ideEdit.y,ideEdit.m,ideEdit.d)]+" "+ideEdit.d+" "+MOIS[ideEdit.m]+" — "+SLOTS[ideEdit.sl]}</div><button style={S.xBtn} onClick={()=>setIdeEdit(null)}>×</button></div>
        <div style={{fontSize:11,color:"var(--txt2)",marginBottom:8}}>{"Besoin calculé : "+(ideMap["#|"+ideEdit.y+"-"+ideEdit.m+"-"+ideEdit.d+"|"+ideEdit.sl]||0)+" IDE. Défaut du "+JOURSL[dow(ideEdit.y,ideEdit.m,ideEdit.d)].toLowerCase()+" : "+(ideDef[dow(ideEdit.y,ideEdit.m,ideEdit.d)+"|"+ideEdit.sl]||0)+"."}</div>
        <input type="number" min={0} max={99} value={ideDispo(ideEdit.y,ideEdit.m,ideEdit.d,ideEdit.sl)} onChange={e=>setIdeOvV(ideEdit.y,ideEdit.m,ideEdit.d,ideEdit.sl,Math.max(0,Math.min(99,parseInt(e.target.value||"0",10)||0)))} style={{...S.fi,width:"100%",textAlign:"center",fontSize:18,fontWeight:800}}/>
        <div style={{display:"flex",gap:6,marginTop:10}}>
          <button style={{...S.icnBtn,flex:1}} onClick={()=>{setIdeOvV(ideEdit.y,ideEdit.m,ideEdit.d,ideEdit.sl,null);setIdeEdit(null);}}>↩ Revenir au défaut</button>
          <button style={{...S.btnP,flex:1}} onClick={()=>setIdeEdit(null)}>OK</button>
        </div>
      </div>
    </div>}
  </div>:null);
  function renderActCell(row,d,sl,ry,rm){
    if(!ry)ry=year;
    if(!rm&&rm!==0)rm=month;
    const isTd=d===today.getDate()&&rm===today.getMonth()&&ry===today.getFullYear();
    if(isWE(ry,rm,d)) return <td key={`${row.label}-${d}-${sl}`} style={{...S.td,...S.tdWE,padding:2}}/>;
    const occ=getOcc(row,d,sl,ry,rm);
    /* v9.54 : deux ACTIVITÉS différentes sur le créneau passent la case en rouge —
       deux salles d'une même activité, non. */
    const _grpsA=salleGroups(row,occ);
    /* v10.53 : notes par médecin — infobulle « INIT : note » sur la case */
    const _nMeds=[];_grpsA.forEach(g=>(g.meds||[]).forEach(m=>{if(m&&m.id!==IDE_MED.id&&!_nMeds.find(x=>x.id===m.id))_nMeds.push(m);}));
    const noteTips=_nMeds.map(m=>{const n=notes[nk(m.id,ry,rm,d,sl)];return n?(m.init+" : "+n):null;}).filter(Boolean).join("  |  ");
    const _idsA={};_grpsA.forEach(g=>{if(g.acte&&g.acte.id)_idsA[g.acte.id]=1;});
    const conflA=Object.keys(_idsA).length>1;
    /* v10.62 : internes de la case — rond pointillé, jamais dans le conflit */
    const semJA=intMedsDuJour(intCfg,ry,rm,d);
    if(semJA)semJA.meds.forEach(im=>{
      row.ids.forEach(aid=>{
        getEntries(im.id,ry,rm,d,sl).forEach(e=>{
          if(!(e&&e.acteId===aid&&!e.cond&&(row.salle?e.salle===row.salle:true)))return;
          const a2=actes.find(a=>a.id===aid)||{id:aid,short:aid,color:row.color};
          let g=_grpsA.find(x=>x.acte&&x.acte.id===aid&&((x.salle||null)===(e.salle||null)));
          if(!g){g={acte:a2,salle:e.salle||null,meds:[],n:null,dif:null};_grpsA.push(g);}
          g.imeds=(g.imeds||[]);
          if(!g.imeds.find(x=>x.id===im.id))g.imeds.push(im);
        });
      });
    });
    return(
      <td key={`${row.label}-${d}-${sl}`} title={noteTips||undefined} style={{...S.td,...(conflA?conflBg(darkMode):{}),...(isTd?{background:"var(--bg-td)"}:{}),padding:3,maxWidth:150,cursor:isEdit?"pointer":"default"}}
        onClick={isEdit?()=>onPickAct({row,d,sl,y:ry,m:rm}):undefined}>
        <div style={{display:"flex",flexDirection:"column",gap:2,alignItems:"stretch"}}
          onClick={e=>{e.stopPropagation();if(isEdit)onPickAct({row,d,sl,y:ry,m:rm});}}>
        {_grpsA.map((g,gi)=>{
          const monoActe=(row.ids||[]).length===1&&!row.multiActe;
          const ideN=(g.n===null||g.n===undefined)?(g.acte.ideN||0):g.n;
          /* v9.45 : le segment gauche porte la SALLE si la ligne en propose, sinon
             le libellé de l'activité — jamais les deux, jamais de couleur de fond. */
          const salleTrack=row.hasSalleChoice||(g.acte&&g.acte.hasSalle&&!g.acte.fixedSalle);
          /* v10.14 : le libellé n'est masqué que sur une colonne d'ACTIVITÉ, où il ferait
             doublon avec l'en-tête. Sur une colonne de SALLE, l'en-tête dit OÙ et non QUOI :
             l'activité doit toujours s'afficher, même s'il n'y en a qu'une possible —
             c'est ce qui rendait la salle d'EEP muette. */
          const colSalle=!!(row.salle||row.hasSalleChoice);
          const lieu=(salleTrack&&g.salle)?g.salle:((monoActe&&!colSalle)?null:(g.acte.short||g.acte.label||""));
          /* v9.67 : option A — l'occupant sans salle est signalé sur sa ligne */
          const noSalle=salleTrack&&!g.salle&&g.acte&&g.acte.hasSalle&&g.meds.some(m=>m&&m.id!==IDE_MED.id);
          const dc=g.dif?((g.dif.c||"")+(g.dif.h?(g.dif.c?" — ":"")+g.dif.h:"")):"";
          /* v9.46 : un groupe porté par IDE_MED n'a pas d'occupant — pas de vignette,
             et le chiffre porte son unité puisque aucun nom ne l'éclaire. */
          const meds=g.meds.filter(m=>m&&m.id!==IDE_MED.id);
          const imeds=g.imeds||[];
          const ideOnly=meds.length===0&&g.meds.length>0;
          const showIde=ideOnly?(ideN>0):(ideActive&&(ideN>0||g.dif));
          return(
          <div key={gi} style={{display:"flex",alignItems:"center",justifyContent:"flex-start",gap:4,paddingTop:gi?4:0,marginTop:gi?1:0,borderTop:gi?"1px dashed "+(conflA?conflSep(darkMode):"var(--border)"):"none"}}>
            {(meds.length>0||imeds.length>0)&&<div style={{display:"flex",flexDirection:"column",gap:2}}>
              {meds.map((m,mi)=>{
                /* v10.74 : meme alerte que le triangle du Planning, sur le rond de l'occupant */
                const iss=issMap[m.id+"|"+ry+"|"+rm+"|"+d+"|"+sl];
                return <span key={mi} title={((m.prenom||"")+" "+(m.nom||"")).trim()+(iss?" — "+iss:"")+(notes[nk(m.id,ry,rm,d,sl)]?" — 📝 "+notes[nk(m.id,ry,rm,d,sl)]:"")} style={{position:"relative",width:22,height:22,borderRadius:"50%",background:m.color,color:"#fff",display:"inline-flex",alignItems:"center",justifyContent:"center",fontSize:9,fontWeight:800,fontFamily:"'JetBrains Mono',monospace",flexShrink:0}}>{m.init}{notes[nk(m.id,ry,rm,d,sl)]&&<span style={{position:"absolute",top:-1,right:-1,width:6,height:6,borderRadius:"50%",background:"#f59e0b"}}/>}
                  {iss&&<span style={{position:"absolute",top:-2,left:-2,width:8,height:8,borderRadius:"50%",background:"#f85149",border:"1.5px solid var(--bg2)"}}/>}
                </span>;
              })}
              {imeds.map((m,mi)=>(
                <span key={"i"+mi} title={m.nom} style={{width:22,height:22,borderRadius:"50%",background:m.color,color:"#fff",display:"inline-flex",alignItems:"center",justifyContent:"center",fontSize:9,fontWeight:800,fontFamily:"'JetBrains Mono',monospace",flexShrink:0,border:"1.5px dashed rgba(255,255,255,.95)"}}>{m.init}</span>
              ))}
            </div>}
            {(lieu||showIde||noSalle)&&
              <span title={g.dif?("Départ différé"+(dc?" — "+dc:"")):undefined} style={{...pillCols((g.acte&&g.acte.color)||"#888888",darkMode),display:"inline-flex",alignItems:"stretch",height:22,borderRadius:4,overflow:"hidden",fontFamily:"'JetBrains Mono',monospace",fontSize:9.5,fontWeight:800,whiteSpace:"nowrap",cursor:g.dif?"help":"inherit"}}>
                {noSalle&&<span style={{display:"flex",alignItems:"center",padding:"0 6px",background:"#fff3cd",color:"#8a6100"}}>⚠ sans salle</span>}
                {lieu&&<span style={{display:"flex",alignItems:"center",padding:"0 6px"}}>{lieu}</span>}
                {showIde&&<span style={{display:"flex",alignItems:"center",padding:"0 5px",background:"#e0f4e3",color:"#2f9440",borderLeft:lieu?"1px solid #95d99f":"none"}}>{ideOnly?(ideN+" IDE"):ideN}{g.dif&&<span style={{marginLeft:4,fontSize:9}}>🕙</span>}</span>}
              </span>}
          </div>
        );})}
        </div>
        {occ.length===0&&_grpsA.length===0&&<div style={{color:"var(--border)",textAlign:"center",fontSize:13}}>·</div>}
      </td>
    );
  }

  let hdr=(
    <div style={S.bar}>
      <div style={{display:"flex",alignItems:"center",gap:8}}>
        <button onClick={prevM} style={S.arr}>‹</button>
        <h2 style={S.mTit}><span style={{color:titleColor}}>{title}</span> — {(MOIS[perStart(year,month).sm]+" — "+MOIS[(perStart(year,month).sm+PCFG.len-1)%12]+" "+perStart(year,month).sy)}</h2>
        <button onClick={nextM} style={S.arr}>›</button>
      </div>
      <div style={{display:"flex",gap:4,alignItems:"center",marginLeft:"auto"}}>
        {orderCtl&&<button onClick={onOrder} title="Ordre des colonnes" style={{...S.arr,fontSize:13,width:30}}>↔</button>}
        {ideFeature&&<button onClick={()=>setIdeOn(v=>!v)} title="Afficher les effectifs IDE" style={{...S.arr,width:"auto",padding:"0 8px",fontSize:11,fontWeight:800,color:ideOn?"#3fb950":"var(--txt2)",border:`1px solid ${ideOn?"#3fb950":"var(--border)"}`}}>🩺 IDE</button>}
        {ideFeature&&ideOn&&canIde&&<button onClick={()=>setIdePanel(p=>!p)} title="Régler les effectifs par défaut" style={{...S.arr,fontSize:13,width:30,color:idePanel?"#3fb950":"var(--txt2)"}}>⚙️</button>}
        {/* v9.91 : PT Cardio a déjà son bouton d'ordre (orderCtl) — le second, ajouté par erreur en v9.74, est retiré */}
        {onPrint&&<button onClick={onPrint} title="Imprimer" style={{...S.arr,fontSize:13,width:30}}>🖨️</button>}
        <button onClick={()=>setDarkMode(d=>!d)} style={{...S.arr,fontSize:13,width:30}}>{darkMode?"☀️":"🌓"}</button>
        <button onClick={()=>setShowFull(f=>!f)} title={showFull?"Depuis aujourd'hui":"Mois complet"} style={{...S.arr,fontSize:16,width:32,color:showFull?"var(--today-c)":"var(--txt2)",border:`1px solid ${showFull?"var(--today-c)":"var(--border)"}`}}>{showFull?"📅":"🗓️"}</button>
      </div>
    </div>
  );
  hdr=<React.Fragment>{hdr}{ideExtra}</React.Fragment>;

    return(
    <div>{hdr}
      <TableScroll jours fit>
        <table style={{borderCollapse:"collapse"}}>
          <thead>
            <tr>
              <th style={{...S.thFix,position:"sticky",top:0,left:0,zIndex:40,minWidth:42}}>Jour</th>
              <th style={{...S.thFix,position:"sticky",top:0,left:42,zIndex:40,minWidth:24,borderRight:"2px solid var(--border)"}}>Sl</th>
              {rows.map(row=><th key={row.label} style={{...S.th,minWidth:105,maxWidth:150,position:"sticky",top:0,zIndex:20}}><div style={{fontWeight:800,fontSize:13,color:darkMode?lightenHex(row.color,.55):row.color,fontFamily:"'JetBrains Mono',monospace"}}>{row.label}</div></th>)}
            </tr>
          </thead>
          <tbody>
            {wdays.map(({y:wY,m:wM,d})=>{
              const isT=d===today.getDate()&&wM===today.getMonth()&&wY===today.getFullYear();
              const dAT=dow(wY,wM,d), weAT=isWE(wY,wM,d), isMonAT=dAT===1&&!weAT;
                if(weAT) return(
                  <tr key={wY+"-"+wM+"-"+d+"we"} data-day={wY+"-"+wM+"-"+d} style={{background:"var(--bg-we)",borderBottom:"1px solid var(--border)",height:28}}>
                    <td colSpan={2} style={{...S.tdFix,position:"sticky",left:0,zIndex:10,background:"var(--bg-we)"}}>
                      <div style={{fontWeight:800,color:"#92400e",fontSize:11,fontFamily:"'JetBrains Mono',monospace",textAlign:"center"}}>{d}{viewPeriod&&<span style={{fontSize:7,color:"#92400e",fontWeight:600,marginLeft:2}}>{MOIS[wM].slice(0,4)}</span>} {JOURSC[dAT]}</div>
                    </td>
                    {rows.map(r=><td key={r.label} style={{...S.td,...S.tdWE}}/>)}
                  </tr>
                );
                return["M","AM"].map((sl,si)=>(
                <tr key={wY+"-"+wM+"-"+d+sl} data-day={wY+"-"+wM+"-"+d} style={{borderBottom:si===1?"1px solid var(--border)":"1px solid var(--border2)",...(isT?{background:"var(--bg-td)"}:{}),...(isMonAT&&si===0?{borderTop:"3px solid var(--border)"}:{})}}>
                  {si===0&&<td style={{...S.tdFix,position:"sticky",left:0,zIndex:10,verticalAlign:"middle",minWidth:42}} rowSpan={2}>
                    <div style={{fontWeight:800,color:isT?"var(--today-c)":"var(--txt)",fontSize:12,fontFamily:"'JetBrains Mono',monospace",textAlign:"center"}}>{d}{viewPeriod&&<div style={{fontSize:7,color:"var(--txt3)",fontWeight:600,lineHeight:1}}>{MOIS[wM]}</div>}</div>
                    <div style={{fontSize:8,color:"var(--txt3)",textTransform:"uppercase",textAlign:"center"}}>{JOURSC[dAT]}</div>
                  </td>}
                  <td style={{...S.tdFix,position:"sticky",left:42,zIndex:9,fontSize:9,color:"var(--txt3)",fontWeight:700,textAlign:"center",background:"var(--td-fix)",borderRight:"2px solid var(--border)",minWidth:ideActive?46:24,padding:"2px"}}>{SLOTS[sl]}{ideActive&&<div style={{marginTop:2}}>{idePill(wY,wM,d,sl)}</div>}</td>
                  {rows.map(row=>renderActCell(row,d,sl,wY,wM))}
                </tr>
              ));
            })}
          </tbody>
        </table>
      </TableScroll>
    </div>
  );
}

/* ════ GARDE VIEW ════ */
/* v9.83 : la LISTE DES CANDIDATS à une garde était écrite deux fois — une par écran.
   C'est cette duplication qui a produit deux jours de contradictions entre l'onglet
   Gardes et l'onglet Planning. Elle devient un composant unique.
   TROIS ÉTATS, volontairement distincts :
     • gris   : disponible ;
     • orange : absence ou FMC DEMAIN — garde normale, seul le repos saute, un clic ;
     • rouge  : absent ou en FMC LE JOUR MÊME — non cliquable, mais un bouton
                « Assigner quand même » permet le cas rare (garde du soir après une
                journée de FMC). Le geste rare coûte un clic de plus, le geste
                fréquent est protégé de l'erreur. */
function GardeCandidateList({meds,isAbsDay,isAbsNext,tourNext=null,prefOf=null,currentId,onPick,maxHeight=340}){
  return(
    <div style={{display:"flex",flexDirection:"column",gap:5,maxHeight,overflowY:"auto"}}>
      {meds.map(m=>{
        const isOn=currentId!=null&&m.id===currentId;
        const dayAbs=!isOn&&isAbsDay(m.id);
        const nxAbs=!dayAbs&&!isOn&&isAbsNext(m.id);
        /* v10.64 : tour médical HC/USIC le lendemain — le repos de garde tomberait dessus */
        const tn=(!dayAbs&&!isOn&&tourNext)?tourNext(m.id):null;
        /* v10.81 : preference de garde du medecin pour ce jour (informative, jamais bloquante) */
        const gp=prefOf?prefOf(m.id):null;
        const bord=isOn?"#16a34a":dayAbs?"#ef444455":(nxAbs||tn)?"#f59e0b55":"var(--border)";
        const bg=isOn?"#f0fdf4":dayAbs?"rgba(239,68,68,.06)":(nxAbs||tn)?"rgba(245,158,11,.08)":"var(--bg2)";
        return(
          <div key={m.id} style={{border:`1px solid ${bord}`,background:bg,borderRadius:8,padding:"7px 10px"}}>
            <div style={{display:"flex",alignItems:"center",gap:8,cursor:dayAbs?"default":"pointer"}}
                 onClick={()=>{if(!dayAbs)onPick(m.id);}}>
              <div style={{width:28,height:28,borderRadius:"50%",background:m.color,display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:10,fontWeight:800,flexShrink:0,opacity:dayAbs?.5:1}}>{m.init}</div>
              <div style={{display:"flex",flexDirection:"column",alignItems:"flex-start",flex:1}}>
                <span style={{fontSize:12,fontWeight:600,color:dayAbs?"#ef4444":"var(--txt)"}}>{m.prenom} {m.nom}</span>
                {dayAbs&&<span style={{fontSize:9,color:"#ef4444",fontWeight:700}}>⛔ Absent / FMC ce jour</span>}
                {nxAbs&&<span style={{fontSize:9,color:"#b45309",fontWeight:700}}>⚠ Absence/FMC demain — garde possible, sans repos</span>}
                {tn&&!nxAbs&&<span style={{fontSize:9,color:"#b45309",fontWeight:700}}>⚠ Tour {tn} demain — le repos de garde tomberait dessus</span>}
                {gp&&<span style={{fontSize:9,fontWeight:700,color:gp==="wish"?"#16a34a":"#b45309"}}>{gp==="wish"?"⭐ Souhaite cette garde":"🚫 A demandé à éviter cette garde"}</span>}
                {!dayAbs&&!nxAbs&&!tn&&!gp&&!isOn&&<span style={{fontSize:9,color:"var(--txt3)"}}>Disponible</span>}
              </div>
              {isOn&&<span style={{color:"#16a34a",fontSize:12,fontWeight:700}}>✓ De garde</span>}
            </div>
            {dayAbs&&<button onClick={()=>onPick(m.id)}
              style={{marginTop:6,width:"100%",padding:"4px",borderRadius:6,border:"1px solid #ef444488",background:"transparent",color:"#ef4444",cursor:"pointer",fontSize:10,fontWeight:800}}>
              Assigner quand même
            </button>}
          </div>);
      })}
      {meds.length===0&&<div style={{fontSize:11,color:"var(--txt3)",textAlign:"center",padding:"8px 0"}}>Aucun médecin de garde configuré.</div>}
    </div>);
}

function GardeView({noNav=false,onRemoveGarde=null,printWk=null,onPrint=null,year,month,prevM,nextM,medecins,getEntry,allDays,isEdit,applyGarde,isMedAvailable,plan,setPlan,darkMode,setDarkMode,showFull,setShowFull,viewPeriod,allDays4,setViewPeriod,tourMed,gardeAvoid,gardeWish,toast}){
  /* v9.82 : le retrait vient désormais de l'application (prop onRemoveGarde), pour que
     l'onglet Gardes et celui du Planning partagent EXACTEMENT le même geste. */
  const removeGarde=(d3,y3,m3)=>{ if(onRemoveGarde)onRemoveGarde(y3,m3,d3); };
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
      return cellHasAny((plan[sk(y2,m2,d2,sl)]||{})[mid],ABS_IDS)
        ||cellHasAny((plan[sk(y2,m2,d2,"JOUR")]||{})[mid],ABS_IDS);
    });
  };
  const [pickerDay,setPickerDay]=React.useState(null);

  /* ═══ Répartition automatique des gardes ═══ */
  const [gardeModal,setGardeModal]=React.useState(false);
  const [lastGReport,setLastGReport]=React.useState(null);
  const [gMax,setGMax]=React.useState({}); // {medId: maxGardes} optionnel
  const gardeMeds=djListePeriode(medecins,perDaysList(gvSy,gvSm)).filter(m=>m.garde);
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
    return Object.keys(dm).some(mid=>cellHasAny(dm[mid],["GARDE"]));
  };
  const isAbsFor=(medId,y2,m2,d2)=>{
    const es=[...(getEntry?[]:[]),];
    const check=(sl)=>cellHasAny((plan[sk(y2,m2,d2,sl)]||{})[medId],ABS_IDS);
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
      if(offOn(m,y2,m2,d2))return false;   /* v10.41 : désactivé ce jour-là */
      if(isAbsFor(m.id,y2,m2,d2))return false;
      if(inTourWeek(m.id,y2,m2,d2))return false;
      const nx=new Date(y2,m2,d2+1);
      if(isAbsFor(m.id,nx.getFullYear(),nx.getMonth(),nx.getDate()))return false; // repos de garde impossible
      if(offOn(m,nx.getFullYear(),nx.getMonth(),nx.getDate()))return false;   /* v10.41 : désactivé le lendemain — même raison */
      if(inTourWeek(m.id,nx.getFullYear(),nx.getMonth(),nx.getDate()))return false; /* v10.64 : veille d'une semaine de tour — le repos tomberait sur le tour */
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
        if(!cellHasAny(dm[mid],["GARDE"]))return;
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
        if(!cellHasAny(dm[mid],["GARDE"]))return;
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
          if(!cellHasAny(ex,EXCL_IDS))dm[best.assign[dk4]]={acteId:"REPOS_GARDE",salle:null};
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
          <div style={{width:24,height:24,borderRadius:"50%",background:gMed.color,display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:9,fontWeight:800}}>{gMed.init}</div>
          <span style={{fontSize:9,fontWeight:700,color:gMed.color}}>{gMed.prenom} {gMed.nom}</span>
        </div>):null}
      </td>
    );
  }

  const wdays=printWk?gvEffDays.filter(o=>inPrintRange(printWk,o.y,o.m,o.d)):gvEffDays; // keep full objects

  const viewV=(
    <TableScroll memId="gardes">
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
              <tr key={gvY+"-"+gvM+"-"+d} style={{height:36,borderBottom:"1px solid var(--border2)",...(we?{background:"var(--bg-we)"}:{}),...(isT?{background:"var(--bg-td)"}:{})}}>
                <td style={{...S.tdFix,position:"sticky",left:0,zIndex:5,textAlign:"center",background:isT?"var(--bg-td)":we?"var(--bg-we)":"var(--td-fix)"}}>
                  <div style={{fontWeight:800,color:isT?"var(--today-c)":we?"#92400e":"var(--txt)",fontSize:13,fontFamily:"'JetBrains Mono',monospace"}}>{d} <span style={{fontSize:9,fontWeight:600}}>{MOIS[gvM].slice(0,4)}</span></div>
                  <div style={{fontSize:9,color:we?"#92400e":isT?"var(--today-c)":"var(--txt3)",fontWeight:600}}>{["Dim","Lun","Mar","Mer","Jeu","Ven","Sam"][dw2]}</div>
                </td>
                <td style={{...S.td,padding:4,cursor:isEdit?"pointer":"default"}} onClick={isEdit?()=>setPickerDay({d,y:gvY,m:gvM}):undefined}>
                  {gMed?(<div style={{display:"flex",alignItems:"center",gap:6,padding:"4px 8px",borderRadius:6,background:gMed.color+"22"}}>
                    <div style={{width:26,height:26,borderRadius:"50%",background:gMed.color,display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:10,fontWeight:800}}>{gMed.init}</div>
                    <span style={{fontSize:12,fontWeight:600,color:"var(--txt)"}}>{gMed.prenom} {gMed.nom}</span>
                  </div>):(<span style={{color:"var(--txt3)",fontSize:11}}>—</span>)}
                </td>
              </tr>
            );
          })}
        </tbody>
      </table>
    </TableScroll>
  );

    return(
    <div>
      <div style={noNav?{display:"none"}:S.bar}>
        <div style={{display:"flex",alignItems:"center",gap:8}}>
          <button onClick={prevM} style={S.arr}>‹</button>
          <h2 style={S.mTit}><span style={{color:"#f85149"}}>🌙 Gardes</span> — {MOIS[gvSm]+" — "+MOIS[(gvSm+PCFG.len-1)%12]+" "+gvSy}</h2>
          <button onClick={nextM} style={S.arr}>›</button>
        </div>
        <div style={{display:"flex",gap:4,alignItems:"center",marginLeft:"auto"}}>
          {onPrint&&<button onClick={onPrint} title="Imprimer" style={{...S.arr,fontSize:13,width:30}}>🖨️</button>}
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
                    if(cellHasAny(dm[mid],["GARDE","REPOS_GARDE"])){const r=cellDrop(dm[mid],["GARDE","REPOS_GARDE"]);if(r)dm[mid]=r;else delete dm[mid];changed=true;}
                  });
                  if(changed)next[k]=dm;
                });
              });
              if(gvAllDays.length){
                      const last=gvAllDays[gvAllDays.length-1];
                      const dtN=new Date(last.y,last.m,last.d+1);
                      const nyN=dtN.getFullYear(),nmN=dtN.getMonth(),ndN=dtN.getDate();
                      ["JOUR","M","AM"].forEach(sl=>{const k=sk(nyN,nmN,ndN,sl);if(!next[k])return;const dm={...next[k]};let changed=false;
                        Object.keys(dm).forEach(mid=>{if(cellHasAny(dm[mid],["REPOS_GARDE"])){const r=cellDrop(dm[mid],["REPOS_GARDE"]);if(r)dm[mid]=r;else delete dm[mid];changed=true;}});
                        if(changed)next[k]=dm;});
                    }
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
                    if(cellHasAny(dmR[m2.id],["GARDE"]))cn[catOf(ry,rm,rd)]++;
                  });
                  const totR=cn.sem+cn.jeu+cn.ven+cn.sam+cn.dim;
                  return(
                  <tr key={m2.id} style={{borderBottom:"1px solid var(--border2)"}}>
                    <td style={{padding:"3px 8px",fontSize:11,fontWeight:700,color:"var(--txt)"}}>
                      <span style={{display:"inline-flex",width:22,height:22,borderRadius:"50%",background:m2.color,color:"#fff",fontSize:8,fontWeight:800,alignItems:"center",justifyContent:"center",marginRight:5,verticalAlign:"middle"}}>{m2.init}</span>
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

      {viewV}

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
                  <div style={{width:28,height:28,borderRadius:"50%",background:gMed.color,display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:10,fontWeight:800}}>{gMed.init}</div>
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
                          <span style={{width:24,height:24,borderRadius:"50%",background:o.mB.color,color:"#fff",fontSize:9,fontWeight:800,display:"inline-flex",alignItems:"center",justifyContent:"center"}}>{o.mB.init}</span>
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
            <GardeCandidateList
              meds={medecins.filter(m=>m.garde===true)}
              isAbsDay={mid=>isMedAvailable(medecins.find(x=>x.id===mid),pd.y,pd.m,pd.d,gardeSlot)==="blocked"||gvIsAbs(mid,pd.y,pd.m,pd.d)}
              isAbsNext={mid=>{const nx=new Date(pd.y,pd.m,pd.d+1);return gvIsAbs(mid,nx.getFullYear(),nx.getMonth(),nx.getDate());}}
              tourNext={mid=>{const nx=new Date(pd.y,pd.m,pd.d+1);const ny=nx.getFullYear(),nm=nx.getMonth(),nd=nx.getDate();if(isWE(ny,nm,nd))return null;const t=["M","AM"].map(sl=>getEntry(mid,ny,nm,nd,sl)).find(e=>e&&(e.acteId==="TOUR_HC"||e.acteId==="TOUR_USIC"));return t?(t.acteId==="TOUR_HC"?"HC":"USIC"):null;}}
              prefOf={mid=>{const dkP=dKey(pd.y,pd.m,pd.d);return ((gardeWish||{})[dkP]||{})[mid]?"wish":(((gardeAvoid||{})[dkP]||{})[mid]?"avoid":null);}}
              currentId={gMed?gMed.id:null}
              onPick={mid=>{applyGarde(mid,pd.y,pd.m,pd.d);setPickerDay(null);}}
              maxHeight={360}/>
          </Ov>
        );
      })()}
    </div>
  );
}


/* ════ BIP TAB ════ */
function PTOccRooms({medecins,planningType,actes,acteById,salleReg,darkMode,perDays=[]}){
  /* v10.44 : la désactivation entre dans l'occupation théorique — couvert sur
     TOUTE la période : exclu du tableau « fictif » ; couvert en partie :
     hachurage ORANGE sur sa pastille, pour prévenir, avec les dates en infobulle. */
  const oeOf={};medecins.forEach(m=>{oeOf[m.id]=offEtat(m,perDays||[]);});
  const medsAct=medecins.filter(m=>oeOf[m.id]!=="off");
  const HACHO="repeating-linear-gradient(45deg,rgba(245,158,11,.35),rgba(245,158,11,.35) 3px,transparent 3px,transparent 7px)";
  const Rond=({m})=>{const part=oeOf[m.id]==="part";
    const tt=((m.prenom||"")+" "+(m.nom||"")).trim()+(part?(" — indisponible "+medOffL(m).map(r=>"du "+offFr(r.du)+" au "+offFr(r.au)).join(", ")):"");
    return(
      <div title={tt} style={{padding:part?2:0,borderRadius:6,background:part?HACHO:"none",flexShrink:0}}>
        <div style={{width:22,height:22,borderRadius:"50%",background:m.color,display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:9,fontWeight:800}}>{m.init}</div>
      </div>);};
  /* v10.44 : les « sans salle » de chaque site. Une activité ferme sans salle va
     dans le tableau de SON site ; un choix ouvert va dans CHAQUE site que ses
     branches sans salle demandent — une seule fois par site (« CsL ou ETT » :
     une fois à Lens ; « ETT et Cs Béthune » : dans les deux tableaux). Les
     activités de site « tous » (CHU, FMC, RG…) ne vont dans aucun tableau. */
  const sansSalle=(dw,sl,key)=>{
    const out=[];
    medsAct.forEach(m=>{
      const e=((planningType[m.id]||{})[dw]||{})[sl];
      if(!e)return;
      const brs=[[e[0],e[1]],[e[2],e[3]],[e[4],e[5]]].filter(b=>b[0]&&!b[1]);
      const mine=brs.filter(b=>{const a=acteById(b[0]);return a&&a.site===key;});
      if(mine.length)out.push({m:m,aids:mine.map(b=>b[0]),cond:!!e[6]||mine.length>1});
    });
    return out;
  };
  const jours=["","Lun","Mar","Mer","Jeu","Ven"];
  const reg=site=>(salleReg||[]).filter(x=>Array.isArray(x.s)?x.s.indexOf(site)>=0:x.s===site).map(x=>x.n);
  const uniq=arr=>arr.filter((s,i2,a2)=>s&&a2.indexOf(s)===i2);
  const angioAll=uniq(actes.flatMap(a=>a.salles||[]).filter(s=>String(s).indexOf("Angio")===0).concat(reg("ANGIO")));
  const SECTIONS=[
    {key:"CHL",titre:"🏥 CHL — occupation type des salles",color:"#388bfd",salles:uniq(["CHL-1","CHL-2","CHL-3","CHL-4","CHL-5","CHL-6","CHL-7","Holter","HC-Exam"].concat(reg("CHL")))},
    {key:"CHB",titre:"🏥 CHB — occupation type des salles",color:"#3fb950",salles:uniq(["CHB-1","CHB-2","CHB-3","CHB-VASC","EE-CHB","Rythmo-CHB"].concat(reg("CHB"))).filter(s=>s!=="CHB-BIP")},
    {key:"ANGIO",titre:"🩸 PT Angio — occupation type des salles",color:"#76a5af",salles:angioAll.length?angioAll:["Angio-1","Angio-2","Angio-3"]}
  ];
  const occ=(dw,sl,salle)=>medsAct.filter(m=>{const e=((planningType[m.id]||{})[dw]||{})[sl];return e&&((e[0]&&e[1]===salle)||(e[2]&&e[3]===salle)||(e[4]&&e[5]===salle));});
  return(
    <div style={{marginTop:26}}>
      <div style={{fontSize:11,color:"var(--txt3)",marginBottom:2}}>Occupation théorique des salles si tout le monde est présent — reflète uniquement le planning type ci-dessus, jamais le planning réel.</div>
      {SECTIONS.map(sec=>(
        <div key={sec.key} style={{marginTop:20,paddingTop:16,borderTop:"2px solid var(--border)"}}>
          <div style={{fontWeight:800,fontSize:13,color:sec.color,marginBottom:8}}>{sec.titre}</div>
          <div style={{overflowX:"auto",borderRadius:8,border:"1px solid var(--border)"}}>
            <table style={{borderCollapse:"collapse",width:"100%"}}>
              <thead><tr>
                <th style={{...S.thFix,position:"sticky",left:0,zIndex:20,minWidth:46}}>JOUR</th>
                <th style={{...S.th,minWidth:28,fontSize:9}}>SL</th>
                {sec.salles.map(s=><th key={s} style={{...S.th,minWidth:64,fontSize:10}}>{s}</th>)}
                <th style={{...S.th,minWidth:74,fontSize:10,borderLeft:"2px solid var(--border)"}}>Sans salle</th>
              </tr></thead>
              <tbody>
                {[1,2,3,4,5].map(dw=>["M","AM"].map(sl=>(
                  <tr key={dw+sl} style={sl==="AM"?{borderBottom:"2px solid var(--border)"}:{borderBottom:"1px solid var(--border2)"}}>
                    {sl==="M"&&<td rowSpan={2} style={{...S.tdFix,position:"sticky",left:0,zIndex:5,fontWeight:700,fontSize:11,textAlign:"center"}}>{jours[dw]}</td>}
                    <td style={{...S.td,fontSize:9,color:"var(--txt3)",textAlign:"center",padding:"2px 1px"}}>{sl}</td>
                    {sec.salles.map(salle=>{
                      const ms=occ(dw,sl,salle);
                      /* v9.66 : même présentation que les onglets salles (v9.54) — activité
                         écrite une fois par groupe, ronds empilés, pointillé entre groupes,
                         fond rouge seulement si deux ACTIVITÉS différentes dans la salle. */
                      const grps=[];
                      ms.forEach(m=>{
                        const e=((planningType[m.id]||{})[dw]||{})[sl]||[null,null];
                        const aidC=(e[1]===salle&&e[0])?e[0]:(e[3]===salle&&e[2])?e[2]:e[4];
                        let g=grps.find(x=>x.aid===aidC);
                        if(!g){g={aid:aidC,acte:aidC?acteById(aidC):null,meds:[]};grps.push(g);}
                        if(!g.meds.find(x=>x.id===m.id))g.meds.push(m);
                      });
                      const confl=grps.length>1;
                      return(<td key={salle} style={{...S.td,padding:2,verticalAlign:"middle",textAlign:"center",background:confl?conflBg(darkMode):undefined}}>
                        <div style={{display:"flex",flexDirection:"column",alignItems:"center"}}>
                          {grps.map((g,gi)=>(
                            <div key={g.aid||gi} style={{display:"flex",alignItems:"center",justifyContent:"center",gap:3,padding:"2px 0",
                              borderTop:gi?"1px dashed "+(confl?conflSep(darkMode):"var(--border)"):"none"}}>
                              <div style={{display:"flex",flexDirection:"column",gap:2}}>
                                {g.meds.map(m=><Rond key={m.id} m={m}/>)}
                              </div>
                              <ActPill a={g.acte} night={darkMode}/>
                            </div>
                          ))}
                        </div>
                      </td>);
                    })}
                    <td style={{...S.td,padding:2,verticalAlign:"middle",textAlign:"center",borderLeft:"2px solid var(--border)"}}>
                      <div style={{display:"flex",flexDirection:"column",alignItems:"center",gap:3}}>
                        {sansSalle(dw,sl,sec.key).map(x=>(
                          <div key={x.m.id} style={{display:"flex",alignItems:"center",gap:3,padding:x.cond?"2px 4px":"0",
                            border:x.cond?"1.5px dashed #8b5cf6":"none",borderRadius:6}}>
                            <Rond m={x.m}/>
                            <div style={{display:"flex",flexDirection:"column",gap:1,alignItems:"flex-start"}}>
                              {x.aids.map((aid,ai)=><ActPill key={ai} a={acteById(aid)} night={darkMode}/>)}
                            </div>
                          </div>
                        ))}
                      </div>
                    </td>
                  </tr>
                )))}
              </tbody>
            </table>
          </div>
        </div>
      ))}
    </div>
  );
}
function PlanTypeGrid({medecins,actes,planningType,setPlanningType,isEdit,acteById,setMData,setModal,perDays=[],onMedClick=null}){
  const jours=["","Lun","Mar","Mer","Jeu","Ven"];
  /* v10.40 : état d'activité sur la période affichée. La colonne d'un médecin
     désactivé sur TOUTE la période est hachurée — son planning type reste
     visible, c'est son APPLICATION qui s'interrompt, jamais son contenu. */
  const offIds=new Set(medecins.filter(m=>offEtat(m,perDays)==="off").map(m=>m.id));
  const HACH="repeating-linear-gradient(45deg,transparent,transparent 5px,rgba(120,130,150,.16) 5px,rgba(120,130,150,.16) 10px)";

    return(
    <TableScroll memId="type" mh={150}>
      <table style={{borderCollapse:"collapse"}}>
        <thead>
          <tr>
            <th style={{...S.thFix,position:"sticky",top:0,left:0,zIndex:40,minWidth:48}}>Jour</th>
            <th style={{...S.thFix,position:"sticky",top:0,left:48,zIndex:40,minWidth:26,borderRight:"2px solid var(--border)"}}>Sl</th>
            {medecins.map(med=>{const oe=offEtat(med,perDays);
              const tt="Dr. "+(med.prenom||"")+" "+(med.nom||"")+(oe?(" — indisponible "+medOffL(med).map(r=>"du "+offFr(r.du)+" au "+offFr(r.au)).join(", ")):(onMedClick?" — cliquer pour activer / désactiver":""));
              return <th key={med.id} style={{...S.th,minWidth:46,position:"sticky",top:0,zIndex:20}} title={tt}>
              <div onClick={()=>{if(onMedClick)onMedClick(med);}}
                style={{...S.avT,background:med.color,margin:"0 auto",cursor:onMedClick?"pointer":"default",
                  opacity:oe==="off"?.38:1,filter:oe==="off"?"grayscale(.8)":"none",
                  outline:oe==="part"?"2px dashed #f59e0b":"none",outlineOffset:1}}>{med.init}</div>
              {oe&&<div style={{fontSize:8,lineHeight:"9px",color:oe==="off"?"var(--txt3)":"#b45309"}}>{oe==="off"?"⏸":"◐"}</div>}
            </th>;})}
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
                const [acteId,salle,acteId2,salle2,acteId3,salle3,c1f]=(pt[dw]||{})[sl]||[null,null];
                const acte=acteId?acteById(acteId):null;const acte2=acteId2?acteById(acteId2):null;const acte3=acteId3?acteById(acteId3):null;
                const _isC=!!c1f||[acteId,acteId2,acteId3].filter(Boolean).length>1;const ptIss=!_isC&&((acte&&acte.hasSalle&&!salle)||(acte2&&acte2.hasSalle&&!salle2)||(acte3&&acte3.hasSalle&&!salle3));
                const ptEs=[{acteId,salle},{acteId:acteId2,salle:salle2},{acteId:acteId3,salle:salle3}].filter(x=>x.acteId);
                if(ptEs.length>1||c1f)ptEs.forEach(x=>{x.cond=1;});
                return(
                  <td key={med.id} style={{...S.td,padding:2,cursor:isEdit?"pointer":"default",position:"relative",...(offIds.has(med.id)?{background:HACH}:{})}} title={ptIss?"⚠ salle non attribuée":undefined}
                    onClick={()=>{ if(!isEdit)return; setMData({medId:med.id,dayOfWeek:dw,slot:sl}); setModal("editPT"); }}>{ptIss&&<div style={{position:"absolute",top:0,right:0,width:0,height:0,borderTop:"9px solid #f85149",borderLeft:"9px solid transparent"}}/>}
                    <div style={{display:"flex",flexDirection:"column",alignItems:"center",gap:1}}><CondBadges es={ptEs} acteById={acteById} noteT={null}/></div>
                  </td>
                );
              })}
            </tr>
          )))}
        </tbody>
      </table>
    </TableScroll>
  );
}

/* ════ PICK MED ACT MODAL (PT Cardio/Angio) ════ */
function PickMedActModal({mData,setMData,medecins,actes,getEntries,isMedAvailable,addEntry,removeEntry,patchAct,canDif=false,onClose,adminOnly=false,selfOnly=null,okKey="adminOk",notes={},setNotes=null,canNotes=false,intCfg=null,canInt=false}){
  /* v10.92 : la liste proposee porte le nom du junior EN POSTE CE JOUR-LA. */
  {const _dj=(mData&&mData.y!=null&&mData.m!=null&&mData.d!=null)?dKey(mData.y,mData.m,mData.d):null;
   if(_dj)medecins=(medecins||[]).map(m0=>djAff(m0,_dj));}
  const {row,d,sl,y:y2,m:m2}=mData;
  const [selMedId,setSelMedId]=useState(null);
  const [difFor,setDifFor]=useState(null);
  const [difH,setDifH]=useState("");
  const [difC,setDifC]=useState("");
  /* v10.62, lot Salles : mêmes règles que dans PickMedSiteModal — internes posables
     par l'éditeur, un intermédiaire ou un cadre, sur les activités cochées 🎓, sans
     jamais compter dans l'occupation des salles ni dans les conflits. */
  const intDay=intMedsDuJour(intCfg,y2,m2,d);
  const selMed=medecins.find(x=>x.id===selMedId)||((intDay&&intDay.meds)||[]).find(x=>x.id===selMedId)||null;
  const selIsInt=!!(selMed&&intDay&&intDay.meds.some(x=>x.id===selMed.id));
  const rowActes=row.ids.map(id=>actes.find(a=>a.id===id)).filter(Boolean);
  const allAuth=new Set(rowActes.flatMap(a=>a.medecinsAutorise||[]));
  const eligMeds=medecins.filter(m=>allAuth.size===0||allAuth.has(authI(m))).filter(m=>!selfOnly||m.id===selfOnly);
  /* v10.50 : okAct = la coche du ROLE connecte (adminOk secretaires, cadreOk cadres).
     Le filtre existait ici (eligActesForMed) mais n'etait branche sur AUCUN chemin de
     pose — un role administratif pouvait donc poser (Stim…) sans pouvoir retirer. */
  const okAct=a=>!adminOnly||!!(a&&a[okKey]===true);
  const roleActes=rowActes.filter(okAct);

  const noMedMode=rowActes.length>0&&rowActes.every(a=>(a.medecinsAutorise||[]).includes("__AUCUN__"));
  const curOcc=[];
  row.ids.forEach(aid=>{
    medecins.forEach(med=>{
      getEntries(med.id,y2,m2,d,sl).forEach(e=>{
        /* v9.63 : une branche non tranchée n'occupe pas la ligne. Sans ce filtre, sur une
           colonne SANS salle fixe (Dobu, ETO, Holter) la comparaison portait sur le seul
           acteId : le praticien passait pour assigné, et disparaissait donc de la liste
           de choix depuis la v9.53 qui écarte les occupants déjà présents. */
        const match=(!e.cond)&&(row.salle?(e.acteId===aid&&e.salle===row.salle):e.acteId===aid);
        if(match&&!curOcc.find(x=>x.med.id===med.id&&x.acteId===aid)){
          const acte=actes.find(a=>a.id===aid);
          curOcc.push({med,acte,acteId:aid,e});
        }
      });
    });
    getEntries(IDE_MED.id,y2,m2,d,sl).forEach(e=>{
      const match=row.salle?(e.acteId===aid&&e.salle===row.salle):e.acteId===aid;
      if(match&&!curOcc.find(x=>x.med.id===IDE_MED.id&&x.acteId===aid))curOcc.push({med:IDE_MED,acte:actes.find(a=>a.id===aid),acteId:aid,e});
    });
  });

  /* v10.62 : les internes posés figurent dans les Assignés (croix pour canInt) */
  if(intDay)row.ids.forEach(aid=>{
    intDay.meds.forEach(im=>{
      getEntries(im.id,y2,m2,d,sl).forEach(e=>{
        if(!(e&&e.acteId)||e.cond)return;
        const match=row.salle?(e.acteId===aid&&e.salle===row.salle):e.acteId===aid;
        if(match&&!curOcc.find(x=>x.med.id===im.id&&x.acteId===aid))curOcc.push({med:im,acte:actes.find(a=>a.id===aid),acteId:aid,e,isInt:true});
      });
    });
  });
  const intActes=rowActes.filter(a=>a.interneOk===true);
  /* v10.70 : seuls les internes cochés « salles » (fiche de l'onglet Équipe) sont
     proposés ici. Les occupants déjà posés restent listés plus haut, avec leur croix. */
  const intPick=(canInt&&intDay&&intActes.length)?intDay.meds.filter(im=>im.salles===true&&!curOcc.find(x=>x.med.id===im.id)):[];
  // v9.53 : déjà dans la case, donc déjà listé au-dessus — inutile de le reproposer
  const pickMeds=eligMeds.filter(m=>!curOcc.find(x=>x.med.id===m.id));

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
          {curOcc.map(({med,acte,acteId,e,isInt},i)=>(
            <div key={i}>
            <div style={{display:"flex",flexWrap:"wrap",alignItems:"center",gap:6,padding:"5px 8px",borderRadius:7,background:"var(--bg2)",border:"1px solid var(--border)",marginBottom:4}}>
              <div style={{width:26,height:26,borderRadius:"50%",background:med.color,display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:10,fontWeight:800,border:isInt?"1.5px dashed rgba(255,255,255,.95)":"none"}}>{med.init}</div>
              <span style={{flex:1,color:"var(--txt)",fontSize:12,fontWeight:700}}>{isInt?med.nom:((med.prenom||"")+" "+(med.nom||"")).trim()}</span>
              {acte&&<span style={{padding:"2px 6px",borderRadius:4,background:acte.bg,color:acte.color,fontSize:10,fontWeight:800,fontFamily:"'JetBrains Mono',monospace"}}>{acte.short}</span>}
              {(()=>{const _rs=e&&e.salle;
                if(_rs)return <span style={{fontSize:9,fontWeight:800,fontFamily:"'JetBrains Mono',monospace",border:"1px solid var(--border)",background:"var(--bg)",borderRadius:4,padding:"1px 5px",whiteSpace:"nowrap"}}>{_rs}</span>;
                if(acte&&acte.hasSalle)return <span style={{fontSize:9,fontWeight:800,background:"#fff3cd",color:"#8a6100",border:"1px solid #f59e0b88",borderRadius:4,padding:"1px 5px",whiteSpace:"nowrap"}}>⚠ sans salle</span>;
                return null;})()}
              {row.hasSalleChoice&&acte&&acte.hasSalle&&(isInt?canInt:((!selfOnly||med.id===selfOnly)&&okAct(acte)))&&<button onClick={()=>setSelMedId(med.id)}
                style={{background:"transparent",border:"1px solid var(--border)",color:"var(--txt2)",borderRadius:5,cursor:"pointer",fontSize:9,fontWeight:800,padding:"2px 7px",whiteSpace:"nowrap"}}>salle…</button>}
              {(isInt?canInt:((!selfOnly||med.id===selfOnly)&&okAct(actes.find(a2=>a2.id===acteId))))&&<button onClick={()=>removeEntry(med.id,y2,m2,d,sl,acteId)} style={{background:"none",border:"none",color:"var(--txt2)",cursor:"pointer",fontSize:15,lineHeight:1}}>×</button>}
              {(()=>{/* v10.53 : note liée à CE médecin (jamais à la ligne IDE) */
                if(med.id===IDE_MED.id||isInt)return null;
                const _nk=nk(med.id,y2,m2,d,sl);
                const _cn=!!setNotes&&(!selfOnly||med.id===selfOnly)&&(canNotes||okAct(acte));
                if(!_cn&&!notes[_nk])return null;
                return <input value={notes[_nk]||""} readOnly={!_cn} onChange={_cn?(e=>{const v=e.target.value;setNotes(p=>({...p,[_nk]:v}));}):undefined} placeholder="📝 Note (visible au survol de la case)…" style={{flexBasis:"100%",padding:"4px 7px",borderRadius:6,border:"1px solid var(--border)",background:_cn?"var(--inp)":"var(--bg)",color:"var(--txt)",fontSize:11,outline:"none",fontFamily:"'Sora',sans-serif"}}/>;})()}
            </div>
            {canDif&&!isInt&&<div style={{margin:"-2px 0 7px 6px",display:"flex",alignItems:"center",gap:5,flexWrap:"wrap"}}>
              {(e&&e.dif)
                ?<><span style={{fontSize:10,fontWeight:800,color:"#f59e0b",border:"1px solid rgba(245,158,11,.5)",borderRadius:5,padding:"1px 5px"}}>{"🕙 départ différé"+(e.dif.c?" — "+e.dif.c:"")+(e.dif.h?" ("+e.dif.h+")":"")}</span>
                  <button onClick={()=>{if(patchAct)patchAct(med.id,y2,m2,d,sl,acteId,e.salle||null,{dif:null});}} style={{background:"none",border:"none",color:"var(--txt3)",cursor:"pointer",fontSize:10,textDecoration:"underline"}}>retirer</button></>
                :difFor===i
                  ?<><input placeholder="Qui prend le relais, à partir de quand…" value={difC} onChange={ev=>setDifC(ev.target.value)} style={{...S.fi,padding:"3px 6px",fontSize:12,flex:1,minWidth:150}}/>
                     <button onClick={()=>{if(patchAct)patchAct(med.id,y2,m2,d,sl,acteId,(e&&e.salle)||null,{dif:{c:difC}});setDifFor(null);setDifH("");setDifC("");}} style={{...S.btnP,padding:"3px 9px",fontSize:11}}>OK</button>
                     <button onClick={()=>setDifFor(null)} style={{background:"none",border:"none",color:"var(--txt3)",cursor:"pointer",fontSize:11}}>annuler</button></>
                  :<button onClick={()=>{setDifFor(i);setDifH("");setDifC("");}} style={{background:"none",border:"1px solid var(--border)",borderRadius:5,color:"var(--txt2)",cursor:"pointer",fontSize:10,padding:"1px 6px"}}>🕙 Départ différé</button>}
            </div>}
            </div>
          ))}
        </div>
      )}

      {noMedMode&&(
        <div>
          <div style={{fontSize:10,color:"var(--txt3)",fontWeight:700,textTransform:"uppercase",marginBottom:8}}>Activité sans médecin — IDE mobilisées</div>
          {roleActes.map(a=>{
            const cur=curOcc.find(x=>x.med.id===IDE_MED.id&&x.acteId===a.id);
            const val=(cur&&cur.e&&cur.e.n!==undefined&&cur.e.n!==null)?cur.e.n:(a.ideN||0);
            return(
              <div key={a.id} style={{display:"flex",alignItems:"center",gap:6,padding:"6px 8px",borderRadius:7,background:"var(--bg2)",border:"1px solid var(--border)",marginBottom:4}}>
                <Badge a={a}/>
                <span style={{flex:1,fontSize:12,fontWeight:700,color:"var(--txt)"}}>{a.label}</span>
                {cur
                  ?<>
                     <span style={{fontSize:9,color:"var(--txt3)",fontWeight:700}}>IDE</span>
                     <input type="number" min={0} max={99} value={val}
                       onChange={ev=>{const v=Math.max(0,Math.min(99,parseInt(ev.target.value||"0",10)||0));if(patchAct)patchAct(IDE_MED.id,y2,m2,d,sl,a.id,(cur.e&&cur.e.salle)||null,{n:v});}}
                       style={{...S.fi,width:54,textAlign:"center",padding:"3px 4px",fontSize:12}}/>
                     <button onClick={()=>removeEntry(IDE_MED.id,y2,m2,d,sl,a.id)} style={{background:"none",border:"none",color:"var(--txt2)",cursor:"pointer",fontSize:15,lineHeight:1}}>×</button>
                   </>
                  :<button onClick={()=>addEntry(IDE_MED.id,y2,m2,d,sl,{acteId:a.id,salle:row.salle||null,n:(a.ideN||0)})} style={{...S.btnP,padding:"4px 11px",fontSize:11}}>Poser</button>}
              </div>
            );
          })}
          <div style={{fontSize:9,color:"var(--txt3)",marginTop:6}}>Le nombre d'IDE est celui que mobilise l'activité sur ce créneau, quel que soit le nombre d'examens.</div>
        </div>
      )}

      {!selMedId&&!noMedMode&&roleActes.length===0&&(
        <div style={{fontSize:12,color:"#b45309",background:"#fff8e6",border:"1px solid #f59e0b",borderRadius:7,padding:"8px 10px"}}>✏️ Cette activité n'est pas ouverte à votre rôle — la coche se règle dans l'onglet Activités.</div>
      )}
      {!selMedId&&!noMedMode&&roleActes.length>0&&(
        <>
          <div style={{fontSize:10,color:"var(--txt3)",fontWeight:700,textTransform:"uppercase",marginBottom:8}}>Choisir un médecin</div>
          {/* Salle occupancy warning for fixed-salle rows (Stim/EEP) */}
          {row.salle&&curOcc.length>0&&(
            <div style={{display:"flex",alignItems:"center",gap:6,padding:"6px 10px",borderRadius:7,background:"rgba(245,158,11,.15)",border:"1px solid #f59e0b44",marginBottom:8}}>
              <span>⚠️</span>
              <span style={{fontSize:11,color:"#f59e0b"}}>
                {row.salle} déjà occupée par {curOcc.map(x=>x.med.init).join(", ")} — vous pouvez quand même ajouter un second médecin.
              </span>
            </div>
          )}
          <div style={{display:"flex",flexDirection:"column",gap:4,maxHeight:320,overflowY:"auto"}}>
            {pickMeds.length===0&&<div style={{fontSize:11,color:"var(--txt3)",padding:"4px 2px"}}>Tous les médecins autorisés sont déjà assignés sur ce créneau.</div>}
            {pickMeds.map(med=>{
              const avail=isMedAvailable(med,y2,m2,d,sl);
              // v9.52 : la salle occupée est annoncée UNE fois dans le bandeau au-dessus.
              // La ligne du médecin ne dit plus que ce qui le concerne LUI, et nomme son activité.
              const busyLabs=uniqArr((sl==="JOUR"?["JOUR","M","AM"]:[sl,"JOUR"])
                .flatMap(s2=>getEntries(med.id,y2,m2,d,s2)||[])
                .filter(e=>e&&e.acteId&&!e._blocked)
                .map(e=>{if(e.acteId==="TOUR_HC")return "HC";if(e.acteId==="TOUR_USIC")return "USIC";const ax=actes.find(x=>x.id===e.acteId);return (ax&&(ax.short||ax.label))||e.acteId;}).filter(Boolean));
              const borderCol=avail==="cond"?COND_C:avail==="warning"?"#f59e0b44":"var(--border)";
              const bgCol=avail==="cond"?COND_BG:avail==="warning"?"rgba(245,158,11,.15)":"var(--bg2)";
              const cIds=avail==="cond"?condOn(getEntries,med.id,y2,m2,d,sl):[];
              const cLab=cIds.map(id=>{const ax=actes.find(x=>x.id===id);return ax?ax.short:id;}).join(" / ");
              const statusTxt=avail==="blocked"?"Absent/repos":avail==="cond"?("◇ Choix ouvert — "+cLab+", non tranché"):avail==="warning"?("⚠ Déjà : "+(busyLabs.join(", ")||"une activité")):"Disponible";
              const statusCol=avail==="blocked"?"#ef4444":avail==="cond"?COND_C:avail==="warning"?"#f59e0b":"var(--txt3)";
              return(
                <button key={med.id} disabled={avail==="blocked"}
                  style={{display:"flex",alignItems:"center",gap:8,padding:"6px 9px",borderRadius:7,border:`1px solid ${borderCol}`,
                    cursor:avail!=="blocked"?"pointer":"default",background:bgCol,opacity:avail==="blocked"?.35:1}}
                  onClick={()=>{
                    if(avail==="blocked")return;
                    // If simple row (no multiActe, no salle choice) with single eligible acte → direct assign
                    const myActes=rowActes.filter(a=>!(a.medecinsAutorise&&a.medecinsAutorise.length)||a.medecinsAutorise.includes(authI(med))).filter(okAct);
                    if(!row.multiActe&&!row.hasSalleChoice&&myActes.length===1){
                      const a=myActes[0];
                      const fs=a.fixedSalle||row.salle||null;
                      addEntry(med.id,y2,m2,d,sl,{acteId:a.id,salle:fs});
                      onClose();
                    } else {
                      setSelMedId(med.id);
                    }
                  }}>
                  <div style={{width:28,height:28,borderRadius:"50%",background:med.color,display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:10,fontWeight:800}}>{med.init}</div>
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

      {!selMedId&&!noMedMode&&intPick.length>0&&(
        <>
          <div style={{fontSize:10,color:"var(--txt3)",fontWeight:700,textTransform:"uppercase",margin:"12px 0 8px",paddingTop:10,borderTop:"1px solid var(--border)"}}>{"🎓 Internes — "+intDay.lbl}</div>
          <div style={{display:"flex",flexDirection:"column",gap:4,maxHeight:220,overflowY:"auto"}}>
            {intPick.map(im=>{
              const ids=[];(sl==="JOUR"?["JOUR","M","AM"]:[sl,"JOUR"]).forEach(s2=>getEntries(im.id,y2,m2,d,s2).forEach(e=>{if(e&&e.acteId&&!e._blocked)ids.push(e.acteId);}));
              const labs=uniqArr(ids.map(id=>{if(id==="TOUR_HC")return "HC";if(id==="TOUR_USIC")return "USIC";const ax=actes.find(x=>x.id===id);return (ax&&(ax.short||ax.label))||id;}));
              const avail=ids.some(id=>ABS_IDS.indexOf(id)>=0||id==="REPOS_GARDE")?"blocked":(ids.length?"warning":"free");
              return(
                <button key={im.id} disabled={avail==="blocked"}
                  style={{display:"flex",alignItems:"center",gap:8,padding:"6px 9px",borderRadius:7,border:`1px solid ${avail==="warning"?"#f59e0b44":"var(--border)"}`,
                    cursor:avail!=="blocked"?"pointer":"default",background:avail==="warning"?"rgba(245,158,11,.15)":"var(--bg2)",opacity:avail==="blocked"?.35:1}}
                  onClick={()=>{
                    if(avail==="blocked")return;
                    if(!row.multiActe&&!row.hasSalleChoice&&intActes.length===1){
                      const a=intActes[0];
                      addEntry(im.id,y2,m2,d,sl,{acteId:a.id,salle:a.fixedSalle||row.salle||null});
                      onClose();
                    } else {
                      setSelMedId(im.id);
                    }
                  }}>
                  <div style={{width:28,height:28,borderRadius:"50%",background:im.color,display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:10,fontWeight:800,border:"1.5px dashed rgba(255,255,255,.95)"}}>{im.init}</div>
                  <div style={{textAlign:"left",flex:1}}>
                    <div style={{fontSize:12,fontWeight:700,color:"var(--txt)"}}>{im.nom}</div>
                    <div style={{fontSize:9,color:avail==="blocked"?"#ef4444":avail==="warning"?"#f59e0b":"var(--txt3)"}}>{avail==="blocked"?"Absent / FMC / repos":avail==="warning"?("⚠ Déjà : "+(labs.join(", ")||"une activité")):"Disponible"}</div>
                  </div>
                </button>
              );
            })}
          </div>
        </>
      )}
      {selMedId&&selMed&&(()=>{
        // Recompute eligible actes now that selMed is known
        const myEligActes=selIsInt?rowActes.filter(a=>a.interneOk===true):rowActes.filter(a=>!(a.medecinsAutorise&&a.medecinsAutorise.length)||a.medecinsAutorise.includes(authI(selMed))).filter(okAct);
        const isSimple=!row.multiActe&&!row.hasSalleChoice;
        return(
          <>
            <div style={{display:"flex",alignItems:"center",gap:8,marginBottom:12}}>
              <button onClick={()=>setSelMedId(null)} style={{background:"var(--bg2)",border:"1px solid var(--border)",borderRadius:6,padding:"4px 9px",cursor:"pointer",color:"var(--txt2)",fontSize:12}}>← Retour</button>
              <div style={{display:"flex",alignItems:"center",gap:6}}>
                <div style={{width:26,height:26,borderRadius:"50%",background:selMed.color,display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:10,fontWeight:800}}>{selMed.init}</div>
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
              /* v10.63 : une salle tenue par un interne se signale aussi — occupation volontaire
                 possible (supervision), mais il faut le SAVOIR avant de s'y ajouter */
              ((intDay&&intDay.meds)||[]).forEach(m=>{
                getEntries(m.id,y2,m2,d,sl).forEach(e=>{
                  if(e&&e.salle&&(row.sallesDisp||[]).includes(e.salle)){
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
                          <button key={s} style={{padding:"5px 9px",borderRadius:5,border:"1px solid #3fb95088",cursor:"pointer",fontFamily:"'JetBrains Mono',monospace",fontSize:11,fontWeight:700,background:"rgba(63,185,80,.15)",color:"#3fb950"}}
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
                          <button key={s} style={{padding:"5px 9px",borderRadius:5,border:"1px solid #f59e0b44",cursor:"pointer",fontFamily:"'JetBrains Mono',monospace",fontSize:11,fontWeight:700,background:"rgba(245,158,11,.15)",color:"#f59e0b"}}
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
function PickMedSiteModal({mData,medecins,actes,getEntries,isMedAvailable,addEntry,removeEntry,onClose,adminOnly=false,selfOnly=null,darkMode=false,okKey="adminOk",notes={},setNotes=null,canNotes=false,intCfg=null,canInt=false}){
  /* v10.92 : la liste proposee porte le nom du junior EN POSTE CE JOUR-LA. */
  {const _dj=(mData&&mData.y!=null&&mData.m!=null&&mData.d!=null)?dKey(mData.y,mData.m,mData.d):null;
   if(_dj)medecins=(medecins||[]).map(m0=>djAff(m0,_dj));}
  const {salle,siteActes,d,sl,y:y2,m:m2}=mData;
  const [step,setStep]=useState("med"); // med | acte | salle
  const [selMedId,setSelMedId]=useState(null);
  /* v10.62, lot Salles : internes du semestre — posables ici par l'éditeur, un
     intermédiaire ou un cadre, sur les seules activités cochées 🎓. Un interne posé
     avec un médecin est VOLONTAIRE (supervision) : il n'entre jamais dans le calcul
     d'occupation des salles ni dans les conflits. */
  const intDay=intMedsDuJour(intCfg,y2,m2,d);
  const selMed=medecins.find(x=>x.id===selMedId)||((intDay&&intDay.meds)||[]).find(x=>x.id===selMedId)||null;
  const selIsInt=!!(selMed&&intDay&&intDay.meds.some(x=>x.id===selMed.id));

  /* v9.58.1 : les colonnes « ↩ reprise activité » étaient câblées pour le seul BIP —
     occupants introuvables et activité proposée toujours BIP dès qu'on en créait une
     autre (SCINTI). Elles s'identifient désormais par l'activité qu'elles reprennent. */
  const recapId=mData?(mData.salle==="CHB-BIP"?"BIP":(String(mData.salle||"").indexOf("RECAP:")===0?String(mData.salle).slice(6):null)):null;
  const isRecapCol=!!recapId;
  const recapActe=recapId?actes.find(a=>a.id===recapId):null;
  const isBipCol=recapId==="BIP";
  const curOcc=[];
  siteActes.forEach(acte=>{
    medecins.forEach(med=>{
      getEntries(med.id,y2,m2,d,sl).forEach(e=>{
        /* colonne de reprise : on repère par l'ACTIVITÉ, la salle étant sans objet
           (le BIP en a une, la scintigraphie n'en a pas) ; colonne de salle : salle exacte */
        const match=isRecapCol?(e.acteId===recapId):(e.acteId===acte.id&&e.salle===salle);
        if(match&&!e.cond&&!curOcc.find(x=>x.med.id===med.id)) curOcc.push({med,acte:(isRecapCol?(recapActe||acte):acte),rs:e.salle});
      });
    });
  });
  const [selBipSalle,setSelBipSalle]=useState(null);
  /* v10.62 : les internes posés apparaissent dans les Occupants (croix pour canInt) */
  if(intDay)intDay.meds.forEach(im=>{
    getEntries(im.id,y2,m2,d,sl).forEach(e=>{
      if(!(e&&e.acteId)||e.cond)return;
      const okA=isRecapCol?(e.acteId===recapId):(e.salle===salle&&siteActes.some(a=>a.id===e.acteId));
      if(okA&&!curOcc.find(x=>x.med.id===im.id))curOcc.push({med:im,acte:(isRecapCol?(recapActe||null):siteActes.find(a=>a.id===e.acteId)),rs:e.salle,isInt:true});
    });
  });
  const intActes=isRecapCol?[recapActe].filter(a=>a&&a.interneOk===true):siteActes.filter(a=>a.interneOk===true);
  /* v10.70 : seuls les internes cochés « salles » (fiche de l'onglet Équipe) sont
     proposés ici. Les occupants déjà posés restent listés plus haut, avec leur croix. */
  const intPick=(canInt&&intDay&&intActes.length)?intDay.meds.filter(im=>im.salles===true&&!curOcc.find(x=>x.med.id===im.id)):[];
  const eligActes0=(selMed?(isRecapCol?[recapActe].filter(a=>a&&(!selIsInt||a.interneOk===true)):(selIsInt?siteActes.filter(a=>a.interneOk===true):siteActes.filter(a=>!(a.medecinsAutorise&&a.medecinsAutorise.length)||a.medecinsAutorise.includes(authI(selMed))))):[]).filter(a=>selIsInt||!adminOnly||a[okKey]===true);
  /* v9.57 : un praticien en choix ouvert n'est proposable que sur SES branches.
     Si aucune n'est offerte par cette salle, on ne le bloque pas — on le prévient. */
  const selCond=selMed?condOn(getEntries,selMed.id,y2,m2,d,sl):[];
  const condHere=eligActes0.filter(a=>selCond.indexOf(a.id)>=0);
  const eligActes=condHere.length?condHere:eligActes0;
  const condOff=selCond.length>0&&condHere.length===0;
  // v9.53 : déjà dans la case, donc déjà listé au-dessus — inutile de le reproposer
  const pickMeds=medecins.filter(med=>!selfOnly||med.id===selfOnly)
    .filter(med=>!curOcc.find(x=>x.med.id===med.id))
    .filter(med=>siteActes.some(a=>!a.medecinsAutorise||!a.medecinsAutorise.length||a.medecinsAutorise.includes(authI(med))));

  return(
    <Ov onClose={onClose}>
      <div style={S.mHd}>
        <div>
          <div style={S.mTit2}>{isRecapCol&&recapActe?("↩ "+(recapActe.label||recapActe.short)):salle} — {JOURSL[dow(y2,m2,d)]} {d} {MOIS[m2]}</div>
          <div style={{color:"var(--txt2)",fontSize:12,marginTop:2}}>{SLOTL[sl]}</div>
        </div>
        <button onClick={onClose} style={S.xBtn}>×</button>
      </div>
      {curOcc.length>0&&(
        <div style={{marginBottom:12}}>
          <div style={{fontSize:10,color:"var(--txt3)",fontWeight:700,textTransform:"uppercase",marginBottom:6}}>Occupants</div>
          {curOcc.map(({med,acte,isInt},i)=>(
            <div key={i} style={{display:"flex",flexWrap:"wrap",alignItems:"center",gap:6,padding:"5px 8px",borderRadius:7,background:"var(--bg2)",border:"1px solid var(--border)",marginBottom:4}}>
              <div style={{width:26,height:26,borderRadius:"50%",background:med.color,display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:10,fontWeight:800,border:isInt?"1.5px dashed rgba(255,255,255,.95)":"none"}}>{med.init}</div>
              <span style={{flex:1,color:"var(--txt)",fontSize:12}}>{isInt?med.nom:((med.prenom||"")+" "+(med.nom||"")).trim()}</span>
              <span style={{fontSize:10,color:acte.color,fontWeight:700,fontFamily:"'JetBrains Mono',monospace"}}>{acte.short}</span>
              {(()=>{const _r=curOcc[i]&&curOcc[i].rs;
                if(_r)return <SallePill nom={_r} acte={curOcc[i]&&curOcc[i].acte} night={darkMode}/>;
                if(acte.hasSalle)return <span style={{fontSize:9,fontWeight:800,background:"#fff3cd",color:"#8a6100",border:"1px solid #f59e0b88",borderRadius:4,padding:"1px 5px",whiteSpace:"nowrap"}}>⚠ sans salle</span>;
                return null;})()}
              {!isInt&&isRecapCol&&acte.hasSalle&&!acte.fixedSalle&&(!selfOnly||med.id===selfOnly)&&(!adminOnly||acte[okKey]===true)&&<button onClick={()=>{setSelMedId(med.id);setStep("salle");}}
                style={{background:"transparent",border:"1px solid var(--border)",color:"var(--txt2)",borderRadius:5,cursor:"pointer",fontSize:9,fontWeight:800,padding:"2px 7px",whiteSpace:"nowrap"}}>salle…</button>}
              {(isInt?canInt:((!selfOnly||med.id===selfOnly)&&(!adminOnly||acte[okKey]===true)))&&<button onClick={()=>removeEntry(med.id,y2,m2,d,sl,acte.id)} style={{background:"none",border:"none",color:"var(--txt2)",cursor:"pointer",fontSize:15,lineHeight:1}}>×</button>}
              {(()=>{if(isInt)return null;/* v10.53 : note liée à CE médecin, mêmes règles que la coche du rôle */
                const _nk=nk(med.id,y2,m2,d,sl);
                const _cn=!!setNotes&&(!selfOnly||med.id===selfOnly)&&(!adminOnly||canNotes||acte[okKey]===true);
                if(!_cn&&!notes[_nk])return null;
                return <input value={notes[_nk]||""} readOnly={!_cn} onChange={_cn?(e=>{const v=e.target.value;setNotes(p=>({...p,[_nk]:v}));}):undefined} placeholder="📝 Note (visible au survol de la case)…" style={{flexBasis:"100%",padding:"4px 7px",borderRadius:6,border:"1px solid var(--border)",background:_cn?"var(--inp)":"var(--bg)",color:"var(--txt)",fontSize:11,outline:"none",fontFamily:"'Sora',sans-serif"}}/>;})()}
            </div>
          ))}
        </div>
      )}
      {step==="med"&&(
        <>
          <div style={{fontSize:10,color:"var(--txt3)",fontWeight:700,textTransform:"uppercase",marginBottom:8}}>Choisir un médecin</div>
          <div style={{display:"flex",flexDirection:"column",gap:4,maxHeight:320,overflowY:"auto"}}>
            {pickMeds.length===0&&<div style={{fontSize:11,color:"var(--txt3)",padding:"4px 2px"}}>Tous les médecins autorisés sont déjà dans cette salle.</div>}
            {pickMeds.map(med=>{
              const avail=isMedAvailable(med,y2,m2,d,sl);
              const cIds=avail==="cond"?condOn(getEntries,med.id,y2,m2,d,sl):[];
              const cLab=cIds.map(id=>{const a=actes.find(x=>x.id===id);return a?a.short:id;}).join(" / ");
              /* v9.74 : même formulation que la modale de PT Cardio — dire LAQUELLE. */
              const busyLabs=uniqArr((sl==="JOUR"?["JOUR","M","AM"]:[sl,"JOUR"])
                .flatMap(s2=>getEntries(med.id,y2,m2,d,s2)||[])
                .filter(e=>e&&e.acteId&&!e._blocked&&!e.cond)
                .map(e=>{if(e.acteId==="TOUR_HC")return "HC";if(e.acteId==="TOUR_USIC")return "USIC";const ax=actes.find(x=>x.id===e.acteId);return (ax&&(ax.short||ax.label))||e.acteId;}).filter(Boolean));
              return(
                <button key={med.id} disabled={avail==="blocked"}
                  style={{display:"flex",alignItems:"center",gap:8,padding:"6px 9px",borderRadius:7,border:`1px ${avail==="cond"?"dashed "+COND_C:"solid "+(avail==="warning"?"#f59e0b44":"var(--border)")}`,
                    cursor:avail!=="blocked"?"pointer":"default",background:avail==="cond"?COND_BG:avail==="warning"?"rgba(245,158,11,.15)":"var(--bg2)",opacity:avail==="blocked"?.35:1}}
                  onClick={()=>{ if(avail==="blocked")return; setSelMedId(med.id); setStep("acte"); }}>
                  <div style={{width:28,height:28,borderRadius:"50%",background:med.color,display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:10,fontWeight:800}}>{med.init}</div>
                  <div style={{textAlign:"left"}}>
                    <div style={{fontSize:12,fontWeight:700,color:"var(--txt)"}}>{med.prenom} {med.nom}</div>
                    <div style={{fontSize:9,color:avail==="blocked"?"#ef4444":avail==="cond"?COND_C:avail==="warning"?"#f59e0b":"var(--txt3)"}}>{avail==="blocked"?"Absent/repos":avail==="cond"?("◇ Choix ouvert — "+cLab+", non tranché"):avail==="warning"?("⚠ Déjà : "+(busyLabs.join(", ")||"une activité")):"Disponible"}</div>
                  </div>
                </button>
              );
            })}
          </div>
        </>
      )}
      {step==="med"&&intPick.length>0&&(
        <>
          <div style={{fontSize:10,color:"var(--txt3)",fontWeight:700,textTransform:"uppercase",margin:"12px 0 8px",paddingTop:10,borderTop:"1px solid var(--border)"}}>{"🎓 Internes — "+intDay.lbl}</div>
          <div style={{display:"flex",flexDirection:"column",gap:4,maxHeight:220,overflowY:"auto"}}>
            {intPick.map(im=>{
              const ids=[];(sl==="JOUR"?["JOUR","M","AM"]:[sl,"JOUR"]).forEach(s2=>getEntries(im.id,y2,m2,d,s2).forEach(e=>{if(e&&e.acteId&&!e._blocked)ids.push(e.acteId);}));
              const labs=uniqArr(ids.map(id=>{if(id==="TOUR_HC")return "HC";if(id==="TOUR_USIC")return "USIC";const ax=actes.find(x=>x.id===id);return (ax&&(ax.short||ax.label))||id;}));
              const avail=ids.some(id=>ABS_IDS.indexOf(id)>=0||id==="REPOS_GARDE")?"blocked":(ids.length?"warning":"free");
              return(
                <button key={im.id} disabled={avail==="blocked"}
                  style={{display:"flex",alignItems:"center",gap:8,padding:"6px 9px",borderRadius:7,border:`1px solid ${avail==="warning"?"#f59e0b44":"var(--border)"}`,
                    cursor:avail!=="blocked"?"pointer":"default",background:avail==="warning"?"rgba(245,158,11,.15)":"var(--bg2)",opacity:avail==="blocked"?.35:1}}
                  onClick={()=>{ if(avail==="blocked")return; setSelMedId(im.id); setStep("acte"); }}>
                  <div style={{width:28,height:28,borderRadius:"50%",background:im.color,display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:10,fontWeight:800,border:"1.5px dashed rgba(255,255,255,.95)"}}>{im.init}</div>
                  <div style={{textAlign:"left"}}>
                    <div style={{fontSize:12,fontWeight:700,color:"var(--txt)"}}>{im.nom}</div>
                    <div style={{fontSize:9,color:avail==="blocked"?"#ef4444":avail==="warning"?"#f59e0b":"var(--txt3)"}}>{avail==="blocked"?"Absent / FMC / repos":avail==="warning"?("⚠ Déjà : "+(labs.join(", ")||"une activité")):"Disponible"}</div>
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
              <div style={{width:26,height:26,borderRadius:"50%",background:selMed.color,display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:10,fontWeight:800}}>{selMed.init}</div>
              <span style={{color:"var(--txt)",fontSize:12,fontWeight:700}}>{selMed.prenom} {selMed.nom}</span>
            </div>
          </div>
          {!selIsInt&&curOcc.length>0&&<div style={{display:"flex",alignItems:"center",gap:6,padding:"6px 10px",borderRadius:7,background:"rgba(245,158,11,.15)",border:"1px solid #f59e0b44",marginBottom:10}}>
            <span>⚠️</span><span style={{fontSize:11,color:"#f59e0b"}}>Cette salle a déjà {curOcc.length} praticien(s) assigné(s). Confirmer quand même ?</span>
          </div>}
          {selCond.length>0&&<div style={{fontSize:10,color:COND_C,fontWeight:700,marginBottom:8,padding:"5px 8px",borderRadius:6,border:"1.5px dashed "+COND_C,background:COND_BG,lineHeight:1.45}}>
            {condOff
              ? "◇ Ce praticien est sur un choix ouvert, dont aucune branche n'est proposée dans cette salle. Poser une activité ici tranchera son choix et retirera ses branches."
              : "◇ Choix ouvert — seules ses branches sont proposées. En attribuer une avec sa salle tranchera le choix."}
          </div>}
          <div style={{fontSize:10,color:"var(--txt3)",fontWeight:700,textTransform:"uppercase",marginBottom:8}}>Activité dans {salle}</div>
          <div style={S.actGrd}>
            {eligActes.map(a=>(
              <button key={a.id} style={{...S.actTog,background:a.color,color:"#111",outline:`1px solid ${a.color}55`}}
                onClick={()=>{
                  /* une colonne de reprise ne demande une salle que si l'activité en a une */
                  /* v9.67.1 : TOUTE colonne de suivi dont l'activité déclare des salles passe par le choix de salle */
                  if(isRecapCol&&a.hasSalle&&!a.fixedSalle){setStep("salle");return;}
                  if(isRecapCol){addEntry(selMed.id,y2,m2,d,sl,{acteId:a.id,salle:a.fixedSalle||null});onClose();return;}
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
      {step==="salle"&&selMed&&isRecapCol&&(
        <>
          <div style={{display:"flex",alignItems:"center",gap:8,marginBottom:12}}>
            <button onClick={()=>setStep("acte")} style={{background:"var(--bg2)",border:"1px solid var(--border)",borderRadius:6,padding:"4px 9px",cursor:"pointer",color:"var(--txt2)",fontSize:12}}>← Retour</button>
            <div style={{display:"flex",alignItems:"center",gap:6}}>
              <div style={{width:26,height:26,borderRadius:"50%",background:selMed.color,display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:10,fontWeight:800}}>{selMed.init}</div>
              <span style={{color:"var(--txt)",fontSize:12,fontWeight:700}}>{selMed.prenom} {selMed.nom}</span>
            </div>
          </div>
          <div style={{fontSize:10,color:"var(--txt3)",fontWeight:700,textTransform:"uppercase",marginBottom:8}}>Choisir la salle {recapActe&&recapActe.short?recapActe.short:""}</div>
          <div style={{display:"flex",flexDirection:"column",gap:6}}>
            {((recapActe&&recapActe.salles&&recapActe.salles.length)?recapActe.salles:["CHB-1","CHB-2","CHB-3"]).map(s=>{
              // Check if salle is occupied by ANY activity
              const salleOccs=medecins.filter(m=>{
                const es=getEntries(m.id,y2,m2,d,sl);
                return es.some(e=>e.salle===s);
              }).concat(((intDay&&intDay.meds)||[]).filter(im=>getEntries(im.id,y2,m2,d,sl).some(e=>e&&e.salle===s)));
              const occupied=salleOccs.length>0;
              return(
                <button key={s}
                  style={{...S.actTog,
                    background:occupied?"#fee2e2":"#46bdc6",
                    color:occupied?"#dc2626":"#111",
                    fontWeight:700,fontSize:13,
                    border:occupied?"1px solid #fca5a5":"1px solid #46bdc6"}}
                  onClick={()=>{ addEntry(selMed.id,y2,m2,d,sl,{acteId:(recapId||"BIP"),salle:s}); onClose(); }}>
                  <span>{recapId==="BIP"?("Salle "+s.replace("CHB-","")):s}</span>
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
  const [acteId,curSalle,acteId2=null,curSalle2=null,acteId3=null,curSalle3=null,c1flag=null]=((pt[dayOfWeek]||{})[slot])||[null,null];
  const brs=[[acteId,curSalle],[acteId2,curSalle2],[acteId3,curSalle3]];
  const nBr=brs.filter(b=>b[0]).length;
  /* v9.69 : « en attente » et « choix ouvert » étaient deux noms pour la même chose et
     deux boutons pour y arriver. Un seul concept désormais : un choix ouvert a de 1 à 3
     branches. `isC` dit si la case est conditionnelle, quel que soit le nombre. */
  const isC=nBr>1||!!c1flag;
  const addIdx=(mData&&mData._ptAdd)||null;   // 2 ou 3 : la branche en cours d'ajout
  const jours=["","Lundi","Mardi","Mercredi","Jeudi","Vendredi"];
  const writePT=(arr)=>setPlanningType(p=>({...p,[medId]:{...p[medId],[dayOfWeek]:{...((p[medId]||{})[dayOfWeek]||{}),[slot]:arr}}}));
  const flushBrs=(list)=>{const k=list.filter(b=>b&&b[0]);const arr=k.length?k.reduce((acc,b)=>acc.concat([b[0],b[1]||null]),[]):[null,null];writePT((k.length===1&&c1flag)?arr.concat([null,null,null,null,1]):arr);};
  const setPT=(aId,salle)=>{const list=brs.slice();list[addIdx?addIdx-1:0]=[aId,salle];flushBrs(list);};
  const dropBr=(i)=>{const list=brs.slice();list[i]=[null,null];flushBrs(list);};
  const afterPick=()=>setMData(p=>({...p,_ptPickSalle:null,_ptAdd:null}));
  const eligActes=actes.filter(a=>!SYS.includes(a.id)&&(!(a.medecinsAutorise&&a.medecinsAutorise.length)||a.medecinsAutorise.includes(authI(med))));

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
        <div style={{display:"flex",alignItems:"center",gap:6,marginBottom:10,padding:"6px 10px",background:isC?COND_BG:"var(--bg)",borderRadius:8,border:isC?"1.5px dashed "+COND_C:"1px solid var(--border)"}}>
          <span style={{fontSize:11,color:isC?COND_C:"var(--txt3)",fontWeight:700}}>{isC?"Choix ouvert ①":"Activité actuelle :"}</span>
          <Badge a={cur}/>
          <span style={{fontSize:10,color:"var(--txt3)",fontStyle:curSalle?"normal":"italic"}}>{curSalle||"sans salle"}</span>
          <button onClick={()=>{dropBr(0);afterPick();}} style={{marginLeft:"auto",background:"#fee2e2",border:"1px solid #fca5a5",borderRadius:4,color:"#dc2626",cursor:"pointer",fontSize:12,fontWeight:900,padding:"1px 6px"}}>×</button>
        </div>
      ):null;})()}
      {acteId2&&(()=>{const cur2=actes.find(x=>x.id===acteId2);return cur2?(
        <div style={{display:"flex",alignItems:"center",gap:6,marginBottom:10,padding:"6px 10px",background:"var(--bg)",borderRadius:8,border:"1px solid var(--border)"}}>
          <span style={{fontSize:11,color:COND_C,fontWeight:700}}>Choix ouvert ②</span>
          <Badge a={cur2}/>
          <span style={{fontSize:10,color:"var(--txt3)",fontStyle:curSalle2?"normal":"italic"}}>{curSalle2||"sans salle"}</span>
          <button onClick={()=>{dropBr(1);afterPick();}} style={{marginLeft:"auto",background:"#fee2e2",border:"1px solid #fca5a5",borderRadius:4,color:"#dc2626",cursor:"pointer",fontSize:12,fontWeight:900,padding:"1px 6px"}}>×</button>
        </div>):null;})()}
      {acteId3&&(()=>{const cur3=actes.find(x=>x.id===acteId3);return cur3?(
        <div style={{display:"flex",alignItems:"center",gap:6,marginBottom:10,padding:"6px 10px",background:COND_BG,borderRadius:8,border:"1.5px dashed "+COND_C}}>
          <span style={{fontSize:11,color:COND_C,fontWeight:700}}>Choix ouvert ③</span>
          <Badge a={cur3}/>
          <span style={{fontSize:10,color:"var(--txt3)",fontStyle:curSalle3?"normal":"italic"}}>{curSalle3||"sans salle"}</span>
          <button onClick={()=>{dropBr(2);afterPick();}} style={{marginLeft:"auto",background:"#fee2e2",border:"1px solid #fca5a5",borderRadius:4,color:"#dc2626",cursor:"pointer",fontSize:12,fontWeight:900,padding:"1px 6px"}}>×</button>
        </div>):null;})()}
      {acteId&&!isC&&!addIdx&&<button style={{marginBottom:10,marginRight:8,padding:"5px 11px",borderRadius:6,border:"1.5px dashed "+COND_C,background:COND_BG,color:COND_C,cursor:"pointer",fontSize:11,fontWeight:700}}
        onClick={()=>writePT([acteId,curSalle||null,null,null,null,null,1])}>◇ Transformer en choix ouvert</button>}
      {acteId&&isC&&nBr<3&&!addIdx&&<button style={{marginBottom:10,marginRight:8,padding:"5px 11px",borderRadius:6,border:"1.5px dashed "+COND_C,background:COND_BG,color:COND_C,cursor:"pointer",fontSize:11,fontWeight:700}} onClick={()=>setMData(p=>({...p,_ptAdd:nBr+1}))}>{nBr===1?"◇ Ajouter une 2e branche":"◇ Ajouter une 3e branche"}</button>}
      {acteId&&isC&&nBr===1&&!addIdx&&<button style={{marginBottom:10,padding:"5px 11px",borderRadius:6,border:"1.5px solid #16a34a",background:"#f0fdf4",color:"#16a34a",cursor:"pointer",fontSize:11,fontWeight:800}}
        onClick={()=>writePT([acteId,curSalle||null])}>✓ Confirmer l’activité</button>}
      {addIdx&&<div style={{marginBottom:8,fontSize:11,color:COND_C,fontWeight:700}}>◇ Choisissez la branche {addIdx===2?"②":"③"} du choix ouvert ci-dessous</div>}
      {isC&&!addIdx&&<div style={{marginBottom:8,fontSize:10,color:"var(--txt3)",lineHeight:1.45}}>{nBr>1?"Le praticien restera disponible pour ces activités tant que le choix n'est pas tranché.":"Branche unique : n'occupe aucune salle ni IDE tant que ce n'est pas tranché."}</div>}
      <div style={S.actGrd}>
{eligActes.map(a=>{
          const tgt=addIdx===2?acteId2:addIdx===3?acteId3:acteId;
          const on=tgt===a.id;const locked=!on&&(!!tgt||[acteId,acteId2,acteId3].filter(Boolean).includes(a.id));
          return(
            <button key={a.id} style={{...S.actTog,
              background:a.color,color:"#111",
              border:`2px solid ${on?"#1d4ed8":a.color}`,
              fontWeight:900,opacity:on?1:(locked?0.22:0.8),pointerEvents:locked?"none":"auto",filter:locked?"grayscale(.7)":"none"}}
              onClick={()=>{ if(a.hasSalle) setMData(p=>({...p,_ptPickSalle:a.id})); else{ setPT(a.id,null); afterPick(); } }}>
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
                onClick={()=>{ setPT(a.id,null); afterPick(); }}>Sans salle</button>
              {(a.salles||[]).map(s=>{
                const usedBy=medecins.filter(o=>o.id!==medId).find(o=>{
                  const op=planningType[o.id]||{};
                  const oe=((op[dayOfWeek]||{})[slot])||[];
                  return oe[1]===s||oe[3]===s; // salle occupée quelle que soit l'activité
                });
                const usedActe=usedBy?(()=>{const oe2=((planningType[usedBy.id]||{})[dayOfWeek]||{})[slot]||[];const aid2=oe2[1]===s?oe2[0]:oe2[2];return(actes.find(x=>x.id===aid2)||{}).short;})():null;
                return(
                  <button key={s} title={usedBy?`⚠ Occupée par Dr. ${usedBy.nom}${usedActe?" ("+usedActe+")":""}`:""}
                    style={{padding:"5px 9px",borderRadius:5,border:`1px solid ${usedBy?"#f59e0b":"var(--border)"}`,cursor:"pointer",fontFamily:"'JetBrains Mono',monospace",fontSize:11,fontWeight:700,background:curSalle===s?a.color:usedBy?"rgba(245,158,11,.15)":"var(--bg2)",color:curSalle===s?"#fff":usedBy?"#f59e0b":"var(--txt2)"}}
                    onClick={()=>{ setPT(a.id,s); afterPick(); }}>{s}{usedBy?" ⚠":""}</button>
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
/* v9.92 : ÉCRAN UNIFIÉ « Modifier sur une période ». Il remplace trois boutons de la
   modale de case — poser/retirer une absence, effacer les activités, effacer le mois —
   qui posaient au fond la même question : quoi, sur quelle période, pour qui.
   Vérifié avant fusion : « effacer le mois » appelait la MÊME fonction que le retrait du
   planning type, avec la même liste de conservation que la case à cocher. Rien n'est
   donc perdu, et il n'y a plus qu'un seul écran à faire évoluer.
   Les demi-journées de début et de fin sont réglables mais déjà sur le bon défaut
   (matin → après-midi), le cas courant restant « deux dates et je valide ».
   Un week-end n'ayant qu'une case JOUR, les demi-journées y sont ignorées : c'est déjà
   le comportement de toutes les fonctions appelées ici. */
/* v10.2 : la restauration ciblée, depuis la modale de case — là où l'on est quand on
   s'aperçoit de la perte. Réservée à l'éditeur : restaurer écrase le travail d'autrui sur
   la période, ce n'est pas le même risque que modifier ses propres cases. */
function RestoreModal({med,backups,y,m,d,onDiff,onGo,onClose}){
  const f=dt=>`${dt.getFullYear()}-${String(dt.getMonth()+1).padStart(2,"0")}-${String(dt.getDate()).padStart(2,"0")}`;
  const jour=new Date(y,m,d);
  const lun=new Date(y,m,d);lun.setDate(lun.getDate()-((lun.getDay()+6)%7));
  const dim=new Date(lun);dim.setDate(dim.getDate()+6);
  const m1=new Date(y,m,1), m2=new Date(y,m+1,0);
  const court=dt=>dt.toLocaleDateString("fr-FR",{day:"numeric",month:"short"});
  const CHOIX=[
    {id:"jour",lab:"Ce jour",det:court(jour),df:f(jour),dt:f(jour)},
    {id:"sem",lab:"Cette semaine",det:court(lun)+" au "+court(dim),df:f(lun),dt:f(dim)},
    {id:"mois",lab:"Ce mois",det:court(m1)+" au "+court(m2),df:f(m1),dt:f(m2)},
    {id:"libre",lab:"Deux dates",det:"au choix",df:null,dt:null}];
  const [bkId,setBkId]=useState(backups.length?backups[0].id:"");
  const [ch,setCh]=useState("jour");
  const [df,setDf]=useState(f(jour)); const [dt2,setDt2]=useState(f(jour));
  const [bilan,setBilan]=useState(null);
  const sel=CHOIX.find(c=>c.id===ch)||CHOIX[0];
  const rDf=sel.df||df, rDt=sel.dt||dt2;
  const bk=backups.find(b=>b.id===bkId);
  const ok=bkId&&rDf&&rDt&&rDt>=rDf;
  const libBk=(b)=>{
    if(!b)return "—";
    const j=Math.floor((Date.now()-b.ts)/86400000);
    const h=new Date(b.ts).toLocaleTimeString("fr-FR",{hour:"2-digit",minute:"2-digit"});
    if(j<=0)return "Aujourd'hui — "+h;
    if(j===1)return "Hier soir — "+h;
    if(j===2)return "Avant-hier — "+h;
    return new Date(b.ts).toLocaleDateString("fr-FR",{weekday:"short",day:"2-digit",month:"short"})+" — "+h;
  };
  const seg=on=>({flex:"1 1 auto",minWidth:96,padding:"7px 6px",borderRadius:7,cursor:"pointer",fontWeight:800,fontSize:11.5,
    border:"1.5px solid "+(on?"#16a34a":"var(--border)"),background:on?"#f0fdf4":"var(--bg2)",color:on?"#166534":"var(--txt2)"});

  if(bilan) return(
    <div style={{minWidth:320,maxWidth:400}}>
      <div style={S.mHd}><div style={{...S.mTit2,color:"#166534"}}>↩ Confirmer la restauration</div></div>
      <div style={{fontSize:12.5,lineHeight:1.6}}>
        État du <b>{libBk(bk)}</b><br/>pour <b>{med?med.prenom+" "+med.nom:"—"}</b><br/>
        sur <b>{sel.id==="libre"?("du "+rDf+" au "+rDt):(sel.lab.toLowerCase()+" — "+sel.det)}</b>.
      </div>
      <div style={{marginTop:10,borderRadius:9,border:"1px solid var(--border)",overflow:"hidden"}}>
        <div style={{display:"flex",gap:8,padding:"8px 10px",fontSize:12,borderBottom:"1px solid var(--border)",background:"#f0fdf4",color:"#166534",fontWeight:700}}>＋ {bilan.nAdd} activité{bilan.nAdd>1?"s":""} remise{bilan.nAdd>1?"s":""}</div>
        <div style={{display:"flex",gap:8,padding:"8px 10px",fontSize:12,borderBottom:"1px solid var(--border)",background:"#fee2e2",color:"#991b1b",fontWeight:700}}>－ {bilan.nDel} case{bilan.nDel>1?"s":""} supprimée{bilan.nDel>1?"s":""}</div>
        <div style={{display:"flex",gap:8,padding:"8px 10px",fontSize:12,background:"var(--bg2)",color:"var(--txt3)"}}>＝ {bilan.nSame} déjà identique{bilan.nSame>1?"s":""}</div>
      </div>
      {(bilan.nAdd>0||bilan.nDel>0)&&<div style={{marginTop:8}}>
        {bilan.detA.length>0&&<><div style={{fontSize:9.5,fontWeight:800,color:"#166534",textTransform:"uppercase"}}>Remises</div>
          <div>{bilan.detA.map(x=><span key={x.lab} style={{display:"inline-block",fontSize:10,fontWeight:800,padding:"2px 7px",borderRadius:11,margin:"2px 3px 0 0",background:"rgba(22,163,74,.12)",border:"1px solid #86efac",color:"#166534"}}>{x.n} × {x.lab}</span>)}</div></>}
        {bilan.detD.length>0&&<><div style={{fontSize:9.5,fontWeight:800,color:"#991b1b",textTransform:"uppercase",marginTop:6}}>Supprimées</div>
          <div>{bilan.detD.map(x=><span key={x.lab} style={{display:"inline-block",fontSize:10,fontWeight:800,padding:"2px 7px",borderRadius:11,margin:"2px 3px 0 0",background:"rgba(220,38,38,.10)",border:"1px solid #fca5a5",color:"#991b1b"}}>{x.n} × {x.lab}</span>)}</div></>}
      </div>}
      {bilan.nAdd===0&&bilan.nDel===0&&<div style={{marginTop:8,fontSize:11.5,color:"#b45309",fontWeight:700}}>Rien à restaurer — cette sauvegarde est identique à l'état actuel. Essayez une sauvegarde plus ancienne.</div>}
      <div style={{display:"flex",gap:6,marginTop:12}}>
        <button style={seg(false)} onClick={()=>setBilan(null)}>← Retour</button>
        <button disabled={bilan.nAdd===0&&bilan.nDel===0} style={{...S.btnP,flex:1,background:"#16a34a",opacity:(bilan.nAdd===0&&bilan.nDel===0)?.5:1}}
          onClick={()=>onGo(bkId,rDf,rDt)}>Restaurer</button>
      </div>
    </div>
  );

  return(
    <div style={{minWidth:320,maxWidth:400}}>
      <div style={S.mHd}>
        <div style={S.mTit2}>↩ Restaurer — {med?med.prenom+" "+med.nom:""}</div>
        <button onClick={onClose} style={S.xBtn}>×</button>
      </div>
      <div style={{fontSize:11.5,color:"var(--txt2)",marginBottom:10,lineHeight:1.5}}>
        Seules les cases de ce médecin, sur ces dates, seront remises dans l'état de la sauvegarde. Le reste du planning n'est pas touché.
      </div>
      <label style={S.fl}>Sauvegarde</label>
      <select value={bkId} onChange={e=>setBkId(e.target.value)} style={{...S.fi,width:"100%"}}>
        {backups.length===0&&<option value="">Aucune sauvegarde</option>}
        {backups.map(b=><option key={b.id} value={b.id}>{libBk(b)}</option>)}
      </select>
      <label style={{...S.fl,marginTop:10,display:"block"}}>Période</label>
      <div style={{display:"flex",gap:5,flexWrap:"wrap"}}>
        {CHOIX.map(c=>(
          <button key={c.id} onClick={()=>setCh(c.id)} style={seg(ch===c.id)}>
            {c.lab}<div style={{fontSize:9.5,fontWeight:600,opacity:.8,marginTop:1}}>{c.det}</div>
          </button>))}
      </div>
      {ch==="libre"&&<div style={{display:"flex",gap:6,marginTop:8}}>
        <input type="date" value={df} onChange={e=>setDf(e.target.value)} style={{...S.fi,flex:1}}/>
        <input type="date" value={dt2} onChange={e=>setDt2(e.target.value)} style={{...S.fi,flex:1}}/>
      </div>}
      <button disabled={!ok} onClick={async()=>{const r=await onDiff(bkId,rDf,rDt);if(r)setBilan(r);}}
        style={{...S.btnP,width:"100%",marginTop:13,background:"#16a34a",opacity:ok?1:.5}}>
        Comparer…
      </button>
    </div>
  );
}

/* v10.18 : « Coller un calendrier ». On colle le texte du site officiel ; les dates sont
   repérées puis PROPOSÉES — rien n'est enregistré sans validation. C'est ce qui permet de
   garder la commodité d'une source extérieure sans lui laisser toucher les données. */
function VacCollerModal({onClose,onValider}){
  const [txt,setTxt]=useState("");
  const [prop,setProp]=useState(null);
  const MOISN={janvier:0,"février":1,fevrier:1,mars:2,avril:3,mai:4,juin:5,juillet:6,"août":7,aout:7,septembre:8,octobre:9,novembre:10,"décembre":11,decembre:11};
  const analyser=()=>{
    const t=txt.toLowerCase().replace(/\s+/g," ");
    const dre="(\\d{1,2})(?:er)? ([a-zéûà]+) (\\d{4})";
    const re=new RegExp("du "+dre+" au "+dre,"g");
    const out=[];let m2,n=0;
    while((m2=re.exec(t))!==null){
      const mm1=MOISN[m2[2]],mm2=MOISN[m2[5]];
      if(mm1===undefined||mm2===undefined)continue;
      const f=(y,mo,d)=>y+"-"+String(mo+1).padStart(2,"0")+"-"+String(d).padStart(2,"0");
      const d1=f(+m2[3],mm1,+m2[1]),d2=f(+m2[6],mm2,+m2[4]);
      const y1=+m2[3],an=(mm1>=7)?(y1+"-"+(y1+1)):((y1-1)+"-"+y1);
      out.push({an,nom:VAC_NOMS[n%5],d1,d2});n++;
    }
    setProp(out);
  };
  return(
    <div style={{minWidth:320,maxWidth:460}}>
      <div style={S.mHd}><div style={S.mTit2}>📋 Coller un calendrier</div><button onClick={onClose} style={S.xBtn}>×</button></div>
      {!prop?<>
        <div style={{fontSize:11.5,color:"var(--txt2)",marginBottom:8,lineHeight:1.5}}>
          Copiez le texte depuis le site officiel — ou n'importe quelle source — et collez-le ici.
          Les mentions « du … au … » seront repérées et proposées avant enregistrement.
        </div>
        <textarea value={txt} onChange={e=>setTxt(e.target.value)} rows={7}
          placeholder="ex. Vacances d'hiver : du samedi 13 février 2027 au lundi 1er mars 2027"
          style={{...S.fi,width:"100%",fontSize:12,fontFamily:"inherit"}}/>
        <button onClick={analyser} disabled={!txt.trim()} style={{...S.btnP,width:"100%",marginTop:10,opacity:txt.trim()?1:.5}}>Analyser</button>
      </>:<>
        {prop.length===0
          ? <div style={{fontSize:12,color:"#b45309",fontWeight:700}}>Aucune date reconnue. Vérifiez que le texte contient des mentions « du … au … », ou saisissez les dates à la main.</div>
          : <>
            <div style={{fontSize:11.5,color:"var(--txt2)",marginBottom:8}}>Vérifiez avant d'enregistrer. Les noms sont attribués dans l'ordre habituel — corrigez-les ensuite si besoin.</div>
            <table style={{width:"100%",borderCollapse:"collapse",fontSize:12}}><tbody>
              {prop.map((v,i)=>(<tr key={i}>
                <td style={{padding:"3px 6px",borderBottom:"1px solid var(--border)",fontWeight:700,width:76}}>{v.nom}</td>
                <td style={{padding:"3px 6px",borderBottom:"1px solid var(--border)",fontSize:11}}>{fmtLong(v.d1)}</td>
                <td style={{padding:"3px 6px",borderBottom:"1px solid var(--border)",fontSize:11}}>{fmtLong(v.d2)}</td>
              </tr>))}
            </tbody></table>
          </>}
        <div style={{display:"flex",gap:6,marginTop:12}}>
          <button style={{...S.icnBtn,flex:1,width:"auto"}} onClick={()=>setProp(null)}>← Retour</button>
          <button disabled={!prop.length} style={{...S.btnP,flex:1,opacity:prop.length?1:.5}} onClick={()=>onValider(prop)}>Enregistrer</button>
        </div>
      </>}
    </div>
  );
}

/* v10.114 : bornes du mode « la semaine » de l'écran de période. Pour une ABSENCE
   (pose, ou retrait ciblé absences/FMC), la semaine embarque le week-end précédent,
   le week-end suivant et les jours fériés ACCOLÉS — sa règle du 25/08/2026 : la
   semaine du 24 août va du samedi 22 au dimanche 30 ; celle du 25 octobre 2027
   court jusqu'au lundi 1er novembre (férié accolé au dimanche). Un férié séparé
   du week-end par un jour ouvré n'est pas pris. */
function semRange(base,abs){
  const lun=new Date(base.getFullYear(),base.getMonth(),base.getDate()-((base.getDay()+6)%7));
  let deb=new Date(lun),fin=new Date(lun);fin.setDate(fin.getDate()+6);
  if(abs){
    deb.setDate(deb.getDate()-2);
    for(let g=0;g<4;g++){const v=new Date(deb);v.setDate(v.getDate()-1);
      if(isFerie(v.getFullYear(),v.getMonth(),v.getDate()))deb=v;else break;}
    for(let g=0;g<4;g++){const v=new Date(fin);v.setDate(v.getDate()+1);
      if(isFerie(v.getFullYear(),v.getMonth(),v.getDate()))fin=v;else break;}
  }
  return {deb,fin};
}
function PeriodModal({medecins,initMedId,initDate,year,month,mois=[],finPer=null,allowActs=true,compter,onPose,onRetraitAbs,onEffacer,onClose}){
  const fmt=d=>`${d.getFullYear()}-${String(d.getMonth()+1).padStart(2,"0")}-${String(d.getDate()).padStart(2,"0")}`;
  const [action,setAction]=useState("poser");        // poser | retirer
  const [cible,setCible]=useState("abs");            // abs | activites | tout   (si retirer)
  const [degre,setDegre]=useState("garde");          // garde = gardes/repos/tour conservés · absolu = tout part
  const [absType,setAbsType]=useState("ABSENCE");    // ABSENCE | FORMATION
  const [medId,setMedId]=useState(initMedId||null);
  const [df,setDf]=useState(initDate||"");
  const [dt,setDt]=useState(initDate||"");
  const [slDeb,setSlDeb]=useState("M");
  const [slFin,setSlFin]=useState("AM");
  /* v10.75 : trois facons de designer la periode. « La semaine » porte sur la semaine
     du jour clique, du lundi au dimanche (sa demande : clic le jeudi 20 -> 17 au 23). */
  const [mode,setMode]=useState("dates");            // dates | semaine | mois
  const moisEntier=mode==="mois", semEntier=mode==="semaine";
  /* v9.96 : « mois entier » ne se limite plus au mois affiché — on choisit parmi les
     mois de la période, ce qui évite de naviguer avant d'effacer. */
  const moisList=(mois&&mois.length)?mois:[{y:year,m:month}];
  /* v9.97 : plusieurs mois à la fois — on peut déjà couvrir plusieurs mois avec deux
     dates, autant pouvoir le faire par mois. */
  const [moisSel,setMoisSel]=useState(()=>{const i=moisList.findIndex(x=>x.y===year&&x.m===month);return [i<0?0:i];});
  const togMois=(i)=>setMoisSel(p=>p.includes(i)?(p.length>1?p.filter(x=>x!==i):p):p.concat([i]).sort((a,b)=>a-b));
  const iDeb=moisSel.length?Math.min(...moisSel):0, iFin=moisSel.length?Math.max(...moisSel):0;
  const mDeb=moisList[iDeb]||{y:year,m:month}, mFin=moisList[iFin]||{y:year,m:month};
  /* La période ne s'arrête pas au dernier jour du mois : elle court jusqu'au dimanche qui
     clôt la dernière semaine, et rattache le lundi suivant s'il est férié. Choisir le
     DERNIER mois de la période doit donc effacer jusqu'à cette fin réelle — sinon un
     1er ou 2 novembre appartenant à la période resterait en place. */
  const finReelle=(iFin===moisList.length-1&&finPer)?finPer:fmt(new Date(mFin.y,mFin.m+1,0));
  const [keepAbs,setKeepAbs]=useState(true);
  const [confirm,setConfirm]=useState(null);
  const med=medecins.find(m=>m.id===medId);

  const moisDeb=fmt(new Date(mDeb.y,mDeb.m,1)), moisFin=finReelle;
  /* la semaine du jour clique : lundi -> dimanche, traverse mois et annees */
  const semBase=(()=>{const s=initDate||df||fmt(new Date());const p2=s.split("-").map(Number);return new Date(p2[0],(p2[1]||1)-1,p2[2]||1);})();
  /* v10.114 : pour une ABSENCE (pose, ou retrait ciblé absences/FMC), la semaine
     embarque les week-ends et les fériés accolés — sa règle du 25/08/2026. */
  const semAbs=action==="poser"||cible==="abs";
  const {deb:semDeb,fin:semFin}=semRange(semBase,semAbs);
  const rDf=moisEntier?moisDeb:semEntier?fmt(semDeb):df, rDt=moisEntier?moisFin:semEntier?fmt(semFin):dt;
  const rDeb=(moisEntier||semEntier)?"M":slDeb, rFin=(moisEntier||semEntier)?"AM":slFin;
  const nbJours=(()=>{ if(!rDf||!rDt)return 0;
    const a=new Date(rDf),b=new Date(rDt); if(b<a)return 0;
    return Math.round((b-a)/86400000)+1; })();
  const ok=medId&&rDf&&rDt&&nbJours>0;

  const libAction=action==="poser"
    ? (absType==="FORMATION"?"Poser une formation":"Poser une absence")
    : (cible==="abs"?"Retirer les absences et FMC"
       :cible==="tout"?(degre==="absolu"?"Tout retirer, gardes et tour compris":"Tout retirer sauf gardes et tour")
       :"Effacer les activités");
  const libPeriode=!ok?"—":semEntier
    ? `semaine du ${semDeb.getDate()} ${MOIS[semDeb.getMonth()].toLowerCase()} au ${semFin.getDate()} ${MOIS[semFin.getMonth()].toLowerCase()} ${semFin.getFullYear()} · ${nbJours} jours`
    :(moisEntier
    ? (moisSel.length===1
        ? `${MOIS[mDeb.m]} ${mDeb.y}${iFin===moisList.length-1&&finPer?" (jusqu'à la fin de la période)":" entier"} · ${nbJours} jours`
        : `${MOIS[mDeb.m]} → ${MOIS[mFin.m]} ${mFin.y}${iFin===moisList.length-1&&finPer?" (jusqu'à la fin de la période)":""} · ${nbJours} jours`)
    : `du ${rDf} ${rDeb==="M"?"matin":"après-midi"} au ${rDt} ${rFin==="M"?"matin":"après-midi"} · ${nbJours} jour${nbJours>1?"s":""}`);

  /* les demi-journées d'extrémité : un jour au milieu de la période est toujours entier */
  const lancer=()=>{
    if(!ok)return;
    const p={medId,dateFrom:rDf,dateTo:rDt,slotDebut:rDeb,slotFin:rFin,slots:["M","AM"]};
    if(action==="poser"){onPose({...p,absType});return;}
    if(cible==="abs"){onRetraitAbs({...p,absType});return;}
    if(cible==="tout"){onEffacer({...p,keepAbs:false,keepGardes:degre!=="absolu"});return;}
    onEffacer({...p,keepAbs,keepGardes:true});
  };

  const segBtn=(on,rouge)=>({flex:1,padding:"7px 5px",borderRadius:7,cursor:"pointer",fontWeight:800,fontSize:12,
    border:"1.5px solid "+(on?(rouge?"#dc2626":"#1d4ed8"):"var(--border)"),
    background:on?(rouge?"#fee2e2":"#eff6ff"):"var(--bg2)",color:on?(rouge?"#991b1b":"#1e40af"):"var(--txt2)"});
  const miniBtn=on=>({padding:"4px 10px",borderRadius:6,cursor:"pointer",fontWeight:800,fontSize:11,
    border:"1.5px solid "+(on?"#1d4ed8":"var(--border)"),background:on?"#eff6ff":"var(--bg2)",color:on?"#1e40af":"var(--txt3)"});

  /* v9.94 : la confirmation annonce le nombre RÉEL d'activités qui vont disparaître.
     « tout le reste sur la période » ne permettait pas de juger : effacer 3 activités et
     en effacer 120 ne se décident pas de la même façon. */
  /* v10.11 : le décompte ne se faisait que pour « Les activités » — avec « Tout » il
     restait à zéro alors que le retrait, lui, fonctionnait. On compte désormais aussi
     pour « Tout », en lui passant les mêmes règles que celles qui seront appliquées. */
  const rEff=(compter&&(confirm==="activites"||confirm==="tout"))
    ? compter({medId,dateFrom:rDf,dateTo:rDt,
        keepAbs:confirm==="tout"?false:keepAbs,
        keepGardes:confirm==="tout"?(degre!=="absolu"):true,
        slotDebut:rDeb,slotFin:rFin})
    : {n:0,det:[]};
  const nEff=rEff.n;
  if(confirm) return(
    <div style={{minWidth:320,maxWidth:400}}>
      <div style={S.mHd}><div style={{...S.mTit2,color:"#991b1b"}}>⚠ Confirmer</div></div>
      <div style={{fontSize:12.5,lineHeight:1.6,color:"var(--txt)"}}>
        Vous allez <b>{libAction.toLowerCase()}</b> pour <b>{med?med.prenom+" "+med.nom:"—"}</b><br/>
        sur <b>{libPeriode}</b>.
        {(confirm==="activites"||confirm==="tout")&&<>
          <div style={{marginTop:9,color:"#16a34a",fontWeight:700}}>✓ Conservés : {confirm==="tout"?(degre==="absolu"?"rien":"gardes, repos et tour"):(keepAbs?"absences, FMC, gardes, repos, tour":"gardes, repos, tour")}</div>
          <div style={{color:"#991b1b",fontWeight:700}}>✗ Effacé : {nEff===0?"aucune activité — rien à retirer":nEff+" activité"+(nEff>1?"s":"")+" posée"+(nEff>1?"s":"")}</div>
          {nEff>0&&<div style={{marginTop:5,display:"flex",flexWrap:"wrap",gap:4}}>
            {rEff.det.map(x=>(
              <span key={x.lab} style={{fontSize:10,fontWeight:800,padding:"2px 7px",borderRadius:11,
                background:"rgba(220,38,38,.10)",border:"1px solid #fca5a5",color:"#991b1b"}}>{x.n} × {x.lab}</span>
            ))}
          </div>}
        </>}
      </div>
      <div style={{display:"flex",gap:6,marginTop:13}}>
        <button style={segBtn(false)} onClick={()=>setConfirm(null)}>Annuler</button>
        <button style={segBtn(true,true)} onClick={()=>{setConfirm(null);lancer();}}>Oui, {action==="poser"?"poser":"retirer"}</button>
      </div>
    </div>
  );

  return(
    <div style={{minWidth:320,maxWidth:400}}>
      <div style={S.mHd}>
        <div style={S.mTit2}>📅 Sur une période{med?" — "+med.prenom+" "+med.nom:""}</div>
        <button onClick={onClose} style={S.xBtn}>×</button>
      </div>

      {!initMedId&&<div style={{marginBottom:10}}>
        <label style={S.fl}>Médecin</label>
        <select value={medId||""} onChange={e=>setMedId(parseInt(e.target.value))} style={{...S.fi,width:"100%"}}>
          <option value="">— Choisir —</option>
          {medecins.filter(m=>m.role==="medecin"||m.role==="attache").map(m=>(
            <option key={m.id} value={m.id}>{m.prenom} {m.nom}</option>))}
        </select>
      </div>}

      <label style={S.fl}>Action</label>
      <div style={{display:"flex",gap:5}}>
        <button style={segBtn(action==="poser")} onClick={()=>setAction("poser")}>＋ Poser</button>
        <button style={segBtn(action==="retirer",true)} onClick={()=>setAction("retirer")}>－ Retirer</button>
      </div>

      {action==="poser"&&<>
        <label style={{...S.fl,marginTop:10,display:"block"}}>Quoi</label>
        <div style={{display:"flex",gap:5}}>
          <button style={segBtn(absType==="ABSENCE")} onClick={()=>setAbsType("ABSENCE")}>🚫 Absence</button>
          <button style={segBtn(absType==="FORMATION")} onClick={()=>setAbsType("FORMATION")}>🎓 Formation</button>
        </div>
      </>}

      {action==="retirer"&&<div style={{marginTop:10,padding:9,borderRadius:8,border:"1.5px dashed #f59e0b",background:"rgba(245,158,11,.07)"}}>
        <div style={{fontSize:9.5,fontWeight:800,color:"#b45309",textTransform:"uppercase",letterSpacing:".04em",marginBottom:6}}>Retirer quoi ?</div>
        <div style={{display:"flex",gap:5}}>
          <button style={segBtn(cible==="abs",true)} onClick={()=>setCible("abs")}>Absence / FMC</button>
          {/* v9.93 : le rôle administratif ne retire pas d'activités — même périmètre qu'avant */}
          {allowActs&&<button style={segBtn(cible==="activites",true)} onClick={()=>setCible("activites")}>Les activités</button>}
          {/* v10.10 : « Tout » évite deux passages sur la même période pour vider une ligne */}
          {allowActs&&<button style={segBtn(cible==="tout",true)} onClick={()=>setCible("tout")}>Tout</button>}
        </div>
        {cible==="tout"&&<div style={{display:"flex",flexDirection:"column",gap:4,marginTop:8}}>
          {[["garde","Tout sauf gardes et tour","absences, FMC et activités"],
            ["absolu","Absolument tout","+ gardes, repos et semaines de tour"]].map(([v,t,d])=>(
            <button key={v} onClick={()=>setDegre(v)}
              style={{textAlign:"left",padding:"7px 10px",borderRadius:7,cursor:"pointer",fontWeight:800,fontSize:12,
                border:"1.5px solid "+(degre===v?"#dc2626":"var(--border)"),
                background:degre===v?"#fee2e2":"var(--bg2)",color:degre===v?"#991b1b":"var(--txt2)"}}>
              {t}<span style={{display:"block",fontSize:10,fontWeight:600,opacity:.85,marginTop:2}}>{d}</span>
            </button>))}
        </div>}
      </div>}

      <label style={{...S.fl,marginTop:10,display:"block"}}>Quelle période</label>
      <div style={{display:"flex",gap:5}}>
        <button style={segBtn(mode==="dates")} onClick={()=>setMode("dates")}>Deux dates</button>
        <button style={segBtn(mode==="semaine")} onClick={()=>setMode("semaine")}>🗓 La semaine</button>
        <button style={segBtn(mode==="mois")} onClick={()=>setMode("mois")}>📆 Le mois</button>
      </div>

      {mode==="dates"?<>
        <label style={{...S.fl,marginTop:10,display:"block"}}>Début</label>
        <input type="date" value={df} onChange={e=>{setDf(e.target.value);if(!dt||e.target.value>dt)setDt(e.target.value);}} style={{...S.fi,width:"100%"}}/>
        <div style={{display:"flex",gap:4,marginTop:5}}>
          <button style={miniBtn(slDeb==="M")} onClick={()=>setSlDeb("M")}>Matin</button>
          <button style={miniBtn(slDeb==="AM")} onClick={()=>setSlDeb("AM")}>Après-midi</button>
        </div>
        <label style={{...S.fl,marginTop:10,display:"block"}}>Fin</label>
        <input type="date" value={dt} onChange={e=>setDt(e.target.value)} style={{...S.fi,width:"100%"}}/>
        <div style={{display:"flex",gap:4,marginTop:5}}>
          <button style={miniBtn(slFin==="M")} onClick={()=>setSlFin("M")}>Matin</button>
          <button style={miniBtn(slFin==="AM")} onClick={()=>setSlFin("AM")}>Après-midi</button>
        </div>
      </>:semEntier?<>
        <div style={{marginTop:9,padding:"9px 11px",borderRadius:8,border:"1px solid var(--border)",background:"var(--bg2)",textAlign:"center"}}>
          <div style={{fontSize:12.5,fontWeight:800,color:"var(--txt)"}}>
            Semaine du {JOURSL[semDeb.getDay()].toLowerCase()} {semDeb.getDate()} au {JOURSL[semFin.getDay()].toLowerCase()} {semFin.getDate()} {MOIS[semFin.getMonth()].toLowerCase()}
          </div>
          <div style={{fontSize:10.5,fontWeight:600,color:"var(--txt3)",marginTop:2}}>
            {nbJours} jours{semAbs?" — week-ends et fériés accolés inclus":""} — contient le {JOURSL[semBase.getDay()].toLowerCase()} {semBase.getDate()}
          </div>
        </div>
      </>:<>
        <label style={{...S.fl,marginTop:10,display:"block"}}>Quels mois (plusieurs possibles)</label>
        <div style={{display:"flex",gap:4,flexWrap:"wrap"}}>
          {moisList.map((x,i)=>(
            <button key={x.y+"-"+x.m} onClick={()=>togMois(i)}
              style={{flex:"1 1 auto",minWidth:78,padding:"7px 6px",borderRadius:7,cursor:"pointer",fontWeight:800,fontSize:11.5,
                border:"1.5px solid "+(moisSel.includes(i)?"#1d4ed8":"var(--border)"),
                background:moisSel.includes(i)?"#eff6ff":"var(--bg2)",color:moisSel.includes(i)?"#1e40af":"var(--txt2)"}}>
              {moisSel.includes(i)?"✓ ":""}{MOIS[x.m].slice(0,4)} {String(x.y).slice(2)}
            </button>))}
        </div>
      </>}

      {action==="retirer"&&cible==="activites"&&
        <label style={{display:"flex",gap:7,alignItems:"center",fontSize:11.5,color:"var(--txt)",marginTop:9,
          background:"var(--bg2)",border:"1px solid var(--border)",borderRadius:7,padding:"7px 9px",cursor:"pointer"}}>
          <input type="checkbox" checked={keepAbs} onChange={e=>setKeepAbs(e.target.checked)} style={{width:14,height:14}}/>
          Conserver absences, FMC, gardes, repos et tour
        </label>}

      <div style={{marginTop:10,padding:"8px 10px",borderRadius:8,fontSize:11.5,fontWeight:700,
        background:action==="poser"?"rgba(63,185,80,.12)":"rgba(220,38,38,.10)",
        border:"1px solid "+(action==="poser"?"#86efac":"#fca5a5"),
        color:action==="poser"?"#166534":"#991b1b"}}>
        {libAction} — {libPeriode}
      </div>

      <button disabled={!ok} onClick={()=>{ if(!ok)return; if(action==="retirer")setConfirm(cible); else lancer(); }}
        style={{...S.btnP,width:"100%",marginTop:11,opacity:ok?1:.5,
          background:action==="poser"?"#1d4ed8":"#dc2626"}}>
        {action==="poser"?"Poser":"Retirer…"}
      </button>
    </div>
  );
}

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
function TourTab({noNav=false,specColors=null,tourMins,tourMinsHard,tourAvoid,tourWish,applyTPForWeek,cleanTPForWeek,clearWeekActivities,reapplyPTWeek,purgeTourExtras,plan,tourDerog,lastReport,setLastReport,tourCfg,setTourCfg,year:tourYear,month:tourMonth,setYear:setTourYear,setMonth:setTourMonth,tourMed,setTourMed,medecins,getEntries,isEdit,darkMode,setDarkMode,planningType,setPlan,allDays,toast}){
  const _psT=perStart(tourYear,tourMonth);
  const perT={pi:_psT.sm,startY:_psT.sy,startM:_psT.sm};
  const perKeyT=perT.startY+"_"+perT.startM;
  const savedCfg=(tourCfg||{})[perKeyT]||null;
  const perLabelT=MOIS[perT.startM]+" — "+MOIS[(perT.startM+PCFG.len-1)%12];
  const prevPeriodT=()=>{const p=perPrev(perT.startY,perT.startM);setTourMonth(p.sm);setTourYear(p.sy);};
  const nextPeriodT=()=>{const p=perNext(perT.startY,perT.startM);setTourMonth(p.sm);setTourYear(p.sy);};
  /* v10.109 : les semaines viennent des BORNES REELLES de la periode. Avant, elles
     partaient du 1er lundi >= 1er du mois et s'arretaient au dernier jour du dernier
     mois — juste tant qu'aucune extension ne deplacait une borne. */
  const weeksT=perWeeksList(perT.startY,perT.startM);
  const tmCountPeriod=(medId)=>weeksT.reduce((n,w)=>{const wm2=tourMed[w.key]||{HC:[],USIC:[]};return((wm2.HC||[]).includes(medId)||(wm2.USIC||[]).includes(medId))?n+1:n;},0);
  const isBlockedInWeek=(medId,wk2)=>{
    const[wy2,wm2,wd2]=wk2.split("-").map(Number);
    const _mo=medecins.find(m=>String(m.id)===String(medId));   /* v10.41 */
    for(let i=0;i<5;i++){
      const dt=new Date(wy2,wm2,wd2+i);
      const dy=dt.getFullYear(),dm=dt.getMonth(),dd=dt.getDate();
      if(_mo&&offOn(_mo,dy,dm,dd))return true;   /* désactivé ce jour-là → semaine bloquée */
      const es1=getEntries(medId,dy,dm,dd,"M");
      const es2=getEntries(medId,dy,dm,dd,"AM");
      if([...es1,...es2].some(e=>ABS_IDS.includes(e.acteId)))return true;
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
      if(es.some(e=>ABS_IDS.includes(e.acteId)))days.push(JOURS_SW[dt.getDay()]+" "+dd);
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
      const PROT=PROT_TOUR;
      setPlan(p=>{
        let next={...p};
        // Chaque personne : retirer ses activités sur sa semaine d'ARRIVÉE, ré-appliquer son PT sur sa semaine de DÉPART
        [[swapSrcMed,swapDstKey,swapSrcKey],[swapDstMed,swapSrcKey,swapDstKey]].forEach(([mid,arriveKey,leaveKey])=>{
          weekDays(arriveKey).forEach(([dy,dm,dd])=>{
            if(isWE(dy,dm,dd))return;
            ["M","AM"].forEach(sl=>{
              const k=sk(dy,dm,dd,sl);
              if(!next[k]||!next[k][mid])return;
              /* v9.88 : lecture de TOUTE la case, et retrait ciblé (même règle que v9.73) */
              if(cellHasAny(next[k][mid],PROT))return;
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
              if(cellHasAny(ex,PROT))return;
              const[acteId,salle,a2x=null,s2x=null,a3x=null,s3x=null,c1x=null]=(pt[dw2][sl])||[null,null];
              if(!acteId)return;
              if(!next[k])next[k]={};
              next[k]={...next[k],[mid]:ptCell(acteId,salle,a2x,s2x,a3x,s3x,c1x)};
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
        if(cellHasAny(dm2[mid],["TOUR_USIC"])){
          const jr=medecins.find(m2=>String(m2.id)===String(mid));
          const tp=derogMeds.length>0?medecins.find(m2=>String(m2.id)===String(derogMeds[0])):null;
          infos.push((jr?jr.init:"?")+" remplace "+(tp?tp.init:"?")+" ("+JOURS_TP[dt.getDay()]+" "+dd+" "+MOIS[dm3].slice(0,4)+(MOIS[dm3].length>4?".":"")+")");
        }
      });
    }
    return infos;
  };
  /* v10.95 : liste de la PÉRIODE de cet écran (celle de Construire quand la
     tuile l'embarque) — les indisponibles sur toute la période en sortent et
     un rôle junior porte les initiales de ses deux titulaires. */
  const medsPerT=djListePeriode(medecins,perDaysList(perT.startY,perT.startM));
  const tourMeds=medsPerT.filter(m=>m.tourMed);
  const horsTourSpecMeds=medsPerT.filter(m=>m.role==="medecin"&&!m.tourMed&&m.surSpec);
  /* v9.84 : couleurs des surspécialités réglables. Elles étaient écrites en dur ici —
     une information dans le code que l'utilisateur ne pouvait pas atteindre. Elles
     viennent maintenant des paramètres, avec repli sur les valeurs historiques. */
  const SPEC_COLORS={...SPEC_COLORS_DEF,...(specColors||{})};
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
      <div style={noNav?{display:"none"}:S.bar}>
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
      <div style={{display:"flex",gap:6,overflowX:"auto",marginBottom:14,paddingBottom:4,position:"sticky",top:noNav?(HDR_H+BUILD_BAR_H):44,zIndex:noNav?10:30,background:"var(--bg)",paddingTop:4}}>
        {tourMeds.map(m=>{
          const hcCount=weeksT.reduce((n,w)=>{const wm2=tourMed[w.key]||{};return (wm2.HC||[]).includes(m.id)?n+1:n;},0);
          const usicCount=weeksT.reduce((n,w)=>{const wm2=tourMed[w.key]||{};return (wm2.USIC||[]).includes(m.id)?n+1:n;},0);
          const total=hcCount+usicCount;
          const isExcl=savedCfg&&savedCfg.excl&&savedCfg.excl[m.id];
          const nActifs=tourMeds.length||1;
          const quotaN=isExcl?0:(savedCfg&&savedCfg.weeks&&savedCfg.weeks[m.id]!==undefined?savedCfg.weeks[m.id]:Math.ceil((weeksT.length*4)/nActifs));
          const quotaOK=total>=quotaN;
          return(
            <div key={m.id} style={{...S.card,textAlign:"center",minWidth:64,flexShrink:0,padding:"5px 7px",opacity:quotaOK?1:.55,filter:quotaOK?"none":"grayscale(.35)"}} title={total+"/"+quotaN+" semaines"}>
              {/* v10.32 : le total passe A COTE des initiales, le decompte HC/USIC
                  remonte d'autant — une ligne de moins, largeur et corps inchanges. */}
              <div style={{display:"flex",alignItems:"center",justifyContent:"center",gap:5}}>
                <Av med={m}/>
                <div style={{fontWeight:800,fontSize:14,color:m.color,fontFamily:"'JetBrains Mono',monospace"}}>{total}</div>
              </div>
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
                <div style={{display:"grid",gap:4,justifyContent:"start",gridTemplateColumns:"repeat(auto-fill,minmax(62px,76px))"}}>
                  {tourMeds.map(m=>{
                    const on=(wm[unit]||[]).includes(m.id);
                    const blocked=isBlockedInWeek(m.id,w.key);
                    const inOther=(wm[unit==="HC"?"USIC":"HC"]||[]).includes(m.id);
                    const dis=blocked||inOther;
                    const avoidW=!!((tourAvoid||{})[w.key]||{})[m.id];
                    const wishW=!!((tourWish||{})[w.key]||{})[m.id];
                    return(
                      <button key={m.id} disabled={dis||!isEdit}
                        style={{padding:"4px 6px",borderRadius:6,border:"none",cursor:dis||!isEdit?"default":"pointer",textAlign:"center",minWidth:62,overflow:"hidden",
                          background:on?({coro:"rgba(118,165,175,.82)",pace:"rgba(227,179,65,.82)",eep:"rgba(139,92,246,.82)",ett:"rgba(236,72,153,.82)"}[m.surSpec]||"rgba(56,139,253,.82)"):"var(--bg2)",color:on?"#fff":"var(--txt2)",fontWeight:on?800:600,opacity:dis?.3:1,
                           outline:on?"2px solid "+(SPEC_COLORS[m.surSpec]||"#388bfd"):m.surSpec&&!blocked?"2px solid "+(SPEC_COLORS[m.surSpec]||"var(--border)"):"1px solid var(--border)"}}
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
                        <div style={{fontWeight:800,fontSize:11,lineHeight:1.15}} title={avoidW?"Préfère ne pas tourner cette semaine":wishW?"Souhaite tourner cette semaine":""}>{m.init}{avoidW?" 🚫":wishW?" ⭐":""}</div>
                        <div style={{fontSize:8.5,color:blocked?"inherit":m.surSpec&&!on?(SPEC_COLORS[m.surSpec]):"inherit"}}>
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
                    <span style={{width:26,height:26,borderRadius:"50%",background:md.color,color:"#fff",fontSize:10,fontWeight:800,display:"inline-flex",alignItems:"center",justifyContent:"center"}}>{md.init}</span>
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
                    <span style={{width:26,height:26,borderRadius:"50%",background:md.color,color:"#fff",fontSize:10,fontWeight:800,display:"inline-flex",alignItems:"center",justifyContent:"center"}}>{md.init}</span>
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
                          <div style={{width:26,height:26,borderRadius:"50%",background:m.color,display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:10,fontWeight:800}}>{m.init}</div>
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
  const allStatMeds=djListePeriode(medecins,days).filter(m=>m.role==="medecin");
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
      <div style={{...S.bar,position:"sticky",top:HDR_H,zIndex:40,background:"var(--bg)",paddingTop:6,paddingBottom:6}}>
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
      <TableScroll memId="stats" mh={190}>
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
                      <div style={{width:26,height:26,borderRadius:"50%",background:m.color,display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:10,fontWeight:800,flexShrink:0}}>{m.init}</div>
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
      </TableScroll>
    </div>
  );
}

/* ════ AIDE (V9) — composant partagé jsx/html, React.createElement pur ════ */
const HE=React.createElement;
/* Reproductions visuelles des éléments de l'interface */
function HBtn(p){
  const st={green:{border:"1.5px solid #16a34a",background:"rgba(22,163,74,.10)",color:"#16a34a"},
    blue:{border:"none",background:"#1d4ed8",color:"#fff"},
    red:{border:"1px solid #fecdd3",background:"#fff1f2",color:"#dc2626"},
    violet:{border:"1.5px solid #7c3aed",background:"rgba(124,58,237,.10)",color:"#7c3aed"},
    ghost:{border:"1px solid var(--border)",background:"var(--bg2)",color:"var(--txt)"}}[p.kind||"ghost"];
  return HE("span",{style:Object.assign({display:"inline-block",fontSize:11,padding:"2px 9px",borderRadius:6,fontWeight:800,verticalAlign:"middle",whiteSpace:"nowrap"},st)},p.children);
}
function HAvat(p){return HE("span",{style:{display:"inline-flex",width:19,height:19,borderRadius:"50%",background:p.color||"#3b82f6",color:"#fff",fontSize:8,fontWeight:800,alignItems:"center",justifyContent:"center",verticalAlign:"middle"}},p.txt||"AB");}
function HBadg(p){return HE("span",{style:{display:"inline-block",padding:"1px 6px",borderRadius:5,fontSize:9,fontWeight:800,fontFamily:"'JetBrains Mono',monospace",background:p.color,color:p.dark?"#fff":"#111",verticalAlign:"middle"}},p.txt);}
function HChip(p){return HE("span",{style:{display:"inline-block",padding:"1px 7px",borderRadius:9,fontSize:9,fontWeight:800,background:p.bg,color:"#fff",verticalAlign:"middle"}},p.txt);}
function HP(p){return HE("div",{style:{fontSize:12,color:"var(--txt)",lineHeight:1.65,marginBottom:p.last?0:8}},p.children);}
function HT(p){return HE("div",{style:{fontSize:11,fontWeight:800,color:"var(--txt2)",textTransform:"uppercase",letterSpacing:.4,margin:"12px 0 4px"}},p.children);}
function HStep(p){return HE("div",{style:{display:"flex",gap:8,marginBottom:7,alignItems:"flex-start"}},
  HE("span",{style:{flexShrink:0,width:26,height:26,borderRadius:"50%",background:"#1d4ed8",color:"#fff",fontSize:10,fontWeight:800,display:"inline-flex",alignItems:"center",justifyContent:"center"}},p.n),
  HE("div",{style:{fontSize:12,color:"var(--txt)",lineHeight:1.6}},p.children));}
function HTab(p){return HE("div",{style:{marginBottom:7}},
  HE("span",{style:{fontWeight:800,fontSize:12,color:"var(--txt)"}},p.t+" — "),
  HE("span",{style:{fontSize:12,color:"var(--txt2)",lineHeight:1.6}},p.children));}

const HELP_SECTIONS=[
 {id:"consult",icon:"👤",title:"Utiliser le planning sans être éditeur",body:()=>HE("div",null,
  HP({children:["Sur la page d'accueil, deux façons d'entrer :"]}),
  HP({children:[HBtn({kind:"ghost",children:"👁 Consulter"})," — lecture libre de tous les onglets, sans code et sans risque de rien modifier."]}),
  HP({children:["Ou bien votre ",HE("b",null,"PIN personnel")," : tapez-le dans le champ PIN puis ",HBtn({kind:"blue",children:"✏️ Édition"}),". Vous entrez en ",HE("b",null,"édition personnelle"),", signalée par un bandeau bleu en bas d'écran : vous pouvez modifier ",HE("b",null,"uniquement votre ligne"),", tout le reste demeure en lecture seule."]}),
  HT({children:"Ce que votre PIN vous permet"}),
  HP({children:["• ",HE("b",null,"Poser vos absences et formations")," : cliquez sur vos cases dans le Planning, ou utilisez la modale d'absence pour une période (dates de début/fin, matin/après-midi)."]}),
  HP({children:["• ",HE("b",null,"Vos préférences de gardes")," : dans le Planning, cliquez la case du jour, puis ",HBtn({kind:"ghost",children:"⚙️ Préférences tour & garde…"})," — ⭐ je souhaite cette garde, 🚫 je préfère éviter. La répartition automatique en tient compte."]}),
  HP({children:["• ",HE("b",null,"Vos préférences de tour")," : même bouton, dans la même fenêtre — la préférence porte alors sur la ",HE("b",null,"semaine entière")," (⭐ je souhaite tourner, 🚫 pas cette semaine)."]}),
  HP({children:["• ",HE("b",null,"Les revoir, les retirer")," : le bouton ",HBtn({kind:"ghost",children:"⭐"})," de la barre du Planning colore les cases concernées — bande bleue « je souhaite tourner », bande rouge « je préfère éviter », ⭐ ou 🚫 sur les jours de garde — avec sa légende au-dessus du tableau. Dans la fenêtre de la case, la ligne de préférence se clique pour la retirer."]}),
  HP({children:["• ",HE("b",null,"Vos propres activités")," : modifier le contenu de vos cases (activité, salle, note)."]}),
  HP({last:true,children:["Votre PIN vous est remis par un éditeur (il le définit dans Équipe → ",HBtn({kind:"ghost",children:"🔑"}),"). En cas d'oubli, demandez-lui de le consulter ou d'en définir un nouveau."]}))},

 {id:"mobile",icon:"📱",title:"Installer sur votre téléphone",body:()=>HE("div",null,
  HP({children:[HE("b",null,"iPhone / iPad (Safari)")," : ouvrez le planning dans Safari, touchez le bouton Partager (le carré avec une flèche vers le haut), faites défiler et choisissez ",HE("b",null,"« Sur l'écran d'accueil »"),", puis Ajouter. L'icône CardioPlanning apparaît et s'ouvre en plein écran, comme une vraie application."]}),
  HP({children:[HE("b",null,"Android (Chrome)")," : ouvrez le planning dans Chrome, menu ⋮ en haut à droite, puis ",HE("b",null,"« Ajouter à l'écran d'accueil »")," (ou « Installer l'application » si Chrome le propose) et validez."]}),
  HP({last:true,children:["Dans les deux cas, l'icône ouvre toujours la dernière version : c'est le site lui-même, aucune mise à jour manuelle à faire. Astuce : refaites simplement l'ajout si vous changez de téléphone."]}))},

{id:"construire",icon:"🧱",title:"Construire — créer le planning pas à pas",body:()=>HE("div",null,
  HP({children:["L'onglet ",HE("b",null,"Construire")," guide la fabrication d'une période en ",HE("b",null,"7 étapes"),", dans l'ordre réel du travail : congés, tour, gardes, absences de tout le monde, planning type, surspécialités, bip. Chaque étape est une tuile qui s'ouvre et se replie ; la première non terminée est ouverte à l'arrivée."]}),
  HP({children:["La ",HE("b",null,"période se choisit en haut"),", une seule fois, et vaut pour toutes les tuiles — l'onglet s'ouvre sur la ",HE("b",null,"période suivante"),", celle qu'on construit. Les tuiles Tour et Gardes reprennent ces deux écrans en entier : leurs onglets ne sont plus affichés dans la barre, ils vivent désormais ici."]}),
  HP({children:["Une étape mesurable se termine ",HE("b",null,"d'elle-même"),' (pastille « terminé ») ; seule l\'étape 5, planning type, se valide à la main. Rien n\'est bloquant : une étape en retard n\'empêche jamais d\'avancer.']}),
  HT({children:"Les demandes à l'équipe"}),
  HP({children:["Depuis la tuile 1, trois demandes s'ouvrent séparément : ",HE("b",null,"poser ses congés"),", ",HE("b",null,"préférences de tour"),", ",HE("b",null,"préférences de gardes"),". Chaque médecin concerné voit alors un ",HE("b",null,"bandeau dans son Planning"),", quelle que soit la période affichée, avec un bouton pour aller à la bonne période et « ✓ C'est fait » qui coche sa ligne. Les préférences de tour ne partent qu'à ceux qui tournent, celles de gardes à ceux qui en prennent."]}),
  HP({children:["Accès : éditeur et intermédiaires. Le bouton du ",HE("b",null,"Bip de Béthune")," vit dans la tuile 7 (il n'est plus dans l'onglet CHB)."]}),
  HT({children:"Le détail, étape par étape"}),
  HP({children:["L'ordre compte : chaque étape s'appuie sur la précédente. Tout se fait sur la ",HE("b",null,"période affichée")," (généralement 4 mois). La période s'étend jusqu'au ",HE("b",null,"dimanche qui clôt la dernière semaine"),", et rattache le lundi suivant s'il est férié (ex. 1er novembre) : la répartition se fait en semaines complètes, et la période suivante démarre le lendemain."]}),
  HT({children:"🏖 Les vacances scolaires"}),
  HP({children:["Les bornes d'une période dépendent des ",HE("b",null,"vacances scolaires"),", qui se saisissent à la main dans ",HE("b",null,"Paramètres"),", année scolaire par année scolaire (Toussaint, Noël, Hiver, Printemps, Été). Si la fin d'une période tombe ",HE("b",null,"dedans"),", elle est repoussée au dernier jour des vacances — sauf au-delà de 21 jours, pour que l'été n'avale pas deux mois."]}),
  HP({children:["« ",HE("b",null,"Coller un calendrier")," » accepte le texte du calendrier officiel et ",HE("b",null,"propose")," les dates trouvées avant de les enregistrer. Le bouton « + Année » prépare l'année suivante ; les années terminées se replient toutes seules et peuvent être supprimées. Un rappel s'affiche dans le Planning dès que la période affichée n'est pas couverte : ",HE("b",null,"rien n'est bloqué"),", mais les bornes seront fausses tant que les dates manquent."]}),
  HStep({n:"1",children:[HE("b",null,"Vérifier l'Équipe")," — rôles (médecin / attaché / IDE), coche ",HChip({txt:"Garde",bg:"#16a34a"})," (elle pilote qui peut recevoir gardes et repos), coche ",HChip({txt:"TM",bg:"#1d4ed8"})," pour le tour, sur-spécialités, temps partiels, PIN individuels, et l'ordre d'affichage avec ▲▼."]}),
  HStep({n:"2",children:[HE("b",null,"Attribuer le Tour")," — tuile 2 de Construire : répartition automatique ",HBtn({kind:"ghost",children:"⚙️ Répartition auto"})," ou attribution manuelle semaine par semaine. L'algorithme respecte les minimums de sur-spécialités, absences, temps partiels et préférences ⭐/🚫."]}),
  HStep({n:"3",children:[HE("b",null,"Répartir les Gardes")," — tuile 3 de Construire : répartition automatique en respectant absences, semaines de tour, jours autorisés par médecin, volume cible, préférences ⭐/🚫 et écart minimal entre deux gardes. Le ",HBadg({txt:"RG",color:"#ffe599"})," repos post-garde est posé automatiquement le lendemain."]}),
  HStep({n:"4",children:[HE("b",null,"Appliquer le Planning type")," — onglet Type : « Depuis le début de la période » par défaut. Les absences, gardes, repos et tours déjà posés sont préservés."]}),
  HStep({n:"5",children:[HE("b",null,"Poser les Astreintes")," — onglet Astreinte : répartition automatique par semaines complètes (lun→dim), équitable entre les médecins cochés « Astreinte rythmo » ; exceptions possibles jour par jour."]}),
  HStep({n:"6",children:[HE("b",null,"Ajuster")," — cases individuelles, échanges de gardes ⇄, dérogations de tour, notes 📝."]}),
  HP({last:true,children:["En fin de période : archiver la période écoulée (voir la tuile Archiver)."]}))},
 {id:"reportsdoc",icon:"📥",title:"Reports de consultations",body:()=>HE("div",null,
  HP({children:["L'onglet liste ",HE("b",null,"toutes les semaines de la période")," — y compris celles où il n'y a rien à faire — avec des pastilles de filtre, pour ne rien oublier. Un bandeau compte les reports encore à valider."]}),
  HP({children:["Pour chaque consultation perdue (absence, semaine de tour), l'application propose la ",HE("b",null,"semaine blanche libre la plus proche"),", jamais à plus d'",HE("b",null,"un mois"),", en avant comme en arrière, dans la période affichée. Une semaine sans solution se traite à la main : « ⇄ Chercher une autre semaine blanche » ouvre le choix complet, sans plafond. La ligne d'une blanche qui reçoit dit « peut accueillir le report de … » et se met à jour toute seule si vous décidez autrement."]}),
  HT({children:"Valider, annuler — tout laisse une trace"}),
  HP({children:["« ✓ valider » écrit un ",HE("b",null,"commentaire estampillé")," dans la case du planning (« 12/08 · TH — Report du 3 août M, trois patients ») ; « annuler le report » n'efface rien : une ligne s'ajoute au commentaire. Les demi-journées blanches restées libres portent la pastille ☐ ",HE("b",null,"à rouvrir"),", qui devient « rouvert par … » une fois cochée — pour ne pas oublier de rendre le créneau aux secrétaires."]}),
  HT({children:"Les demi-journées off"}),
  HP({children:["Le tableau des ",HE("b",null,"off")," liste vos demi-journées habituellement libres, matin et après-midi séparément. Chaque pastille a trois états : ",HE("b",null,"vide")," = pas de off · ",HE("b",null,"verte")," = off, et au moins une salle est disponible ce créneau (cliquez pour l'ouvrir) · ",HE("b",null,"hachurée grise")," = off, mais aucune salle libre. Les salles concernées sont celles cochées « Ouvrable sur un off » dans leur fiche ; sans réglage, ce sont les salles de consultation des deux sites."]}),
  HT({children:"Le décompte des patients"}),
  HP({children:["La case patients ",HE("b",null,"vide"),", c'est toute la consultation qui part d'un bloc ; un ",HE("b",null,"nombre"),", c'est vous qui divisez. Les ",HE("b",null,"après-midis des semaines de tour")," peuvent reprendre une partie des patients — jamais le matin — et la part posée crée alors réellement la consultation dans le planning, avec choix de salle. Le reste peut partir « ↪ en liste d'attente », gérée par les secrétaires. Un badge « ⚠ report incomplet » reste affiché tant que le compte n'est pas à zéro."]}),
  HP({last:true,children:["En bas, « ",HE("b",null,"Demi-journées off par semaine")," » montre les créneaux libres hors semaines de tour : de quoi ouvrir une consultation, une fois tous les reports traités (export CSV). Les flèches ↶↷ couvrent aussi les reports, y compris pour les administratifs."]}))},
 {id:"onglets",icon:"📑",title:"Les onglets un par un",body:()=>HE("div",null,
  HTab({t:"📅 Planning",children:["vue d'ensemble de tous les médecins. Colonne Garde à gauche, fond vert clair = semaine d'astreinte du médecin, fond jaune pâle = week-end. Filtre par médecins possible."]}),
  HTab({t:"🧱 Construire",children:["la fabrication du planning en 7 étapes guidées, avec les demandes à l\'équipe (congés, préférences) et le bouton du Bip. Les anciens onglets Tour et Gardes vivent ici, entiers, dans les tuiles 2 et 3."]}),
  HTab({t:"🏥 CHL / CHB",children:["plannings par site : qui fait quoi dans quelle salle, jour par jour. Le bouton ↔ règle l'",HE("b",null,"ordre des colonnes"),", de gauche à droite, site par site (↩ Ordre par défaut pour revenir en arrière)."]}),
  HTab({t:"❤️ PT Cardio / 🔬 PT Angio",children:["les plateaux techniques, avec occupation des salles et activités de reprise."]}),
  HTab({t:"🎓 Internes",children:["le planning des internes, par semestre de 6 mois : demi-journées, colonne de garde, jauge et statistiques. Onglet facultatif, activé dans Paramètres."]}),
  HTab({t:"📞 Astreinte",children:["semaines d'astreinte rythmo, répartition automatique, exceptions jour par jour (contour violet), export CSV."]}),
  HTab({t:"📋 Type",children:["le planning type hebdomadaire (le « moule ») et son application sur la période."]}),
  HTab({t:"👔 Attachés",children:["planning des attachés et IDE — sans colonne de garde."]}),
  HTab({t:"⚙️ Activités",children:["le catalogue : couleur, abréviation, salles, médecins autorisés. Les activités Garde et Repos post-garde sont synchronisées avec la coche Garde de l'Équipe (note verte)."]}),
  HTab({t:"👥 Équipe",children:["les fiches : rôle, coches Garde/TM/Astreinte, sur-spécialités, activités autorisées (dans la fiche ✏️, groupées Général / CHL / CHB), PIN 🔑, ordre d'affichage ▲▼, temps partiel."]}),
  HTab({t:"⚙️ Paramètres",children:["registre des salles, PIN éditeur, archives, sauvegardes automatiques, export, jauge de taille Firebase. Les encarts arrivent repliés : cliquez un titre pour l\'ouvrir, « Tout déplier » en haut."]}),
  HTab({t:"📊 Stats",children:["compteurs d'activités par médecin sur la période, tri par colonne, export CSV."]}),
  HTab({t:"📥 Reports",children:["outil individuel et facultatif : cochez vos semaines blanches, puis un tableau chronologique signale les semaines de tour reportées sur vos blanches (dates habituelles), celles sans report possible, celles déjà blanches, et les dates fermées à réouvrir ; suivi des offs par semaine. Les activités concernées se cochent « 📥 à reporter » dans l'onglet Activités. Export CSV."]}))},

 {id:"edition",icon:"🔒",title:"Modes d'accès et PIN",body:()=>HE("div",null,
  HP({children:["Trois niveaux d'accès depuis la page d'accueil :"]}),
  HP({children:["• ",HBtn({kind:"ghost",children:"👁 Consulter"})," — lecture seule, sans code."]}),
  HP({children:["• ",HE("b",null,"PIN médecin")," — édition personnelle : uniquement sa propre ligne (voir la première tuile). Défini par un éditeur dans Équipe → ",HBtn({kind:"ghost",children:"🔑"}),"."]}),
  HP({children:["• ",HE("b",null,"PIN administratif")," — pour les secrétaires et cadres : un code partagé (défini dans Paramètres) ; chacun saisit son prénom à la connexion. Chaque activité porte deux coches : « ✏️ secrétaires » et « ✏️ cadres » — le rôle ne peut poser, modifier ou retirer que les activités cochées pour lui (sur la ligne de n'importe quel médecin), et remplir les semaines blanches de l'onglet Reports. Le PIN cadre, distinct, ouvre en plus le planning IDE. Gardes, tours, astreintes et réglages restent hors de portée."]}),
  HP({children:["• ",HE("b",null,"PIN éditeur")," — édition complète de tout le planning. Défini dans Paramètres."]}),
  HP({children:["🔐 ",HE("b",null,"Niveaux de droits")," : chaque médecin a un niveau dans sa fiche ✏️ (onglet Équipe), qui s'applique quand il se connecte avec son PIN personnel. ",HE("b",null,"Basique")," = sa propre ligne, plus ses activités dans CHL, CHB et les plateaux. ",HE("b",null,"Intermédiaire")," = le planning de tous les médecins, gardes et échanges, semaines de tour, planning type et attachés — sans Paramètres, Équipe ni Activités. ",HE("b",null,"Éditeur")," = accès complet. Récapitulatif dans Paramètres."]}),
  HP({children:["📴 ",HE("b",null,"Hors ligne")," : sans réseau, l'application s'ouvre quand même et affiche le dernier planning reçu sur cet appareil, en lecture seule (bandeau gris, pastille grise). Dès le retour du réseau, tout se remet à jour et l'édition se rouvre automatiquement — rien à faire. La première ouverture doit se faire avec du réseau ; sur iPhone, ajoutez l'icône à l'écran d'accueil pour que la mise en cache soit conservée."]}),
  HP({children:["🕘 ",HE("b",null,"Historique d'une case")," : en mode édition, appui long (téléphone) ou clic droit (ordinateur) sur une case du Planning — affiche qui a posé ou retiré quoi, et quand (signé du prénom pour le rôle administratif). Seules les modifications manuelles de cases sont journalisées, pas le planning type ni les répartitions automatiques."]}),
  HP({last:true,children:["Les boutons d'édition (répartitions automatiques, ",HBtn({kind:"green",children:"+ Ajouter"}),", 🗑️, ▲▼…) n'apparaissent qu'en édition complète."]}))},

 {id:"cellules",icon:"🔲",title:"Les cellules du planning",body:()=>HE("div",null,
  HP({children:["Chaque jour de semaine a deux créneaux (M matin, AM après-midi) plus la nuit N pour la garde ; le week-end une seule case JOUR. Cliquez sur une case (en mode édition) pour ouvrir la modale :"]}),
  HP({children:["• choisir l'",HE("b",null,"activité")," (seules celles autorisées pour ce médecin apparaissent), la ",HE("b",null,"salle")," si l'activité en demande une, ajouter une ",HE("b",null,"note")," 📝."]}),
  HP({children:["• ",HE("b",null,"retirer")," : rouvrir la case et choisir Retirer."]}),
  HP({children:["Repères visuels : cases grisées = bloquées par une semaine de tour · fond jaune pâle = week-end · fond et contour verts = semaine d'astreinte · ",HBadg({txt:"G",color:"#93c47d"})," garde · ",HBadg({txt:"RG",color:"#ffe599"})," repos post-garde · cases ",HE("b",null,"hachurées")," = personne indisponible (section ⏸)."]}),
  HP({children:["Les activités cochées « reprise » affichent le nom du médecin seul dans les onglets concernés."]}),
  HT({children:"📝 Les notes"}),
  HP({children:["Une note s'écrit depuis la modale de case, et aussi depuis les fenêtres des onglets ",HE("b",null,"CHL, CHB, PT Cardio et PT Angio"),", où chaque occupant a son propre champ. Elle est donc toujours ",HE("b",null,"rattachée à un médecin"),", ce qui compte quand deux personnes se succèdent dans la même salle : au survol de la case, les notes s'affichent préfixées des initiales (« ND : 4 cs · TH : 3 cs »). Un point orange sur la vignette signale qui en porte une."]}),
  HT({children:"◇ Le choix ouvert"}),
  HP({children:["Un ",HE("b",null,"choix ouvert")," est une activité (une, deux ou trois) posée sans être tranchée : « ce sera l'une de celles-là ». Il se crée dans le ",HE("b",null,"planning type")," (fenêtre d'une case → « ◇ Transformer en choix ouvert »), et se reconnaît dans les grilles à son ",HE("b",null,"cadre pointillé violet"),"."]}),
  HP({children:["Tant qu'il n'est pas tranché, le médecin reste ",HE("b",null,"disponible")," pour ces activités : il n'occupe aucune salle, ne consomme aucune IDE, et reste proposé dans les fenêtres — c'est tout l'intérêt, notamment pour le bip. Un compteur violet à part, en haut du Planning, dit combien il en reste à trancher."]}),
  HP({children:["Trancher, c'est ",HE("b",null,"poser quelque chose de ferme")," : attribuer une salle depuis un onglet de salle, ou cliquer « ✓ c'est celle-ci » dans la modale de case (pour les activités sans salle). Les autres branches disparaissent alors — mais elles sont gardées en mémoire : la modale propose ",HE("b",null,"↩ rétablir"),", et retirer l'activité rétablit le choix tout seul. Une croix par branche permet aussi d'en supprimer une, ou tout le choix."]}),
  HT({children:"📅 Modifier sur une période"}),
  HP({children:["Depuis la modale d'une case, ",HBtn({kind:"ghost",children:"📅 Modifier sur une période…"})," évite de cliquer case par case. On choisit des dates (ou « la semaine », « le mois entier », qui affichent les dates réelles), puis ce qu'on fait : poser ou retirer une ",HE("b",null,"absence / FMC"),", retirer ",HE("b",null,"les activités"),", ou ",HE("b",null,"tout"),". Pour une absence ou une FMC, « la semaine » embarque aussi le ",HE("b",null,"week-end précédent, le week-end suivant et les fériés accolés")," — une semaine de vacances va du samedi au dimanche d'après (l'encart affiche les dates exactes)."]}),
  HP({last:true,children:["Pour « tout », deux degrés : « Tout sauf gardes et tour » ou « Absolument tout » — chacun retire un peu plus que le précédent. Une garde et son repos partent ",HE("b",null,"toujours ensemble"),". Avant de valider, la confirmation annonce le ",HE("b",null,"nombre réel")," de demi-journées concernées et le détail par activité : effacer 3 activités ou 120 ne se décide pas de la même façon. Chacun peut le faire sur sa propre ligne, dans les mêmes limites que case par case."]}))},

 {id:"periodes",icon:"📆",title:"Les périodes de l'application",body:()=>HE("div",null,
  HP({children:["L'application manipule plusieurs découpages du temps. Les voici, pour s'y retrouver."]}),
  HP({children:[HE("b",null,"La période (4 mois)")," : l'unité centrale — la navigation ‹ ›, le verrou, l'archivage, Construire, le planning type, les stats et l'export travaillent par période. Ses bornes sont RÉELLES : elle commence le lendemain de la fin de la précédente et se termine au dimanche qui clôt la dernière semaine de son dernier mois ; le lundi suivant lui est rattaché s'il est férié (1er novembre) ; et sa fin s'étend jusqu'au dernier jour des vacances scolaires quand elle tombe dedans (21 jours au plus — l'été n'est jamais absorbé). Une période ne va donc jamais « du 1er au 31 ». Longueur et mois de départ se règlent dans Paramètres."]}),
  HP({children:[HE("b",null,"Les semaines")," (tour et planning type) : toujours entières, du lundi au dimanche. Les semaines d'une période vont du lundi qui précède ou égale son premier jour au dimanche qui précède ou égale son dernier jour — autrement dit, une semaine appartient à la période de son dimanche. Quand un lundi férié est rattaché à la période précédente, la semaine de ce lundi ouvre la période suivante : le tour s'y répartit à partir du mardi."]}),
  HP({children:[HE("b",null,"Les semestres")," (internes et Dr Juniors) : six mois, bascules début mai et début novembre, reportées au lundi. Ils sont indépendants des périodes — seule la période de mars à juin contient une bascule en son milieu (début mai) ; celle de novembre tombe sur une frontière de période."]}),
  HP({children:[HE("b",null,"L'année scolaire des vacances")," (Toussaint → Été), saisie dans Paramètres : elle sert au calcul de la fin de période et au fond coloré des jours de vacances."]}),
  HP({last:true,children:[HE("b",null,"En cours, close, archivée")," : la période en cours est celle qui contient aujourd'hui ; tout ce qui la précède est clos (lecture seule, badge 🔒) ; une période close peut être archivée (badge 🗄) — voir la section « Archiver, sauvegarder, exporter »."]}))},

{id:"archives",icon:"🗄️",title:"Archiver, sauvegarder, exporter",body:()=>HE("div",null,
  HP({children:[HE("b",null,"Les périodes closes")," : tout ce qui précède le premier jour de la période en cours est en LECTURE SEULE, pour tout le monde, éditeur compris — « 🔒 Période close » s'affiche sous le titre en haut à gauche et les modifications y sont refusées. Pour une correction exceptionnelle, l'éditeur peut lever le verrou dans Paramètres, encart 🔓 Périodes closes : il ne vaut que pour cette session et se remet en place au rechargement suivant."]}),
  HP({children:[HE("b",null,"Archiver une période")," (Paramètres → Archives) : chaque période close a son bouton 🗄 Archiver — et « Tout archiver » quand il y en a plusieurs. L'archivage copie dans Firebase les cases de la période et ses données datées (tour, notes, souhaits, reports, Construire), télécharge un fichier .json sur l'appareil (à conserver : c'est la copie hors Firebase), puis les retire des données actives — la base reste légère. En naviguant vers une période archivée, ses cases, son tour et ses notes se rechargent automatiquement en consultation, et « 🗄 Période archivée » remplace le badge de verrou. Chaque période archivée a sa pastille dans Paramètres : ↩ la désarchive et rend tout. Une période corrigée après déverrouillage peut être archivée une seconde fois — l'archive fusionne. Seule l'astreinte reste volontairement dans les données actives (poids négligeable)."]}),
  HP({children:[HE("b",null,"Sauvegardes automatiques")," : une photographie complète une fois par jour, les 45 dernières conservées, avec aperçu avant restauration."]}),
  HP({children:[HE("b",null,"Restaurer un seul médecin, sur quelques jours")," : depuis la modale d'une case, ",HBtn({kind:"ghost",children:"↩ Restaurer depuis une sauvegarde…"})," (éditeur seulement). On choisit la sauvegarde, puis les dates, et l'application affiche d'abord un ",HE("b",null,"bilan")," — remises, supprimées, inchangées, avec le détail par activité — avant toute écriture. Seules les cases de ce médecin sur ces dates sont touchées : le travail des autres depuis la sauvegarde est préservé, ce qu'une restauration complète écraserait."]}),
  HP({children:[HE("b",null,"Exports")," : JSON complet (Paramètres), CSV des gardes, des astreintes et des stats depuis leurs onglets."]}),
  HP({children:["La jauge dans Paramètres indique la taille des données Firebase — archivez les périodes passées si elle monte."]}),
  HT({children:"💻 Copie sur mon ordinateur"}),
  HP({children:["Dans Paramètres, encart 💾 Sauvegarde & archivage, le bloc ",HE("b",null,"Copie sur mon ordinateur")," produit deux fichiers indépendants de l'application : le ",HE("b",null,"tableau (.xls)"),", limité à la période choisie, à ouvrir dans Excel ou Google Sheets pour rediffuser le planning (week-ends et fériés en jaune, notes ✎ dans les cases), et les ",HE("b",null,"données brutes (.json)"),", qui contiennent l'intégralité des données (toutes périodes) et permettent de tout remettre en place via l'encart 📂 Importer, juste en dessous. Source au choix : le planning actuel ou l'une des sauvegardes automatiques. Aucune connexion nécessaire — cela fonctionne même quand la synchronisation est en panne, c'est fait pour ça."]}),
  HP({last:true,children:["Un ",HE("b",null,"rappel")," s'affiche dans le Planning de l'éditeur au bout de 7 jours ou de 200 cases modifiées depuis la dernière sauvegarde (seuil réglable dans l'encart). La date de dernière sauvegarde et le compteur sont propres à ",HE("b",null,"chaque ordinateur"),"."]}))},

 {id:"desactiver",icon:"⏸",title:"Indisponible : les hachures et la désactivation",body:()=>HE("div",null,
  HP({children:["Une case ",HE("b",null,"hachurée")," veut toujours dire la même chose, quel que soit l'onglet : ",HE("b",null,"cette personne n'est pas disponible ce jour-là"),". Ce n'est pas un effet d'affichage mais un ",HE("b",null,"verrou")," : la case ne s'ouvre pas au clic, le planning type ne s'y applique pas, et les répartitions automatiques passent la personne. Couverte sur ",HE("b",null,"toute")," la période affichée, sa colonne disparaît même des grilles."]}),
  HP({children:["Deux situations produisent une hachure : une ",HE("b",null,"désactivation posée à la main")," (ci-dessous), et un ",HE("b",null,"rôle de Dr Junior dont le nom du semestre n'a pas encore été saisi")," (section suivante). Dans les deux cas, le contenu déjà posé n'est pas effacé : il reste sous les hachures."]}),
  HT({children:"Désactiver quelqu'un"}),
  HP({children:["Pour un long congé, un départ, une période sans remplaçant : plutôt qu'une ligne remplie d'absences, on ",HE("b",null,"désactive")," la personne sur des dates. Dans l'onglet ",HE("b",null,"Type"),", cliquez sur ",HE("b",null,"la pastille ronde")," d'un médecin (éditeur seulement) : la fenêtre propose « sur toute la période affichée » ou « de date à date », et liste les indisponibilités déjà posées avec un bouton ▶ Réactiver chacune."]}),
  HP({children:["Pendant ses dates, la personne sort du ",HE("b",null,"tour, des gardes, du bip")," et des demandes de Construire. Sa pastille reste dans Type (grisée ⏸) pour la réactiver, et elle redevient disponible ",HE("b",null,"le jour de son retour"),", sans autre manipulation. Ce sont des ",HE("b",null,"dates")," qui sont enregistrées : changer la durée des périodes ne déplace rien."]}),
  HT({children:"⚠ Les limites à connaître"}),
  HP({children:["• ",HE("b",null,"Retirez ses activités avant de désactiver")," : la désactivation n'efface ",HE("b",null,"rien"),'. La fenêtre compte ce qui est posé sur les dates choisies et propose « 🧹 Retirer ses activités sur ces dates » (gardes, tour et absences comprises).']}),
  HP({children:["• L'",HE("b",null,"astreinte")," n'est pas couverte : gérez-la à part dans son onglet."]}),
  HP({last:true,children:["• L'éditeur peut toujours poser ",HE("b",null,"à la main")," un tour ou une garde sur quelqu'un de désactivé, depuis les tuiles 2 et 3 de Construire — le verrou porte sur les cases et les automatismes, pas sur un geste délibéré."]}))},

 {id:"internes",icon:"🎓",title:"Internes — l'onglet et les semestres",body:()=>HE("div",null,
  HP({children:["L'onglet ",HE("b",null,"🎓 Internes")," est facultatif : il s'affiche si la coche est mise dans ",HE("b",null,"Paramètres → tuile Internes"),". Contrairement à tous les autres onglets, il travaille ",HE("b",null,"par semestre de 6 mois")," et non par période de 4 mois — les flèches ‹ › passent d'un semestre au suivant."]}),
  HT({children:"Les semestres et les fiches"}),
  HP({children:["Tout se règle dans l'onglet ",HE("b",null,"Équipe"),", section Internes. Un semestre démarre le ",HE("b",null,"2 mai")," ou le ",HE("b",null,"2 novembre"),", reporté au ",HE("b",null,"lundi suivant")," si la date tombe un vendredi, un samedi ou un dimanche ; les dates restent modifiables à la main. Chaque interne y reçoit un nom, des initiales et une ",HE("b",null,"couleur"),", reprise partout."]}),
  HP({children:["« + Semestre suivant » se bloque à ",HE("b",null,"deux semestres ouverts")," (l'actuel et le prochain) — on ne connaît les internes que quelques semaines à l'avance. Un semestre ",HE("b",null,"pas encore commencé")," peut être supprimé (🗑) : la fin du précédent est recollée automatiquement."]}),
  HP({children:["La coche ☑ devant chaque interne dit s'il a ",HE("b",null,"accès aux salles"),". Sans elle, il n'est pas proposé dans les fenêtres de CHL, CHB, PT Cardio et PT Angio."]}),
  HT({children:"Ce qu'ils peuvent avoir, ce qu'ils peuvent poser"}),
  HP({children:["C'est l'onglet ",HE("b",null,"Activités")," qui décide, avec la coche ",HChip({txt:"🎓 Internes",bg:"#0e9f9f"})," : une activité cochée peut leur être posée. Une ",HE("b",null,"seconde coche")," dit s'ils peuvent la poser ",HE("b",null,"eux-mêmes")," (absences, FMC, gardes, HC/USIC en général) ; le reste est posé par un éditeur, un intermédiaire ou un cadre. Les activités ",HE("b",null,"à salle")," ne sont jamais posées par eux — elles le sont depuis leur onglet ou depuis les onglets de salle, avec choix de la salle."]}),
  HP({children:["Sur un ",HE("b",null,"lundi"),", poser HC ou USIC propose de ",HE("b",null,"remplir la semaine")," : le remplissage saute les repos de garde, absences et FMC déjà posés. Le ",HE("b",null,"samedi")," n'a qu'une case, pour le HC du samedi matin."]}),
  HT({children:"Les gardes"}),
  HP({children:["La colonne ",HE("b",null,"Garde")," de l'onglet fonctionne comme celle des médecins, ",HE("b",null,"sans répartition automatique"),". La garde se pose sur la nuit et le ",HBadg({txt:"RG",color:"#ffe599"})," repos est posé tout seul le lendemain — sauté, avec un avertissement, si l'interne est absent ou en FMC ce jour-là. ⇄ échange deux gardes directement, dans la liste de celles du semestre."]}),
  HP({children:["Un ",HE("b",null,"interne extérieur")," au service se saisit au nom libre : il apparaît dans la colonne, sans repos chez nous. Un jour ",HE("b",null,"sans personne de garde")," est signalé en rouge. Dans le Planning, la colonne « 🎓 Garde int. » s'affiche à la demande depuis la ligne Filtre, en ",HE("b",null,"lecture seule"),", et se remasque à chaque ouverture."]}),
  HT({children:"Jauge, statistiques, PIN"}),
  HP({children:[HBtn({kind:"ghost",children:"🚦"})," affiche la ",HE("b",null,"jauge")," H et U à gauche de chaque demi-journée, en rouge sous les seuils réglés dans Paramètres (un seuil à 0 = pas d'alerte). ",HBtn({kind:"ghost",children:"📊"})," ouvre les ",HE("b",null,"statistiques du semestre")," : gardes par catégorie, HC, USIC et les activités retenues — les colonnes affichées se choisissent dans Paramètres, tuile Internes."]}),
  HP({last:true,children:["Un ",HE("b",null,"PIN interne partagé")," se définit dans la même tuile. Avec lui, un interne saisit son prénom, arrive directement sur son onglet et ",HE("b",null,"ne peut modifier que celui-là")," : Planning, CHL, CHB, PT Cardio, PT Angio et l'Aide lui restent visibles en lecture seule."]}))},

 {id:"juniors",icon:"🩺",title:"Dr Juniors — un rôle, un nom par semestre",body:()=>HE("div",null,
  HP({children:["Une fiche de ",HE("b",null,"Dr Junior")," ne décrit pas une personne, mais un ",HE("b",null,"rôle")," : son nom, sa couleur, sa surspécialité, son planning type, ses coches tour et gardes. Tout cela ",HE("b",null,"ne change pas")," quand le titulaire change — c'est l'intérêt du mécanisme : le planning type se fait une fois pour toutes, et il n'y a jamais de fiche à recréer."]}),
  HP({children:["Ce qui change, c'est le ",HE("b",null,"nom du titulaire"),", saisi ",HE("b",null,"semestre par semestre")," dans la fiche (onglet Équipe), aux ",HE("b",null,"mêmes dates que les internes"),". Dès qu'il est saisi, ce sont ses initiales et son nom qui apparaissent partout — cases, fenêtres, infobulles, impression, export — et ",HE("b",null,"à la date près")," : une case du 4 mai affiche le nouveau titulaire même si vous la regardez depuis le mois d'avril."]}),
  HT({children:"Un rôle sans titulaire"}),
  HP({children:["Tant qu'aucun nom n'est saisi pour un semestre, le rôle est ",HE("b",null,"hachuré et verrouillé")," sur ces dates (voir la section précédente), et sa colonne disparaît si toute la période est concernée. La personne n'existe pas encore : rien ne peut lui être posé, pas même un congé. ",HE("b",null,"Saisir le nom déverrouille")," aussitôt, sans autre manipulation."]}),
  HP({children:["⚠ Conséquence pratique : ",HE("b",null,"saisissez les noms avant de construire la période"),". Sinon le planning type saute ces mois, et il faudra le réappliquer une fois les noms entrés."]}),
  HP({children:["Effacer un nom déjà saisi ",HE("b",null,"n'efface aucune activité")," : les cases se reverrouillent, le contenu reste dessous. La fiche le ",HE("b",null,"compte")," et propose de retirer ces activités si c'est ce que vous voulez."]}),
  HT({children:"Quand le changement tombe au milieu d'une période"}),
  HP({last:true,children:["Le changement du 2 novembre tombe sur une frontière de période : rien à gérer. Seule la période ",HE("b",null,"mars-juin")," contient une bascule. Dans ce cas, l'en-tête de colonne montre ",HE("b",null,"un seul jeu d'initiales"),", celui du titulaire du moment, et bascule tout seul le jour dit. Dans Construire, le tour et les gardes, le rôle reste ",HE("b",null,"une seule ligne")," portant les deux noms (« X puis Y ») : il compte ainsi sur la période entière, comme tout le monde."]}))},

 {id:"legende",icon:"🎨",title:"Légende",body:()=>HE("div",null,
  HP({children:[HAvat({txt:"TH",color:"#ec4899"})," pastille d'initiales : chaque médecin a sa couleur · ",HBadg({txt:"CORO",color:"#76a5af"})," badge d'activité, dans la couleur de l'activité."]}),
  HP({children:["Fiches Équipe : ",HChip({txt:"Garde",bg:"#16a34a"})," / ",HChip({txt:"Sans garde",bg:"#dc2626"})," · ",HChip({txt:"TM",bg:"#1d4ed8"})," / ",HChip({txt:"Sans TM",bg:"#d97706"}),"."]}),
  HP({children:["Sur-spécialités : ",HE("span",{style:{color:"#76a5af",fontWeight:800}},"Coro")," · ",HE("span",{style:{color:"#e3b341",fontWeight:800}},"Pace")," · ",HE("span",{style:{color:"#8b5cf6",fontWeight:800}},"EEP")," · ",HE("span",{style:{color:"#ec4899",fontWeight:800}},"ETT"),"."]}),
  HP({children:["⭐ souhaite (garde ou tour) · 🚫 préfère éviter · ⇄ échange · ✂ temps partiel · 📝 note sur la case."]}),
  HP({children:["👁 en haut de l'écran : mode consultation (lecture seule) · pastille ",HE("span",{style:{display:"inline-block",width:9,height:9,borderRadius:"50%",background:"#3fb950",margin:"0 2px"}})," verte en haut : synchronisation Firebase active (grise = hors ligne)."]}),
  HP({last:true,children:["Fonds : jaune pâle = week-end · bleuté = aujourd'hui · vert clair + contour vert = astreinte de la semaine · contour violet = exception d'astreinte posée sur un jour précis."]}))}
];

function HelpView(){
  const [hOpen,setHOpen]=React.useState({});
  const toggleH=(id)=>setHOpen(p=>Object.assign({},p,{[id]:!p[id]}));
  /* v10.100 : le rappel des tuiles en haut est retire a sa demande. Seules
     restent les tuiles depliables ci-dessous ; le raccourci de defilement
     n'avait plus d'appelant. */
  return HE("div",{style:{maxWidth:760}},
    HE("div",{style:{display:"flex",alignItems:"center",gap:8,marginBottom:10}},
      HE("h2",{style:{fontSize:17,fontWeight:800,color:"var(--txt)",margin:0}},"❓ Aide"),
      HE("span",{style:{fontSize:11,color:"var(--txt3)"}},"— cliquez sur une tuile pour l'ouvrir")),
    HELP_SECTIONS.map(s=>HE("div",{key:s.id,id:"help-"+s.id,style:{marginBottom:8,borderRadius:10,border:"1px solid var(--border)",background:"var(--card)",overflow:"hidden",scrollMarginTop:150}},
      HE("button",{onClick:()=>toggleH(s.id),
        style:{width:"100%",display:"flex",alignItems:"center",gap:9,padding:"11px 13px",border:"none",background:"transparent",cursor:"pointer",textAlign:"left"}},
        HE("span",{style:{fontSize:16}},s.icon),
        HE("span",{style:{flex:1,fontSize:13,fontWeight:800,color:"var(--txt)"}},s.title),
        HE("span",{style:{fontSize:11,color:"var(--txt3)",transform:hOpen[s.id]?"rotate(180deg)":"none",transition:"transform .18s"}},"▼")),
      hOpen[s.id]&&HE("div",{style:{padding:"2px 14px 13px"}},s.body()))));
}

/* ════ REPORTS (v9.2) — aide au report de consultations, composant partagé jsx/html ════ */
function ReportsView(p){
  const RE=React.createElement;
  const medecins=p.medecins,actes=p.actes,getEntries=p.getEntries,tourMed=p.tourMed,planningType=p.planningType,
    isVac=p.isVac,isEdit=p.isEdit,editMedId=p.editMedId,accessMode=p.accessMode,
    csBlanches=p.csBlanches,setCsBlanches=p.setCsBlanches,csActsSel=p.csActsSel,setCsActsSel=p.setCsActsSel,
    year=p.year,month=p.month,toast=p.toast;
  const medsCS=medecins.filter(m=>m.role==="medecin");
  const [selId,setSelId]=React.useState(accessMode==="medecinEdit"?editMedId:(medsCS[0]?medsCS[0].id:null));
  const medSelRaw=medecins.find(m=>m.id===(accessMode==="medecinEdit"?editMedId:selId));
  /* v10.35.1 : valeur de repli — les hooks qui suivent doivent s'exécuter à TOUS
     les rendus. La garde est descendue juste avant le rendu (règle des hooks). */
  const medSel=medSelRaw||{id:"__aucun__",init:"",nom:"",prenom:""};
  const mid=medSel.id;
  const editable=isEdit||(accessMode==="medecinEdit"&&editMedId===mid)||p.adminReports===true;
  const dk3=(y,m,d)=>y+"-"+m+"-"+d;
  /* ── v9.14 : registre des reports (persisté, partagé avec les secrétaires) ── */
  const repAll=(p.csRep&&p.csRep[mid])||{};
  const repDone=repAll.done||{};
  const repTo=repAll.to||{};
  const lostK=(o)=>dk3(o.y,o.m,o.d)+"|"+o.sl;
  const setRep=(fn)=>{if(!p.setCsRep)return;p.setCsRep(pr=>{const cur=pr[mid]||{};const nx={done:{...(cur.done||{})},to:{...(cur.to||{})}};fn(nx);const out={...pr};out[mid]=nx;return out;});};
  /* v10.24 : le pointage « rouvert » se fait par DEMI-JOURNEE (avant : par semaine)
     et retient QUI l'a fait. Les anciennes coches par semaine deviennent inertes. */
  const doneK=(o)=>dk3(o.y,o.m,o.d)+"|"+o.sl;
  const doneInfo=(o)=>{const v=repDone[doneK(o)];if(!v)return null;return (typeof v==="object")?v:{by:"",at:""};};
  const toggleDone=(o)=>setRep(c=>{const k=doneK(o);if(c.done[k])delete c.done[k];else c.done[k]={by:whoNow(),at:jourMois()};});
  const setReport=(o,dest,note)=>setRep(c=>{c.to[lostK(o)]={d:dk3(dest.y,dest.m,dest.d),sl:dest.sl,n:note||""};});
  const clrReport=(o)=>setRep(c=>{delete c.to[lostK(o)];});
  const setRepNote=(o,txt)=>setRep(c=>{const k=lostK(o);if(c.to[k])c.to[k]={...c.to[k],n:txt};});
  const [repModal,setRepModal]=React.useState(null);
  const [repStep,setRepStep]=React.useState(null);/* 2e temps : combien de patients, quelle salle */
  const [showG3,setShowG3]=React.useState(false);/* 3e groupe de la modale, replie par defaut */
  const [weekModal,setWeekModal]=React.useState(null);/* bouton violet : choix d'une autre semaine */
  const dkParse=(s)=>{const q=String(s).split("-");return {y:+q[0],m:+q[1],d:+q[2]};};
  /* ── v10.24 : petits nombres en toutes lettres dans les libelles ── */
  const NLET=["zéro","un","deux","trois","quatre","cinq","six","sept","huit","neuf","dix","onze","douze","treize","quatorze","quinze","seize","dix-sept","dix-huit","dix-neuf","vingt"];
  const enLet=(n)=>(n>=0&&n<=20)?NLET[n]:String(n);
  const enLetF=(n)=>n===1?"une":enLet(n);/* feminin : « une semaine » */
  const cap1=(s)=>s.charAt(0).toUpperCase()+s.slice(1);
  const ecLbl=(n)=>(n>=0?"+ ":"− ")+Math.abs(n)+" j";
  /* Une proposition ne s'ecarte JAMAIS de plus d'un mois de la semaine d'origine */
  const MAXEC=31;
  const jourMois=()=>{const t=new Date();return t.getDate()+"/"+(t.getMonth()+1<10?"0":"")+(t.getMonth()+1);};
  /* ── v10.27 : SIGNATURE COURTE des lignes de commentaire. Meme regle que
     `whoNow` ci-dessous, mais les INITIALES pour un medecin — un commentaire
     est une ligne, pas une pastille, et « TH » suffit a dire qui a ecrit.
     L'administratif garde son prenom : il n'a pas d'initiales dans l'equipe. ── */
  const sigNow=()=>{
    if(accessMode==="medecinEdit"&&editMedId){const me=medecins.find(m=>m.id===editMedId);
      if(me)return (me.init||"?");}
    if(p.adminReports&&p.adminName)return String(p.adminName).trim();
    return "Éditeur";
  };
  /* Qui rouvre : le medecin connecte avec son PIN, sinon le prenom saisi par
     l'administratif, sinon l'editeur (toujours la meme personne). */
  const whoNow=()=>{
    if(accessMode==="medecinEdit"&&editMedId){const me=medecins.find(m=>m.id===editMedId);
      if(me)return ((me.prenom||"")+" "+(me.nom||"")).trim();}
    if(p.adminReports&&p.adminName)return String(p.adminName).trim();
    return "Éditeur";
  };
  const wkOf=(y,m,d)=>{const dt=new Date(y,m,d);const dw=dt.getDay();const diff=dw===0?-6:1-dw;const mn=new Date(y,m,d+diff);return dk3(mn.getFullYear(),mn.getMonth(),mn.getDate());};
  /* ── Période : sélecteur local, défaut = période suivante (outil de préparation) ── */
  const [repPer,setRepPer]=React.useState(()=>{const t=new Date();const p0=perStart(t.getFullYear(),t.getMonth());return perNext(p0.sy,p0.sm);});
  const per=repPer;
  const perLbl=MOIS[per.sm]+" — "+MOIS[(per.sm+PCFG.len-1)%12]+" "+per.sy;
  const days=React.useMemo(()=>perDaysList(per.sy,per.sm),[per.sy,per.sm]);
  const weeks=React.useMemo(()=>{
    const map={},order=[];
    days.forEach(o=>{const dw=new Date(o.y,o.m,o.d).getDay();if(dw===0||dw===6)return;
      const wk=wkOf(o.y,o.m,o.d);if(!map[wk]){map[wk]=[];order.push(wk);}map[wk].push(o);});
    return order.map(wk=>({key:wk,days:map[wk]}));
  },[days]);
  /* ── Blanches du médecin ── */
  const bl=csBlanches[mid]||{};
  const isBl=(y,m,d)=>!!bl[dk3(y,m,d)];
  const setBlDays=(list,on)=>{
    if(!editable)return;
    setCsBlanches(prev=>{const cur=Object.assign({},prev[mid]||{});
      list.forEach(o=>{const k=dk3(o.y,o.m,o.d);if(on)cur[k]=true;else delete cur[k];});
      return Object.assign({},prev,{[mid]:cur});});
  };
  const prefillVac=()=>{
    const vd=days.filter(o=>{const dw=new Date(o.y,o.m,o.d).getDay();return dw>=1&&dw<=5&&isVac(o.y,o.m,o.d)&&!isFerie(o.y,o.m,o.d);});
    if(vd.length===0){toast("Aucune vacance scolaire chargée sur la période","warn");return;}
    setBlDays(vd,true);toast(vd.length+" jour(s) de vacances scolaires précochés — ajustez ensuite","info");
  };
  /* ── Activités "consultation" du médecin ── */
  const flagged=actes.filter(a=>a.csReport===true).map(a=>a.id);
  const globalOK=flagged.length?flagged:((p.csActsGlobal&&p.csActsGlobal.length)?p.csActsGlobal:["CS_CHL","CS_CHB","DOBU","DOBU_CHB","ETO_CHL","PM_CS","DEFIB_CS","RYTHMO_CHB"]);
  const defActs=actes.filter(a=>globalOK.indexOf(a.id)>=0).map(a=>a.id).filter(id=>id==="CS_CHL"||id==="CS_CHB");
  const myActs=(csActsSel[mid]&&csActsSel[mid].length?csActsSel[mid]:defActs).filter(id=>globalOK.indexOf(id)>=0);
  const toggleAct=(aid)=>{if(!editable)return;
    setCsActsSel(prev=>{const cur=(prev[mid]&&prev[mid].length?prev[mid]:defActs).slice();
      const i=cur.indexOf(aid);if(i>=0)cur.splice(i,1);else cur.push(aid);
      return Object.assign({},prev,{[mid]:cur});});};
  const candActs=actes.filter(a=>globalOK.indexOf(a.id)>=0&&(!(a.medecinsAutorise&&a.medecinsAutorise.length)||a.medecinsAutorise.includes(authI(medSel))));
  /* ── Jours habituels de consultation (planning type) ── */
  const pt=planningType[mid]||{};
  const habCS={};// {dw:{M:acteId,AM:acteId}}
  [1,2,3,4,5].forEach(dw=>["M","AM"].forEach(sl=>{
    const e=(pt[dw]||{})[sl];if(e&&e[0]&&myActs.indexOf(e[0])>=0){if(!habCS[dw])habCS[dw]={};habCS[dw][sl]=e[0];}
  }));
  const habList=[];Object.keys(habCS).forEach(dw=>Object.keys(habCS[dw]).forEach(sl=>habList.push({dw:+dw,sl})));
  const habDW=Object.keys(habCS).map(Number); // jours de la semaine avec consultation habituelle
  /* ── Analyse ── */
  const JR=["Dim","Lun","Mar","Mer","Jeu","Ven","Sam"];/* v10.25 : aussi utilise par la modale */
  const fmtD=(o)=>JR[new Date(o.y,o.m,o.d).getDay()]+" "+o.d+" "+MOIS[o.m].slice(0,4);
  const inTour=(y,m,d)=>{const wm=tourMed[wkOf(y,m,d)]||{};return((wm.HC||[]).includes(mid)||(wm.USIC||[]).includes(mid));};
  const slotState=(y,m,d,sl)=>{
    const es=getEntries(mid,y,m,d,sl);
    if(es.some(e=>ABS_IDS.includes(e.acteId))||(es[0]&&es[0]._blocked))return "abs";
    if(es.length>0)return "busy";
    return "free";
  };
  const acteOf=(id)=>actes.find(a=>a.id===id);
  /* Sur une semaine blanche, une date habituelle portant uniquement l'activité de consultation (posée par le type) est disponible : la blanche est vide de patients */
  const slotFreeCS=(y,m,d,sl)=>{const es=getEntries(mid,y,m,d,sl);if(es.length===0)return true;if(es[0]&&es[0]._blocked)return false;return es.every(e=>myActs.indexOf(e.acteId)>=0);};
  /* ── v10.24 : « des que l'on modifie quelque chose d'une consultation il faut le
     preciser dans le commentaire ». On AJOUTE une ligne, on n'ecrase jamais ce qui
     a ete ecrit a la main — y compris quand un report est annule.
     v10.27 : chaque ligne ajoutee est ESTAMPILLEE « 12/08 · TH — … ». Les lignes
     s'empilent : sans date ni auteur, on ne sait plus ce qui a ete fait quand ni
     par qui. L'estampille est en TETE pour que les lignes s'alignent et se lisent
     comme un journal. Les commentaires tapes a la main ne sont pas touches. ── */
  const addNote=(dest,txt)=>{if(!p.setNotes)return;
    const lg=jourMois()+" · "+sigNow()+" — "+txt;
    p.setNotes(pn=>{const k=nk(mid,dest.y,dest.m,dest.d,dest.sl);const cur=(pn[k]||"").trim();
      const nn={...pn};nn[k]=cur?(cur+"\n"+lg):lg;return nn;});};
  /* ── v10.25 : une consultation perdue peut etre DIVISEE ────────────────────
     csRep[mid].to[<demi-journee perdue>] = {
       tot   : nombre total de patients, ou null tant qu'il n'est pas divise
       att   : nombre parti en liste d'attente
       n     : note libre
       parts : [ {d,sl,n,salle,cree} ]   n=null -> la consultation entiere
                                          cree=true -> la CS a ete creee dans le planning
     }
     La case tot VIDE veut dire « toute la consultation part d'un bloc » ; un nombre
     veut dire « je divise ». C'est la case elle-meme qui porte l'information. */
  const repOf=(L)=>repTo[lostK(L)]||null;
  const partsOf=(L)=>{const r=repOf(L);return (r&&r.parts)||[];};
  const totOf=(L)=>{const r=repOf(L);return (r&&typeof r.tot==="number")?r.tot:null;};
  const attOf=(L)=>{const r=repOf(L);return (r&&r.att)||0;};
  const placeOf=(L)=>partsOf(L).reduce((s,q)=>s+(q.n||0),0);
  const resteOf=(L)=>{const t=totOf(L);if(t===null)return null;return Math.max(0,t-placeOf(L)-attOf(L));};
  const incomplet=(L)=>{const r=resteOf(L);return r!==null&&r>0;};
  const vide={tot:null,att:0,n:"",parts:[]};
  const setTot=(L,v)=>setRep(c=>{const k=lostK(L),cur=c.to[k]||vide;
    c.to[k]={...cur,tot:(v===""||v===null)?null:Math.max(0,parseInt(v,10)||0)};});
  const addPart=(L,q)=>setRep(c=>{const k=lostK(L),cur=c.to[k]||vide;
    c.to[k]={...cur,parts:(cur.parts||[]).concat([q])};});
  const delPart=(L,i)=>setRep(c=>{const k=lostK(L),cur=c.to[k];if(!cur)return;
    const ps=(cur.parts||[]).slice();ps.splice(i,1);
    if(ps.length===0&&cur.tot===null&&!cur.att&&!cur.n)delete c.to[k];else c.to[k]={...cur,parts:ps};});
  const setAtt=(L,v)=>setRep(c=>{const k=lostK(L),cur=c.to[k]||vide;c.to[k]={...cur,att:Math.max(0,v)};});
  const setRepNote2=(L,txt)=>setRep(c=>{const k=lostK(L),cur=c.to[k]||vide;c.to[k]={...cur,n:txt};});
  const txtPat=(nb)=>nb===null?"":(", "+enLet(nb)+" patient"+(nb>1?"s":""));
  /* Poser sur une semaine blanche : la consultation existe deja, elle n'attend que
     ses patients — aucune salle a choisir, et elle reprend tout ce qui reste. */
  const poseBlanche=(L,dest)=>{const a2=acteOf(L.acte),t=totOf(L),nb=(t===null)?null:resteOf(L);
    addPart(L,{d:dk3(dest.y,dest.m,dest.d),sl:dest.sl,n:nb,salle:null,cree:false});
    addNote(dest,"Report du "+fmtD(L)+" "+L.sl+txtPat(nb)+(a2?" ("+(a2.short||a2.label)+")":""));};
  /* Poser sur un creneau de tour ou un autre jour : la consultation est CREEE dans le
     planning, avec sa salle, et ne reprend qu'une part des patients. */
  const poseCree=(L,dest,nb,salle)=>{const a2=acteOf(L.acte);
    if(p.addEntry)p.addEntry(mid,dest.y,dest.m,dest.d,dest.sl,{acteId:L.acte,salle:salle||null});
    addPart(L,{d:dk3(dest.y,dest.m,dest.d),sl:dest.sl,n:nb,salle:salle||null,cree:true});
    addNote(dest,"Report du "+fmtD(L)+" "+L.sl+txtPat(nb)+(a2?" ("+(a2.short||a2.label)+")":""));};
  const annulPart=(L,i)=>{const q=partsOf(L)[i];if(!q)return;const D=dkParse(q.d);
    if(q.cree&&p.removeEntry)p.removeEntry(mid,D.y,D.m,D.d,q.sl,L.acte);
    addNote({y:D.y,m:D.m,d:D.d,sl:q.sl},"Report annulé"
      +(q.cree?", consultation retirée du planning":", demi-journée redevenue libre"));
    delPart(L,i);};
  /* Salles reellement libres pour l'activite reportee ; null = activite sans salle */
  const sallesLibres=(L,o,sl)=>{const a2=acteOf(L.acte);
    if(!a2||!a2.hasSalle)return null;
    const occ=occSalles(o.y,o.m,o.d,sl);return (a2.salles||[]).filter(s=>!occ[s]);};
  const seulLeTour=(y,m,d,sl)=>{const es=getEntries(mid,y,m,d,sl);
    return es.length>0&&es.every(e=>e&&(e.acteId==="TOUR_HC"||e.acteId==="TOUR_USIC"));};
  const analysis=React.useMemo(()=>{
    /* Semaines à reporter : dates habituelles perdues (tour ou absence) hors blanche, groupées par semaine */
    const lostByWeek={},weekOrder=[];
    days.forEach(o=>{
      const dt=new Date(o.y,o.m,o.d),dw=dt.getDay();
      if(dw===0||dw===6||isFerie(o.y,o.m,o.d))return;
      const blanche=isBl(o.y,o.m,o.d),tour=inTour(o.y,o.m,o.d);
      ["M","AM"].forEach(sl=>{
        const hab=habCS[dw]&&habCS[dw][sl];
        if(!hab)return;
        const st=slotState(o.y,o.m,o.d,sl);
        if(!blanche&&(tour||st==="abs")){
          const wk=wkOf(o.y,o.m,o.d);
          if(!lostByWeek[wk]){lostByWeek[wk]=[];weekOrder.push(wk);}
          lostByWeek[wk].push({y:o.y,m:o.m,d:o.d,sl,dw,acte:hab,why:tour?"tour":"absence"});
        }
      });
    });
    /* Semaines blanches d'accueil */
    const recvWeeks=weeks.filter(w=>{
      const wm=tourMed[w.key]||{};if((wm.HC||[]).includes(mid)||(wm.USIC||[]).includes(mid))return false;
      if(lostByWeek[w.key])return false;
      return habList.some(hb=>{const o=w.days.find(x=>new Date(x.y,x.m,x.d).getDay()===hb.dw);
        return o&&isBl(o.y,o.m,o.d)&&!isFerie(o.y,o.m,o.d)&&slotFreeCS(o.y,o.m,o.d,hb.sl);});
    });
    /* ── v10.24 : appariement semaine → semaine blanche ───────────────────────
       Deux regles posees le 11/08/2026 :
       (1) une proposition ne s'ecarte JAMAIS de plus de 31 jours, en avant comme en
           arriere (avancer des patients est permis) ; la periode affichee borne le
           reste, au-dela cela se regle directement avec le secretariat ;
       (2) l'attribution ne se fait plus semaine par semaine dans l'ordre du
           calendrier. Le premier arrive consommait la blanche dont une semaine
           ULTERIEURE avait bien plus besoin (blanche du 12 Octo partie a la semaine
           du 14 Sept, a 4 semaines, alors que le 19 Octo l'attendait a 1 semaine).
           On construit TOUTES les paires possibles, on les trie par ecart croissant,
           et on attribue dans cet ordre. */
    const pairsAll=[];
    weekOrder.forEach(wk=>{
      const lost=lostByWeek[wk];
      const src=new Date(lost[0].y,lost[0].m,lost[0].d);
      recvWeeks.forEach(w=>{
        const fits=lost.every(L=>{const o=w.days.find(x=>new Date(x.y,x.m,x.d).getDay()===L.dw);
          return o&&isBl(o.y,o.m,o.d)&&!isFerie(o.y,o.m,o.d)&&slotFreeCS(o.y,o.m,o.d,L.sl);});
        if(!fits)return;
        const o0=w.days.find(x=>new Date(x.y,x.m,x.d).getDay()===lost[0].dw);
        if(!o0)return;
        const ec=Math.round((new Date(o0.y,o0.m,o0.d)-src)/86400000);
        if(Math.abs(ec)>MAXEC)return;
        pairsAll.push({wk,w,ec});
      });
    });
    /* ecart absolu croissant ; a egalite l'avant plutot que l'arriere, puis le calendrier */
    pairsAll.sort((A,B)=>(Math.abs(A.ec)-Math.abs(B.ec))||(B.ec-A.ec)||(A.wk<B.wk?-1:1));
    const usedW=new Set(),takenWk={};
    pairsAll.forEach(PR=>{
      if(takenWk[PR.wk]||usedW.has(PR.w.key))return;
      takenWk[PR.wk]=PR;usedW.add(PR.w.key);
    });
    const weekPairs=weekOrder.map(wk=>{
      const lost=lostByWeek[wk],got=takenWk[wk],best=got?got.w:null;
      const dest=best?lost.map(L=>{const o=best.days.find(x=>new Date(x.y,x.m,x.d).getDay()===L.dw);return {y:o.y,m:o.m,d:o.d,sl:L.sl};}):null;
      return {wk,lost,to:best,dest,ec:got?got.ec:null};
    });
    /* Dates habituelles disponibles en blanche et demi-journees off.
       v10.24 : les destinations proposees ne sont PLUS retirees de cette liste —
       c'est la ligne de la blanche qui dit ce qu'elle accueille, deduit de l'etat
       courant demi-journee par demi-journee, jamais memorise. */
    const restHab=[],offs=[];
    days.forEach(o=>{
      const dt=new Date(o.y,o.m,o.d),dw=dt.getDay();
      if(dw===0||dw===6||isFerie(o.y,o.m,o.d))return;
      if(inTour(o.y,o.m,o.d))return;
      const blanche=isBl(o.y,o.m,o.d);
      ["M","AM"].forEach(sl=>{
        const hab=habCS[dw]&&habCS[dw][sl];
        if(blanche&&hab&&slotFreeCS(o.y,o.m,o.d,sl))restHab.push({y:o.y,m:o.m,d:o.d,sl,acte:hab});
        else if(!blanche&&!hab&&slotState(o.y,o.m,o.d,sl)==="free")offs.push({y:o.y,m:o.m,d:o.d,sl,dw});
      });
    });
    /* ── v10.24 : la liste porte TOUTES les semaines de la periode, y compris celles
       ou il n'y a rien a faire — « pour etre sur de ne rien oublier ». Le champ grp
       sert aux pastilles de filtre du haut. ── */
    const pairByWk={};weekPairs.forEach(wp=>{pairByWk[wp.wk]=wp;});
    const restHabByWk={};restHab.forEach(o=>{const wk=wkOf(o.y,o.m,o.d);(restHabByWk[wk]=restHabByWk[wk]||[]).push(o);});
    const weekItems=[];
    weeks.forEach(w=>{
      const wm=tourMed[w.key]||{};const isTW=((wm.HC||[]).includes(mid)||(wm.USIC||[]).includes(mid));
      const wp=pairByWk[w.key];
      if(wp)weekItems.push({kind:wp.to?"report":"norep",grp:wp.to?"todo":"none",wk:w.key,days:w.days,
        lost:wp.lost,to:wp.to,dest:wp.dest,ec:wp.ec,why:wp.lost.some(L=>L.why==="tour")?"tour":"absence"});
      else if(restHabByWk[w.key])weekItems.push({kind:"recv",grp:"recv",wk:w.key,days:w.days,dates:restHabByWk[w.key]});
      else if(isTW)weekItems.push({kind:"ok",grp:"rien",wk:w.key,days:w.days});
      else weekItems.push({kind:"rien",grp:"rien",wk:w.key,days:w.days});
    });
    /* Offs regroupés par semaine */
    const offByWk={};offs.forEach(o=>{const wk=wkOf(o.y,o.m,o.d);const b=(offByWk[wk]=offByWk[wk]||{});(b[o.dw]=b[o.dw]||[]).push(o.sl);});
    const offWeeks=weeks.filter(w=>offByWk[w.key]).map(w=>({key:w.key,days:w.days,slots:offByWk[w.key]}));
    return {weekPairs,weekItems,offWeeks};
  },[days,weeks,bl,tourMed,planningType,myActs.join(","),mid]);
  /* ── v10.24 : ce qui atterrit sur chaque demi-journee blanche, DEDUIT de l'etat
     courant (report valide, ou simple proposition). Se met donc a jour tout seul
     s'il repartit les deux consultations d'une semaine sur des semaines differentes. */
  const propAt={},validAt={};
  analysis.weekPairs.forEach(wp=>wp.lost.forEach((L,k)=>{
    const ps=partsOf(L);
    if(ps.length)ps.forEach(q=>{validAt[q.d+"|"+q.sl]=L;});
    else if(wp.dest&&wp.dest[k])propAt[dk3(wp.dest[k].y,wp.dest[k].m,wp.dest[k].d)+"|"+wp.dest[k].sl]=L;
  }));
  const [hidGrp,setHidGrp]=React.useState({});
  /* ── v9.12 : salles libres sur les demi-journées off ── */
  const [freeModal,setFreeModal]=React.useState(null);
  const [freeStep,setFreeStep]=React.useState(null);
  /* v10.49 : les salles PARTICIPANTES — cochées « ouvrable sur un off » sur leur
     fiche (Paramètres → Salles) ; non renseigné = les salles de consultation
     (précochage). Tout le bas de l'onglet ne voit qu'elles ; les REPORTS du
     haut, eux, ne passent pas par ici et ne changent pas. */
  const offSalleSet=React.useMemo(()=>{
    const s=new Set();
    (p.salleReg||[]).forEach(x=>{if(offOuvOn(x,actes))s.add(x.n);});
    return s;
  },[p.salleReg,actes]);
  const myActesAll=actes.filter(a=>!a.isSystem&&a.id!=="TP"
    &&(!(a.medecinsAutorise&&a.medecinsAutorise.length)||a.medecinsAutorise.indexOf(authI(medSel))>=0)
    &&(!p.adminReports||a[p.adminOkKey||"adminOk"]===true));
  const myActesOff=myActesAll.filter(a=>a.hasSalle&&(a.salles||[]).some(s=>offSalleSet.has(s)));   /* v10.49 : ouvrables — au moins une salle participante */
  const occSalles=(yy,mm,dd,ss)=>{const s={};medecins.forEach(mb=>getEntries(mb.id,yy,mm,dd,ss).forEach(e=>{if(e&&e.salle)s[e.salle]=true;}));return s;};
  const freeFor=(a,occ)=>(a.salles||[]).filter(s=>offSalleSet.has(s)&&!occ[s]);   /* v10.49 : participantes seulement */
  const hasFreeRoom=(yy,mm,dd,ss)=>{const occ=occSalles(yy,mm,dd,ss);return myActesOff.some(a=>freeFor(a,occ).length>0);};
  const dayOf=(w,dw)=>w.days.find(x=>new Date(x.y,x.m,x.d).getDay()===dw);
  const poseFree=(a,salle,lost)=>{
    const F=freeModal;if(!F||!p.addEntry)return;
    p.addEntry(mid,F.y,F.m,F.d,F.sl,{acteId:a.id,salle:salle||null});
    if(lost&&p.setNotes)p.setNotes(pn=>{const nn={...pn};nn[nk(mid,F.y,F.m,F.d,F.sl)]="Report de la "+(a.short||a.label)+" du "+fmtD(lost)+" "+lost.sl;return nn;});
    if(lost)setReport(lost,{y:F.y,m:F.m,d:F.d,sl:F.sl},"posé depuis les salles libres");
    setFreeModal(null);setFreeStep(null);
    if(toast)toast("Ajouté"+(salle?" — "+salle:""));
  };
  const exportCSVR=()=>{
    const rows=[["Consultation perdue","Activité","Cause","Report proposé"]];
    analysis.weekPairs.forEach(wp=>wp.lost.forEach((L,i)=>{
      const a2=acteOf(L.acte);
      rows.push([fmtD(L)+" "+L.sl,a2?a2.short:L.acte,L.why==="tour"?"Semaine de tour":"Absence",
        (partsOf(L).length
          ?partsOf(L).map(q=>fmtD(dkParse(q.d))+" "+q.sl+(q.n===null?" (entière)":" ("+q.n+" patients)")).join(" + ")
            +(attOf(L)?" + "+attOf(L)+" en liste d'attente":"")
          :(wp.dest?(fmtD(wp.dest[i])+" "+wp.dest[i].sl+" (proposé, semaine blanche)"):"Pas de report possible"))]);
    }));
    const csv=rows.map(r=>r.map(v=>'"'+String(v).replace(/"/g,'""')+'"').join(";")).join("\n");
    const blob=new Blob(["\ufeff"+csv],{type:"text/csv;charset=utf-8"});
    const a=document.createElement("a");a.href=URL.createObjectURL(blob);a.download="reports-consultations.csv";a.click();
  };
  /* ── Rendu ── */
  const cellSt=(o,dw)=>{
    const blanche=isBl(o.y,o.m,o.d),tour=inTour(o.y,o.m,o.d),fer=isFerie(o.y,o.m,o.d);
    const absD=slotState(o.y,o.m,o.d,"M")==="abs"||slotState(o.y,o.m,o.d,"AM")==="abs";
    return {blanche,tour,fer,absD};
  };
  if(!medSelRaw)return RE("div",{style:{color:"var(--txt3)",fontSize:12}},"Aucun médecin.");
  return RE("div",{style:{maxWidth:820}},
    RE("div",{style:{display:"flex",alignItems:"center",gap:10,marginBottom:10,flexWrap:"wrap",position:"sticky",top:HDR_H,zIndex:40,background:"var(--bg)",paddingTop:6,paddingBottom:6}},
      RE("h2",{style:{fontSize:17,fontWeight:800,color:"var(--txt)",margin:0}},"📥 Reports de consultations"),
      accessMode==="medecinEdit"
        ?RE("span",{style:{fontSize:12,fontWeight:700,color:"var(--txt)"}},medSel.prenom+" "+medSel.nom)
        :RE("select",{value:selId||"",onChange:e=>setSelId(parseInt(e.target.value)),style:{padding:"5px 8px",borderRadius:7,border:"1px solid var(--border)",background:"var(--bg2)",color:"var(--txt)",fontSize:12,fontWeight:700}},
          medsCS.map(m=>RE("option",{key:m.id,value:m.id},"Dr. "+m.prenom+" "+m.nom))),
      RE("span",{style:{display:"inline-flex",alignItems:"center",gap:4,marginLeft:"auto"}},
        RE("button",{onClick:()=>setRepPer(pp=>perPrev(pp.sy,pp.sm)),style:{fontSize:12,padding:"3px 9px",borderRadius:6,border:"1px solid var(--border)",background:"var(--bg2)",color:"var(--txt)",cursor:"pointer",fontWeight:800}},"◀"),
        RE("span",{style:{fontSize:12,fontWeight:800,color:"#1d4ed8",minWidth:150,textAlign:"center"}},perLbl),
        RE("button",{onClick:()=>setRepPer(pp=>perNext(pp.sy,pp.sm)),style:{fontSize:12,padding:"3px 9px",borderRadius:6,border:"1px solid var(--border)",background:"var(--bg2)",color:"var(--txt)",cursor:"pointer",fontWeight:800}},"▶"))),
    RE("div",{style:{fontSize:11,color:"var(--txt3)",marginBottom:12,lineHeight:1.6}},
      "Outil individuel et facultatif : cochez vos jours/semaines sans consultation (« blanches ») laissés par votre secrétaire dans le logiciel métier, l'application propose ensuite les reports les plus adaptés."),
    editable&&RE("div",{style:{display:"flex",gap:6,marginBottom:10,flexWrap:"wrap"}},
      RE("button",{onClick:prefillVac,style:{fontSize:11,padding:"4px 10px",borderRadius:6,border:"1.5px solid #f59e0b",background:"rgba(245,158,11,.10)",color:"#b45309",fontWeight:800,cursor:"pointer"}},"☀️ Précocher les vacances scolaires"),
      RE("button",{onClick:()=>{if(confirm("Effacer toutes vos semaines blanches de la période ?"))setCsBlanches(prev=>Object.assign({},prev,{[mid]:{}}));},
        style:{fontSize:11,padding:"4px 10px",borderRadius:6,border:"1px solid var(--border)",background:"var(--bg2)",color:"var(--txt2)",fontWeight:700,cursor:"pointer"}},"Tout effacer")),
    RE("div",{style:{fontSize:10,fontWeight:800,color:"var(--txt2)",textTransform:"uppercase",letterSpacing:.4,marginBottom:5}},"Mes activités de consultation"),
    RE("div",{style:{display:"flex",flexWrap:"wrap",gap:4,marginBottom:12}},
      candActs.map(a=>{const on=myActs.indexOf(a.id)>=0;
        return RE("button",{key:a.id,onClick:()=>toggleAct(a.id),disabled:!editable,
          style:{fontSize:10,padding:"3px 8px",borderRadius:11,cursor:editable?"pointer":"default",fontWeight:700,
            border:on?"1.5px solid "+a.color:"1px solid var(--border)",background:on?a.color+"33":"var(--bg2)",color:on?"var(--txt)":"var(--txt3)"}},a.short);})),
    habList.length===0&&RE("div",{style:{fontSize:11,color:"#b45309",background:"rgba(245,158,11,.10)",border:"1px solid rgba(245,158,11,.4)",borderRadius:7,padding:"6px 10px",marginBottom:12}},
      "Aucune demi-journée de consultation trouvée dans votre planning type pour ces activités — renseignez votre planning type (onglet Type) ou ajustez les activités ci-dessus."),
    /* Calendrier des semaines */
    RE("div",{style:{fontSize:10,fontWeight:800,color:"var(--txt2)",textTransform:"uppercase",letterSpacing:.4,marginBottom:5}},"Semaines blanches (cliquez un jour, ou « Sem. » pour la semaine entière)"),
    RE("div",{style:{overflowX:"auto",border:"1px solid var(--border)",borderRadius:8,marginBottom:14}},
      RE("table",{style:{borderCollapse:"collapse",width:"100%"}},
        RE("thead",null,RE("tr",null,
          RE("th",{style:{padding:"4px 8px",fontSize:9,color:"var(--txt3)",textAlign:"left",background:"var(--th)"}},"Semaine"),
          ["Lun","Mar","Mer","Jeu","Ven"].map(j=>RE("th",{key:j,style:{padding:"4px 6px",fontSize:9,color:"var(--txt3)",background:"var(--th)"}},j)),
          RE("th",{style:{padding:"4px 6px",fontSize:9,color:"var(--txt3)",background:"var(--th)"}},""))),
        RE("tbody",null,weeks.map(w=>{
          const allBl=w.days.every(o=>isBl(o.y,o.m,o.d)||isFerie(o.y,o.m,o.d));
          const first=w.days[0];
          const wm=tourMed[w.key]||{};const isTW=((wm.HC||[]).includes(mid)||(wm.USIC||[]).includes(mid));
          return RE("tr",{key:w.key,style:{borderTop:"1px solid var(--border2)"}},
            RE("td",{style:{padding:"3px 8px",fontSize:10,fontWeight:700,color:isTW?"#1d4ed8":"var(--txt)",whiteSpace:"nowrap"}},
              first.d+" "+MOIS[first.m].slice(0,4)+(isTW?" · TOUR":"")),
            [1,2,3,4,5].map(dw=>{
              const o=w.days.find(x=>new Date(x.y,x.m,x.d).getDay()===dw);
              if(!o)return RE("td",{key:dw,style:{padding:"2px"}});
              const st=cellSt(o,dw);
              return RE("td",{key:dw,onClick:()=>{if(!st.fer)setBlDays([o],!st.blanche);},
                title:st.fer?"Férié":(st.blanche?"Blanche — cliquer pour retirer":"Cliquer pour marquer blanche"),
                style:{padding:"4px 2px",textAlign:"center",fontSize:10,fontWeight:800,
                  cursor:st.fer||!editable?"default":"pointer",
                  background:st.fer?"var(--bg2)":st.blanche?"rgba(245,158,11,.25)":st.tour?"rgba(29,78,216,.12)":"transparent",
                  color:st.fer?"var(--txt3)":st.absD?"#ef4444":"var(--txt)",
                  border:"1px solid var(--border2)",borderRadius:4}},
                st.fer?"F":o.d);
            }),
            RE("td",{style:{padding:"2px 6px",textAlign:"center"}},
              editable&&RE("button",{onClick:()=>setBlDays(w.days.filter(o=>!isFerie(o.y,o.m,o.d)),!allBl),
                style:{fontSize:9,padding:"2px 7px",borderRadius:5,border:"1px solid var(--border)",background:allBl?"rgba(245,158,11,.25)":"var(--bg2)",color:"var(--txt2)",fontWeight:800,cursor:"pointer"}},"Sem.")));
        })))),
    RE("div",{style:{fontSize:9,color:"var(--txt3)",marginBottom:14}},
      RE("span",{style:{background:"rgba(245,158,11,.25)",padding:"0 6px",borderRadius:3,marginRight:6}},"blanche"),
      RE("span",{style:{background:"rgba(29,78,216,.12)",padding:"0 6px",borderRadius:3,marginRight:6}},"semaine de tour"),
      RE("span",{style:{color:"#ef4444",marginRight:6}},"date rouge = absence"),"F = férié"),
    /* ── Rapport ── */
    /* ── v10.24 : Semaine par semaine ─────────────────────────────────────── */
    RE("div",{style:{fontSize:11,fontWeight:800,color:"var(--txt2)",textTransform:"uppercase",letterSpacing:.4,marginBottom:6}},"Semaine par semaine — ce qu'il y a à faire"),
    (()=>{
      const items=analysis.weekItems;
      const GRPS=[
        {g:"todo",col:"#7c3aed",lbl:(n)=>enLetF(n)+" à traiter"},
        {g:"none",col:"#ef4444",lbl:(n)=>enLetF(n)+" sans solution"},
        {g:"recv",col:"#b45309",lbl:(n)=>enLetF(n)+(n>1?" qui accueillent":" qui accueille")},
        {g:"rien",col:"var(--txt3)",lbl:(n)=>enLetF(n)+" rien à faire"}
      ];
      let nPend=0;
      items.forEach(it=>{if(it.kind==="report")it.lost.forEach(L=>{if(!repTo[lostK(L)])nPend++;});});
      const shown=items.filter(it=>!hidGrp[it.grp]);
      const badge=(txt,bgc,cl)=>RE("span",{style:{fontSize:10,padding:"1px 6px",borderRadius:5,fontWeight:800,background:bgc,color:cl}},txt);
      const pill=(a2)=>a2&&RE("span",{style:{padding:"0 5px",borderRadius:4,fontSize:9,fontWeight:800,fontFamily:"'JetBrains Mono',monospace",background:a2.site==="CHB"?"#b4a7d6":"#c9daf8",color:"#111"}},a2.short);
      const miniBtn=(txt,col,fn)=>RE("button",{onClick:fn,style:{fontSize:10,padding:"1px 7px",borderRadius:5,cursor:"pointer",fontWeight:800,border:"1px solid "+col,background:"transparent",color:col}},txt);
      const ecBadge=(n)=>RE("span",{style:{fontSize:10,fontWeight:800,padding:"1px 6px",borderRadius:5,background:"var(--th)",color:"var(--txt2)",fontFamily:"'JetBrains Mono',monospace"}},ecLbl(n));
      /* pastille « a rouvrir » — collee au libelle, jamais isolee en debut de ligne */
      const tick=(o)=>{
        const inf=doneInfo(o);
        return RE("label",{style:{display:"inline-flex",alignItems:"center",gap:5,fontSize:11,
          cursor:editable?"pointer":"default",border:"1px solid "+(inf?"rgba(22,163,74,.45)":"rgba(245,158,11,.55)"),
          background:inf?"rgba(22,163,74,.09)":"rgba(245,158,11,.10)",borderRadius:11,padding:"1px 9px 1px 6px"}},
          RE("input",{type:"checkbox",checked:!!inf,disabled:!editable,onChange:()=>toggleDone(o),
            style:{width:13,height:13,margin:0,cursor:editable?"pointer":"default"}}),
          RE("span",{style:{fontWeight:800,color:inf?"#16a34a":"#b45309"}},
            inf?("rouvert par "+(inf.by||"?")+(inf.at?" — "+inf.at:"")):"à rouvrir"));
      };
      /* une consultation perdue */
      /* case patients — VIDE par defaut : vide = tout part d'un bloc */
      const patBox=(L,tot)=>RE("span",{style:{display:"inline-flex",alignItems:"center",gap:4,fontSize:10.5,fontWeight:800,
        color:tot===null?"var(--txt3)":"var(--txt2)",background:tot===null?"var(--th)":"rgba(124,58,237,.09)",
        borderRadius:9,padding:"1px 7px"}},
        "👥",
        RE("input",{value:tot===null?"":String(tot),placeholder:"—",readOnly:!editable,
          title:"Laissez vide si toute la consultation part d'un bloc ; un nombre signifie que vous la divisez",
          onChange:e=>setTot(L,e.target.value.replace(/[^0-9]/g,"")),
          style:{width:30,textAlign:"center",fontSize:10.5,fontWeight:800,fontFamily:"inherit",color:"var(--txt)",
            border:"1px solid var(--border)",borderRadius:4,background:"var(--bg2)",padding:"0 2px"}}),
        "patients");
      const jauge=(tot,pl,att,reste)=>{const pc=tot>0?Math.round(100*(pl+att)/tot):0;
        return RE("span",{style:{display:"inline-flex",alignItems:"center",gap:5,fontSize:10.5,fontWeight:800}},
          RE("span",{style:{display:"inline-block",width:74,height:8,borderRadius:4,background:"var(--th)",
            overflow:"hidden",border:"1px solid var(--border2)",verticalAlign:"middle"}},
            RE("span",{style:{display:"block",height:"100%",width:pc+"%",background:reste>0?"#f59e0b":"#16a34a"}})),
          RE("span",{style:{color:reste>0?"#ef4444":"#16a34a"}},
            reste>0?(enLet(reste)+" à placer"):(enLet(pl)+" placé"+(pl>1?"s":""))));};
      const noteInp=(L)=>RE("input",{value:(repOf(L)||{}).n||"",placeholder:"note…",readOnly:!editable,
        onChange:e=>setRepNote2(L,e.target.value),
        style:{fontSize:10,padding:"1px 5px",borderRadius:4,border:"1px solid var(--border)",background:"var(--bg)",color:"var(--txt2)",width:140}});
      const cmtTag=()=>RE("span",{style:{fontSize:10,color:"#16a34a",background:"rgba(22,163,74,.09)",borderRadius:4,padding:"1px 6px"}},"💬 commentaire écrit dans la case");
      const lostLine=(L,k,prop)=>{
        const a2=acteOf(L.acte),ps=partsOf(L),tot=totOf(L),att=attOf(L),reste=resteOf(L);
        const divise=tot!==null,rows=[];
        rows.push(RE("div",{key:"h",style:{display:"flex",alignItems:"center",gap:5,flexWrap:"wrap",padding:"2px 0"}},
          pill(a2),
          RE("span",{style:{fontWeight:(divise||ps.length)?800:700,color:"var(--txt)"}},fmtD(L)+" "+L.sl),
          patBox(L,tot),
          divise&&jauge(tot,placeOf(L),att,reste),
          /* cas simple : rien de pose, la consultation part d'un bloc */
          !divise&&ps.length===0&&prop&&RE("span",{style:{color:"var(--txt3)"}},"→ "+fmtD(prop)+" "+prop.sl+" — la consultation entière"),
          !divise&&ps.length===0&&editable&&prop&&miniBtn("✓ valider","#16a34a",()=>poseBlanche(L,prop)),
          !divise&&ps.length===1&&RE("span",{style:{color:"#16a34a",fontWeight:800}},"→ reporté au "+fmtD(dkParse(ps[0].d))+" "+ps[0].sl),
          !divise&&ps.length===1&&ps[0].salle&&RE("span",{style:{color:"var(--txt3)"}},"salle "+ps[0].salle),
          !divise&&ps.length===1&&cmtTag(),
          !divise&&ps.length===1&&noteInp(L),
          !divise&&ps.length===1&&editable&&miniBtn("annuler le report","var(--txt3)",()=>annulPart(L,0)),
          ps.length===0&&editable&&miniBtn(prop?"autre date":"choisir une date","#7c3aed",()=>{setRepStep(null);setShowG3(false);setRepModal({L});})));
        /* cas divise : une sous-ligne par part */
        if(divise)ps.forEach((q,i)=>{const D=dkParse(q.d);
          rows.push(RE("div",{key:"p"+i,style:{display:"flex",alignItems:"center",gap:5,flexWrap:"wrap",padding:"1px 0 1px 20px"}},
            RE("span",{style:{color:"#16a34a",fontWeight:800}},"✓ "+(q.n===null?"la consultation entière":enLet(q.n))),
            RE("span",{style:{color:"var(--txt2)"}},"→ "+fmtD(D)+" "+q.sl),
            q.cree&&badge("créée","rgba(29,78,216,.12)","#1d4ed8"),
            q.salle&&RE("span",{style:{color:"var(--txt3)"}},"salle "+q.salle),
            cmtTag(),
            editable&&miniBtn("annuler le report","var(--txt3)",()=>annulPart(L,i))));});
        if(divise&&reste>0)rows.push(RE("div",{key:"al",style:{display:"flex",alignItems:"center",gap:6,flexWrap:"wrap",
          fontSize:11,fontWeight:800,color:"#ef4444",background:"rgba(239,68,68,.08)",
          border:"1px solid rgba(239,68,68,.35)",borderRadius:6,padding:"4px 8px",marginTop:4}},
          "⚠ ",RE("b",null,cap1(enLet(reste))+" patient"+(reste>1?"s":"")+(reste>1?" ne sont pas replacés.":" n'est pas replacé.")),
          editable&&miniBtn("placer le reste","#7c3aed",()=>{setRepStep(null);setShowG3(false);setRepModal({L});}),
          editable&&miniBtn("↪ en liste d'attente","#b45309",()=>setAtt(L,att+reste))));
        if(att>0)rows.push(RE("div",{key:"at",style:{display:"flex",alignItems:"center",gap:6,flexWrap:"wrap",
          fontSize:11,fontWeight:800,color:"#b45309",background:"rgba(245,158,11,.10)",
          border:"1px solid rgba(245,158,11,.45)",borderRadius:6,padding:"4px 8px",marginTop:4}},
          "↪ ",RE("b",null,cap1(enLet(att))+" en liste d'attente"),
          RE("span",{style:{color:"var(--txt3)",fontWeight:400}},"— replacés hors période ou ventilés par le secrétariat"),
          editable&&miniBtn("reprendre","var(--txt3)",()=>setAtt(L,0))));
        if(divise&&ps.length===0&&reste===tot)rows.push(RE("div",{key:"ai",style:{fontSize:10.5,color:"var(--txt3)",fontStyle:"italic",paddingLeft:20}},
          "Videz la case pour reporter la consultation entière d'un seul bloc."));
        return RE("div",{key:k,style:{padding:"1px 0"}},rows);
      };
      /* une demi-journee blanche : que recoit-elle ? */
      const recvLine=(o,k)=>{
        const kk=dk3(o.y,o.m,o.d)+"|"+o.sl,V=validAt[kk],P2=propAt[kk];
        return RE("div",{key:k,style:{display:"flex",alignItems:"center",gap:5,flexWrap:"wrap",padding:"2px 0"}},
          pill(acteOf(o.acte)),
          RE("span",{style:{color:"var(--txt2)",fontWeight:700}},fmtD(o)+" "+o.sl),
          V&&RE("span",{style:{color:"#16a34a",fontWeight:800}},"← reçoit "+fmtD(V)+" "+V.sl),
          !V&&P2&&RE("span",{style:{color:"var(--txt3)"}},"← proposé pour "+fmtD(P2)+" "+P2.sl),
          !V&&!P2&&RE("span",{style:{color:"var(--txt3)"}},"— aucun report dessus"),
          !V&&!P2&&tick(o));
      };
      return RE("div",null,
        /* pastilles de filtre */
        RE("div",{style:{display:"flex",gap:8,flexWrap:"wrap",marginBottom:7}},
          GRPS.map(G=>{const n=items.filter(it=>it.grp===G.g).length;if(!n)return null;
            const off=!!hidGrp[G.g];
            return RE("span",{key:G.g,onClick:()=>setHidGrp(h=>Object.assign({},h,{[G.g]:!h[G.g]})),
              title:off?"Afficher ces semaines":"Masquer ces semaines",
              style:{fontSize:11.5,fontWeight:800,padding:"3px 10px",borderRadius:11,cursor:"pointer",userSelect:"none",
                border:"1px solid "+G.col,color:G.col,background:"var(--bg2)",opacity:off?.4:1,
                textDecoration:off?"line-through":"none"}},G.lbl(n));})),
        nPend>0&&RE("div",{style:{fontSize:11.5,color:"#b45309",background:"rgba(245,158,11,.10)",border:"1px solid rgba(245,158,11,.45)",
          borderRadius:7,padding:"6px 10px",marginBottom:10,lineHeight:1.5}},
          "⏳ ",RE("b",null,cap1(enLet(nPend))+" report"+(nPend>1?"s":"")+" encore à valider."),
          " Les demi-journées à rouvrir n'apparaîtront toutes qu'une fois ces reports traités — d'ici là, cette liste n'est pas définitive."),
        shown.length===0
          ?RE("div",{style:{fontSize:12,color:"var(--txt3)",fontWeight:700,marginBottom:10}},"Tout est masqué — touchez une pastille pour réafficher.")
          :RE("div",{style:{border:"1px solid var(--border)",borderRadius:8,overflow:"hidden",marginBottom:12}},
            shown.map((it,i)=>{
              const f=it.days[0];
              const bar={report:"#7c3aed",norep:"#ef4444",recv:"#16a34a",ok:"#16a34a",rien:"transparent"}[it.kind];
              /* blanche entiere ou partielle ? */
              let nHab=0;
              if(it.kind==="recv")it.days.forEach(o=>{const dw=new Date(o.y,o.m,o.d).getDay();
                if(isFerie(o.y,o.m,o.d))return;["M","AM"].forEach(sl=>{if(habCS[dw]&&habCS[dw][sl])nHab++;});});
              let nV=0,nP=0;
              if(it.kind==="recv")it.dates.forEach(o=>{const kk=dk3(o.y,o.m,o.d)+"|"+o.sl;
                if(validAt[kk])nV++;else if(propAt[kk])nP++;});
              const recvTxt=[];
              if(nV)recvTxt.push({t:"reçoit "+enLet(nV)+" report"+(nV>1?"s":""),c:"#16a34a"});
              if(nP)recvTxt.push({t:"peut accueillir "+enLet(nP)+" report"+(nP>1?"s":""),c:"var(--txt2)"});
              if(!nV&&!nP)recvTxt.push({t:"libre — rien ne s'y reporte pour l'instant",c:"#b45309"});
              /* le bouton de rattrapage manuel, a DROITE du texte rouge */
              /* v10.25 : le bouton n'applique plus rien tout seul — il OUVRE le choix. */
              const nInc=(it.lost||[]).filter(L=>incomplet(L)).length;
              return RE("div",{key:it.wk,style:{padding:"7px 10px 8px 13px",borderTop:i>0?"1px solid var(--border2)":"none",
                fontSize:12,position:"relative",borderLeft:"3px solid "+bar,
                background:it.kind==="rien"?"rgba(127,127,127,.045)":"transparent"}},
                RE("div",{style:{display:"flex",alignItems:"center",gap:7,flexWrap:"wrap"}},
                  RE("span",{style:{fontWeight:800,color:it.kind==="rien"?"var(--txt3)":"var(--txt)"}},"Semaine du "+f.d+" "+MOIS[f.m].slice(0,4)),
                  it.kind==="ok"&&badge("tour","rgba(29,78,216,.12)","#1d4ed8"),
                  (it.kind==="report"||it.kind==="norep")&&badge(it.why,it.why==="tour"?"rgba(29,78,216,.12)":"rgba(239,68,68,.12)",it.why==="tour"?"#1d4ed8":"#ef4444"),
                  nInc>0&&badge("⚠ report incomplet","#ef4444","#fff"),
                  it.kind==="recv"&&badge(it.dates.length>=nHab?"blanche":"blanche partielle","rgba(245,158,11,.2)","#b45309"),
                  RE("span",{style:{color:"var(--txt3)"}},"→"),
                  it.kind==="report"&&RE("span",{style:{fontWeight:800,color:"var(--txt2)"}},
                    "semaine blanche libre la plus proche : "+it.to.days[0].d+" "+MOIS[it.to.days[0].m].slice(0,4)),
                  it.kind==="report"&&ecBadge(it.ec),
                  it.kind==="norep"&&RE("span",{style:{color:"#ef4444",fontWeight:800}},"aucune semaine blanche à moins d'un mois"),
                  it.kind==="norep"&&editable&&RE("button",{onClick:()=>setWeekModal({it}),
                    style:{fontSize:11,padding:"3px 9px",borderRadius:6,cursor:"pointer",fontWeight:800,
                      border:"1.5px solid #7c3aed",background:"rgba(124,58,237,.10)",color:"#7c3aed"}},"⇄ Chercher une autre semaine blanche"),
                  it.kind==="ok"&&RE("span",{style:{fontWeight:800,color:"#16a34a"}},"✓ semaine blanche — pas de report nécessaire"),
                  it.kind==="rien"&&RE("span",{style:{fontWeight:700,color:"var(--txt3)"}},"rien à faire"),
                  it.kind==="recv"&&recvTxt.map((R,k2)=>RE("span",{key:k2,style:{fontWeight:800,color:R.c}},(k2?" · ":"")+R.t))),
                (it.kind==="report"||it.kind==="norep")&&RE("div",{style:{fontSize:11,color:"var(--txt2)",lineHeight:1.7,marginTop:3}},
                  it.lost.map((L,k)=>lostLine(L,k,it.dest?it.dest[k]:null))),
                it.kind==="recv"&&RE("div",{style:{fontSize:11,color:"var(--txt2)",lineHeight:1.7,marginTop:3}},
                  it.dates.map((o,k)=>recvLine(o,k))));
            })));
    })(),
    RE("div",{style:{fontSize:11,fontWeight:800,color:"var(--txt2)",textTransform:"uppercase",letterSpacing:.4,marginBottom:3}},"Demi-journées off par semaine"),
    RE("div",{style:{fontSize:11,color:"var(--txt3)",marginBottom:5,lineHeight:1.5}},
      "Demi-journées libres, hors semaines de tour : de quoi OUVRIR une consultation, une fois tous vos reports traités."),
    analysis.offWeeks.length===0
      ?RE("div",{style:{fontSize:12,color:"var(--txt3)",fontWeight:700,marginBottom:10}},"Aucune demi-journée off sur la période.")
      :RE("div",{style:{overflowX:"auto",border:"1px solid var(--border)",borderRadius:8,marginBottom:6}},
        RE("table",{style:{borderCollapse:"collapse",width:"100%"}},
          RE("thead",null,RE("tr",null,
            RE("th",{style:{padding:"4px 8px",fontSize:10,color:"var(--txt3)",textAlign:"left",background:"var(--th)"}},"Semaine"),
            ["Lun","Mar","Mer","Jeu","Ven"].map(j=>RE("th",{key:j,style:{padding:"4px 6px",fontSize:10,color:"var(--txt3)",background:"var(--th)"}},j)))),
          RE("tbody",null,analysis.offWeeks.map(w=>{
            const f=w.days[0];
            return RE("tr",{key:w.key,style:{borderTop:"1px solid var(--border2)"}},
              RE("td",{style:{padding:"3px 8px",fontSize:11,fontWeight:700,color:"var(--txt)",whiteSpace:"nowrap"}},f.d+" "+MOIS[f.m].slice(0,4)),
                    [1,2,3,4,5].map(dw=>{
                      const sls=w.slots[dw]||[];
                      const o=dayOf(w,dw);
                      /* v10.49, sa règle : trois états PAR DEMI-JOURNÉE. Vide = pas
                         de off ; vert = off avec au moins une salle participante
                         libre (cliquable) ; hachuré gris = off mais aucune salle
                         libre — inutile d'ouvrir la fenêtre pour le savoir. */
                      return RE("td",{key:dw,
                        style:{padding:"3px 2px",textAlign:"center",border:"1px solid var(--border2)",
                          background:(sls.length&&habDW.indexOf(dw)>=0)?"rgba(124,58,237,.06)":"transparent"}},
                        o?sls.map(s2=>{
                          const ok=hasFreeRoom(o.y,o.m,o.d,s2);
                          return RE("span",{key:s2,
                            onClick:(ok&&editable)?()=>{setFreeStep(null);setFreeModal({y:o.y,m:o.m,d:o.d,sl:s2,slots:[s2]});}:undefined,
                            title:ok?undefined:"off, mais aucune salle libre ce créneau",
                            style:{display:"inline-block",minWidth:22,margin:"1px 2px",padding:"1px 5px",borderRadius:5,fontSize:10,fontWeight:800,
                              cursor:(ok&&editable)?"pointer":"default",
                              border:ok?"1.5px solid #2da44e":"1.5px dashed #b6bec7",
                              background:ok?"rgba(22,163,74,.16)":"repeating-linear-gradient(45deg,rgba(140,150,160,.18),rgba(140,150,160,.18) 3px,transparent 3px,transparent 6px)",
                              color:ok?"#16a34a":"var(--txt3)"}},s2);
                        }):null);
                    }));
          })))),
              analysis.offWeeks.length>0&&RE("div",{style:{fontSize:10.5,color:"var(--txt3)",marginBottom:10,display:"flex",alignItems:"center",gap:5,flexWrap:"wrap"}},
                RE("span",{style:{display:"inline-block",width:24,height:12,borderRadius:5,border:"1px solid var(--border)",background:"var(--bg2)"}}),"pas de off",
                RE("span",null,"·"),
                RE("span",{style:{display:"inline-block",width:24,height:12,borderRadius:5,border:"1.5px solid #2da44e",background:"rgba(22,163,74,.16)"}}),"off avec au moins une salle disponible"+(editable?" — cliquez pour ouvrir":""),
                RE("span",null,"·"),
                RE("span",{style:{display:"inline-block",width:24,height:12,borderRadius:5,border:"1.5px dashed #b6bec7",background:"repeating-linear-gradient(45deg,rgba(140,150,160,.18),rgba(140,150,160,.18) 3px,transparent 3px,transparent 6px)"}}),"off mais pas de salle"),
    analysis.weekPairs.length>0&&RE("button",{onClick:exportCSVR,style:{fontSize:12,padding:"5px 12px",borderRadius:6,border:"1.5px solid #16a34a",background:"rgba(22,163,74,.10)",color:"#16a34a",fontWeight:800,cursor:"pointer"}},"⬇ Export CSV des propositions"),
    /* ── v10.25 : modale de report a TROIS groupes ────────────────────────────
       1. semaines blanches, meme jour de semaine — reprennent tout d'un coup
       2. creneaux de tour — APRES-MIDI seulement (« on ne consulte jamais le matin
          en semaine de tour »), sur ses jours habituels, la ou seul le tour est pose
       3. autres jours de la semaine — REPLIE par defaut
       Les groupes 2 et 3 CREENT la consultation dans le planning : salle demandee. */
    repModal&&(()=>{
      const L=repModal.L,dwL=new Date(L.y,L.m,L.d).getDay(),src=new Date(L.y,L.m,L.d);
      const tot=totOf(L),reste=resteOf(L);
      const g1=[],g2=[],g3=[];
      days.forEach(x=>{
        const dw=new Date(x.y,x.m,x.d).getDay();
        if(dw===0||dw===6||isFerie(x.y,x.m,x.d))return;
        if(x.y===L.y&&x.m===L.m&&x.d===L.d)return;
        const tour=inTour(x.y,x.m,x.d),blanche=isBl(x.y,x.m,x.d);
        const ec=Math.round((new Date(x.y,x.m,x.d)-src)/86400000);
        ["M","AM"].forEach(sl=>{
          const kk=dk3(x.y,x.m,x.d)+"|"+sl;
          const hab=habCS[dw]&&habCS[dw][sl];
          if(!tour&&blanche&&dw===dwL&&hab)
            g1.push({o:x,sl,ec,libre:slotFreeCS(x.y,x.m,x.d,sl),val:validAt[kk]||null,prop:propAt[kk]||null});
          else if(tour&&sl==="AM"&&habDW.indexOf(dw)>=0&&seulLeTour(x.y,x.m,x.d,sl))
            g2.push({o:x,sl,ec,salles:sallesLibres(L,x,sl)});
          else if(!tour&&habDW.indexOf(dw)<0&&slotState(x.y,x.m,x.d,sl)==="free")
            g3.push({o:x,sl,ec,salles:sallesLibres(L,x,sl)});
        });
      });
      const parEc=(A,B)=>Math.abs(A.ec)-Math.abs(B.ec);
      g1.sort(parEc);g2.sort(parEc);g3.sort(parEc);
      const tagS=(bgc,cl,dash)=>({fontSize:8.5,fontWeight:800,padding:"1px 6px",borderRadius:9,background:bgc,color:cl,
        border:dash?"1px dashed var(--border)":"none"});
      const tag=(txt,bgc,cl,dash)=>RE("span",{style:tagS(bgc,cl,dash)},txt);
      const grpT=(txt)=>RE("div",{style:{fontSize:9.5,fontWeight:800,textTransform:"uppercase",letterSpacing:.4,
        color:"var(--txt3)",margin:"11px 0 5px",borderTop:"1px solid var(--border2)",paddingTop:9}},txt);
      const ligne=(cle,contenu,style2,ko,fn)=>RE("button",{key:cle,disabled:ko,onClick:ko?undefined:fn,
        style:Object.assign({display:"flex",alignItems:"center",gap:8,width:"100%",textAlign:"left",padding:"6px 9px",
          borderRadius:8,marginBottom:5,fontFamily:"inherit",cursor:ko?"not-allowed":"pointer",opacity:ko?.8:1},style2)},contenu);
      const dJour=(C,violet)=>RE("span",{style:{fontSize:11.5,fontWeight:800,color:"var(--txt)",minWidth:104}},
        violet?RE("span",{style:{display:"inline-block",width:30,color:"#7c3aed",fontWeight:800}},JR[new Date(C.o.y,C.o.m,C.o.d).getDay()]):null,
        (violet?"":"")+ (violet?(C.o.d+" "+MOIS[C.o.m].slice(0,4)):fmtD(C.o))+" "+C.sl);
      const metas=(kids)=>RE("span",{style:{fontSize:9,display:"flex",gap:4,flexWrap:"wrap",alignItems:"center",
        marginLeft:"auto",justifyContent:"flex-end"}},kids);
      const ouvrir=(C)=>{setRepStep({L,o:C.o,sl:C.sl,salles:C.salles,tot:"",nb:"",salle:(C.salles&&C.salles.length===1)?C.salles[0]:null});};
      return RE("div",{onClick:()=>{setRepModal(null);setRepStep(null);},
        style:{position:"fixed",top:0,left:0,right:0,bottom:0,background:"rgba(0,0,0,.55)",zIndex:900,display:"flex",alignItems:"center",justifyContent:"center",padding:12}},
        RE("div",{onClick:e=>e.stopPropagation(),style:{background:"var(--bg2)",border:"1px solid var(--border)",borderRadius:12,padding:14,width:"100%",maxWidth:460,maxHeight:"85vh",overflowY:"auto"}},
          RE("div",{style:{fontWeight:800,fontSize:13,color:"var(--txt)",marginBottom:3}},"⇄ Reporter "+fmtD(L)+" "+L.sl),
          RE("div",{style:{fontSize:10,color:"var(--txt3)",marginBottom:9,lineHeight:1.5}},
            tot===null
              ?"Une semaine blanche reprend la consultation entière. Un créneau de tour n'en reprend qu'une part, et vous demandera alors le total."
              :RE("span",null,"Il reste ",RE("b",null,enLet(reste)+" patient"+(reste>1?"s":""))," à replacer sur les "+enLet(tot)+".")),
          /* ── 1 ── */
          g1.length>0&&grpT(tot===null?"Semaines blanches — reprennent la consultation entière":"Semaines blanches — reprennent tout ce qui reste"),
          g1.map((C,k)=>{const ko=!C.libre||!!C.val;
            return ligne("a"+k,[
              RE("span",{key:"d",style:{fontSize:11.5,fontWeight:800,color:"var(--txt)",minWidth:104}},fmtD(C.o)+" "+C.sl),
              metas([tag(ecLbl(C.ec),"var(--th)","var(--txt2)"),
                tag("semaine blanche","rgba(245,158,11,.2)","#b45309"),
                C.val?tag("✓ validée — "+fmtD(C.val)+" "+C.val.sl,"rgba(239,68,68,.10)","#ef4444")
                  :(!C.libre?tag("occupée","rgba(239,68,68,.10)","#ef4444")
                    :(C.prop?tag("proposée — "+fmtD(C.prop)+" "+C.prop.sl,"var(--th)","var(--txt2)",true)
                      :tag("libre","rgba(22,163,74,.14)","#16a34a")))])],
              {border:"1.5px "+(C.prop?"dashed":"solid")+" "+(ko?"rgba(239,68,68,.45)":"#16a34a"),
               background:ko?"rgba(239,68,68,.04)":"rgba(22,163,74,.07)"},ko,
              ()=>{poseBlanche(L,{y:C.o.y,m:C.o.m,d:C.o.d,sl:C.sl});setRepModal(null);});}),
          /* ── 2 ── */
          g2.length>0&&grpT("Créneaux pendant vos tours — vous choisissez le nombre"),
          g2.map((C,k)=>{const ko=C.salles!==null&&C.salles.length===0;
            return ligne("b"+k,[
              RE("span",{key:"d",style:{fontSize:11.5,fontWeight:800,color:"var(--txt)",minWidth:104}},fmtD(C.o)+" "+C.sl),
              metas([tag(ecLbl(C.ec),"var(--th)","var(--txt2)"),
                tag("tour · rien d'autre posé","rgba(29,78,216,.14)","#1d4ed8"),
                C.salles===null?tag("sans salle","var(--th)","var(--txt2)",true)
                  :(ko?tag("aucune salle libre","rgba(239,68,68,.10)","#ef4444")
                    :tag(enLet(C.salles.length)+(C.salles.length>1?" salles libres":" salle libre"),"rgba(22,163,74,.14)","#16a34a"))])],
              {border:"1.5px solid "+(ko?"rgba(239,68,68,.45)":"#1d4ed8"),background:ko?"rgba(239,68,68,.04)":"rgba(29,78,216,.05)"},
              ko,()=>ouvrir(C));}),
          /* ── 3, replie ── */
          g3.length>0&&RE("button",{onClick:()=>setShowG3(s=>!s),
            style:{display:"flex",alignItems:"center",gap:7,width:"100%",textAlign:"left",padding:"7px 9px",borderRadius:8,
              border:"1.5px dashed #7c3aed",background:"rgba(124,58,237,.06)",color:"#7c3aed",cursor:"pointer",
              fontFamily:"inherit",fontSize:10.5,fontWeight:800,marginTop:11}},
            (showG3?"▾ Masquer les autres jours de la semaine":"▸ Aucun "+JR[dwL]+" ne convient ? Chercher un autre jour de la semaine"),
            RE("span",{style:{marginLeft:"auto",fontWeight:800,fontSize:9,background:"rgba(124,58,237,.14)",borderRadius:9,padding:"1px 7px"}},String(g3.length))),
          g3.length>0&&showG3&&RE("div",null,
            grpT("Autres jours — demi-journées libres, hors semaines de tour"),
            g3.map((C,k)=>{const ko=C.salles!==null&&C.salles.length===0;
              return ligne("c"+k,[
                RE("span",{key:"d",style:{fontSize:11.5,fontWeight:800,color:"var(--txt)",minWidth:104}},
                  RE("span",{style:{display:"inline-block",width:30,color:"#7c3aed"}},JR[new Date(C.o.y,C.o.m,C.o.d).getDay()]),
                  C.o.d+" "+MOIS[C.o.m].slice(0,4)+" "+C.sl),
                metas([tag(ecLbl(C.ec),"var(--th)","var(--txt2)"),
                  C.salles===null?tag("sans salle","var(--th)","var(--txt2)",true)
                    :(ko?tag("aucune salle libre","rgba(239,68,68,.10)","#ef4444")
                      :tag(enLet(C.salles.length)+(C.salles.length>1?" salles libres":" salle libre"),"rgba(22,163,74,.14)","#16a34a"))])],
                {border:"1.5px solid "+(ko?"rgba(239,68,68,.45)":"#7c3aed"),background:ko?"rgba(239,68,68,.04)":"rgba(124,58,237,.05)"},
                ko,()=>ouvrir(C));}),
            RE("div",{style:{fontSize:9.5,color:"var(--txt3)",lineHeight:1.6,marginTop:6}},
              "Un autre jour crée la consultation dans le planning, comme un créneau de tour : la salle vous sera demandée. Le repère « semaine blanche » ne s'y applique pas — il signifie que votre secrétaire a vidé votre consultation, ce qui n'a pas de sens un jour où vous n'en tenez jamais.")),
          (g1.length+g2.length+g3.length)===0&&RE("div",{style:{fontSize:11,color:"#ef4444",fontWeight:700}},"Aucune destination possible sur la période."),
          RE("div",{style:{fontSize:9.5,color:"var(--txt3)",lineHeight:1.6,marginTop:10,borderTop:"1px solid var(--border2)",paddingTop:8}},
            "Hors période affichée, rien n'est proposé : ces reports-là se règlent directement avec le secrétariat."),
          RE("button",{onClick:()=>{setRepModal(null);setRepStep(null);},style:{marginTop:10,fontSize:11,padding:"4px 10px",borderRadius:6,border:"1px solid var(--border)",background:"var(--bg)",color:"var(--txt2)",cursor:"pointer",fontWeight:700}},"Fermer")));
    })(),
    /* ── v10.25 : 2e temps — combien de patients, et dans quelle salle ────────── */
    repStep&&(()=>{
      const L=repStep.L,tot=totOf(L),besoinTot=(tot===null);
      const dest={y:repStep.o.y,m:repStep.o.m,d:repStep.o.d,sl:repStep.sl};
      const salles=repStep.salles;
      const num=(v)=>{const q=parseInt(v,10);return isNaN(q)?0:q;};
      const champ=(lbl,val,fn,gros)=>RE("div",{style:{display:"flex",alignItems:"center",gap:8,marginBottom:9,flexWrap:"wrap",
        background:gros?"rgba(124,58,237,.07)":"transparent",border:gros?"1px solid rgba(124,58,237,.3)":"none",
        borderRadius:gros?8:0,padding:gros?"8px 10px":0}},
        RE("label",{style:{fontSize:11,fontWeight:700,color:"var(--txt)"}},lbl),
        RE("input",{value:val,placeholder:"—",onChange:e=>fn(e.target.value.replace(/[^0-9]/g,"")),
          style:{width:56,padding:"4px 6px",borderRadius:6,border:"1px solid var(--border)",background:"var(--bg2)",
            color:"var(--txt)",fontSize:13,fontWeight:800,textAlign:"center",fontFamily:"inherit"}}));
      const valider=()=>{
        const t=besoinTot?num(repStep.tot):tot;
        const nb=num(repStep.nb);
        if(besoinTot&&t<=0){if(toast)toast("Indiquez d'abord le nombre total de patients de la consultation","warn");return;}
        if(nb<=0){if(toast)toast("Indiquez le nombre de patients repris ce jour-là","warn");return;}
        if(nb>t){if(toast)toast("Vous reprenez plus de patients que n'en comptait la consultation","warn");return;}
        if(salles!==null&&salles.length>0&&!repStep.salle){if(toast)toast("Choisissez une salle","warn");return;}
        if(besoinTot)setTot(L,t);
        poseCree(L,dest,nb,repStep.salle);
        setRepStep(null);setRepModal(null);
      };
      return RE("div",{onClick:()=>setRepStep(null),
        style:{position:"fixed",top:0,left:0,right:0,bottom:0,background:"rgba(0,0,0,.6)",zIndex:950,display:"flex",alignItems:"center",justifyContent:"center",padding:12}},
        RE("div",{onClick:e=>e.stopPropagation(),style:{background:"var(--bg2)",border:"1px solid var(--border)",borderRadius:12,padding:14,width:"100%",maxWidth:450,maxHeight:"85vh",overflowY:"auto"}},
          RE("div",{style:{fontWeight:800,fontSize:13,color:"var(--txt)",marginBottom:3}},"➕ Consultation — "+fmtD(repStep.o)+" "+repStep.sl),
          RE("div",{style:{fontSize:10,color:"var(--txt3)",marginBottom:9,lineHeight:1.5}},
            (inTour(repStep.o.y,repStep.o.m,repStep.o.d)
              ?"Vous êtes en tour cette semaine-là : la consultation sera créée dans le planning, à côté du tour."
              :"Ce jour n'est pas un de vos jours de consultation : elle sera créée dans le planning.")
            +(besoinTot?" Comme vous n'en reprenez qu'une partie, il me faut d'abord savoir sur combien.":"")),
          besoinTot&&champ("Patients sur la consultation du "+fmtD(L)+" "+L.sl,repStep.tot,v=>setRepStep(s=>Object.assign({},s,{tot:v})),true),
          champ("Patients repris ce jour-là",repStep.nb,v=>setRepStep(s=>Object.assign({},s,{nb:v})),false),
          !besoinTot&&RE("div",{style:{fontSize:10,color:"var(--txt3)",marginTop:-4,marginBottom:9}},"sur les "+enLet(resteOf(L))+" restants"),
          salles!==null&&salles.length>0&&RE("div",{style:{marginBottom:9}},
            RE("label",{style:{display:"block",fontSize:11,fontWeight:700,color:"var(--txt)",marginBottom:5}},"Salle"),
            RE("div",null,salles.map(s=>RE("button",{key:s,onClick:()=>setRepStep(st=>Object.assign({},st,{salle:s})),
              style:{fontSize:11,padding:"5px 11px",borderRadius:8,cursor:"pointer",fontWeight:800,fontFamily:"inherit",margin:"0 5px 5px 0",
                border:"1.5px solid "+(repStep.salle===s?"#16a34a":"var(--border)"),
                background:repStep.salle===s?"rgba(22,163,74,.10)":"var(--bg)",
                color:repStep.salle===s?"#16a34a":"var(--txt2)"}},s)))),
          salles===null&&RE("div",{style:{fontSize:10,color:"var(--txt3)",marginBottom:9}},"Cette activité ne demande pas de salle."),
          besoinTot&&RE("div",{style:{fontSize:9.5,color:"var(--txt3)",lineHeight:1.6,marginBottom:9}},
            "Le premier nombre remplit la case patients de la ligne et ouvre la jauge : la ligne saura dès lors ce qui reste. Il ne vous sera plus demandé ensuite."),
          RE("div",null,
            RE("button",{onClick:valider,style:{fontSize:12,padding:"6px 14px",borderRadius:8,cursor:"pointer",fontWeight:800,border:"none",background:"#16a34a",color:"#fff",fontFamily:"inherit"}},"✓ Créer la consultation"),
            RE("button",{onClick:()=>setRepStep(null),style:{marginLeft:6,fontSize:11,padding:"5px 10px",borderRadius:6,border:"1px solid var(--border)",background:"var(--bg)",color:"var(--txt2)",cursor:"pointer",fontWeight:700,fontFamily:"inherit"}},"Annuler"))));
    })(),
    /* ── v10.25 : le bouton violet ouvre le choix des semaines, il ne decide plus ── */
    weekModal&&(()=>{
      const it=weekModal.it,src=new Date(it.lost[0].y,it.lost[0].m,it.lost[0].d);
      const cands=weeks.filter(w=>w.key!==it.wk&&it.lost.every(L=>{
          const o=w.days.find(x=>new Date(x.y,x.m,x.d).getDay()===L.dw);
          return o&&isBl(o.y,o.m,o.d)&&!isFerie(o.y,o.m,o.d)&&slotFreeCS(o.y,o.m,o.d,L.sl);}))
        .map(w=>{const o0=w.days.find(x=>new Date(x.y,x.m,x.d).getDay()===it.lost[0].dw);
          return {w,ec:Math.round((new Date(o0.y,o0.m,o0.d)-src)/86400000)};})
        .sort((A,B)=>Math.abs(A.ec)-Math.abs(B.ec));
      const poser=(w)=>{it.lost.forEach(L=>{const o=w.days.find(x=>new Date(x.y,x.m,x.d).getDay()===L.dw);
          if(o)poseBlanche(L,{y:o.y,m:o.m,d:o.d,sl:L.sl});});
        setWeekModal(null);
        if(toast)toast("Reporté sur la semaine du "+w.days[0].d+" "+MOIS[w.days[0].m].slice(0,4));};
      return RE("div",{onClick:()=>setWeekModal(null),
        style:{position:"fixed",top:0,left:0,right:0,bottom:0,background:"rgba(0,0,0,.55)",zIndex:900,display:"flex",alignItems:"center",justifyContent:"center",padding:12}},
        RE("div",{onClick:e=>e.stopPropagation(),style:{background:"var(--bg2)",border:"1px solid var(--border)",borderRadius:12,padding:14,width:"100%",maxWidth:450,maxHeight:"85vh",overflowY:"auto"}},
          RE("div",{style:{fontWeight:800,fontSize:13,color:"var(--txt)",marginBottom:3}},"⇄ Reporter la semaine du "+it.days[0].d+" "+MOIS[it.days[0].m].slice(0,4)),
          RE("div",{style:{fontSize:10,color:"var(--txt3)",marginBottom:9,lineHeight:1.5}},
            "Semaines blanches où "+(it.lost.length>1?("les "+enLet(it.lost.length)+" demi-journées tiennent"):"la demi-journée tient")
            +". La limite d'un mois ne s'applique pas ici : c'est le rattrapage manuel, à vous de juger l'écart."),
          cands.length===0
            ?RE("div",{style:{fontSize:11,color:"#ef4444",fontWeight:700}},"Aucune semaine blanche ne peut reprendre la semaine entière. Reportez alors chaque consultation séparément, avec « choisir une date ».")
            :RE("div",null,cands.map((C,k)=>RE("button",{key:k,onClick:()=>poser(C.w),
              style:{display:"flex",alignItems:"center",gap:8,width:"100%",textAlign:"left",padding:"6px 9px",borderRadius:8,
                marginBottom:5,fontFamily:"inherit",cursor:"pointer",border:"1.5px solid #16a34a",background:"rgba(22,163,74,.07)"}},
              RE("span",{style:{fontSize:11.5,fontWeight:800,color:"var(--txt)",minWidth:120}},"Semaine du "+C.w.days[0].d+" "+MOIS[C.w.days[0].m].slice(0,4)),
              RE("span",{style:{fontSize:9,display:"flex",gap:4,alignItems:"center",marginLeft:"auto"}},
                RE("span",{style:{fontSize:8.5,fontWeight:800,padding:"1px 6px",borderRadius:9,background:"var(--th)",color:"var(--txt2)",fontFamily:"'JetBrains Mono',monospace"}},ecLbl(C.ec)),
                RE("span",{style:{fontSize:8.5,fontWeight:800,padding:"1px 6px",borderRadius:9,background:"rgba(245,158,11,.2)",color:"#b45309"}},"semaine blanche"))))),
          RE("button",{onClick:()=>setWeekModal(null),style:{marginTop:10,fontSize:11,padding:"4px 10px",borderRadius:6,border:"1px solid var(--border)",background:"var(--bg)",color:"var(--txt2)",cursor:"pointer",fontWeight:700}},"Fermer")));
    })(),
    freeModal&&RE("div",{onClick:()=>{setFreeModal(null);setFreeStep(null);},
      style:{position:"fixed",top:0,left:0,right:0,bottom:0,background:"rgba(0,0,0,.55)",zIndex:900,display:"flex",alignItems:"center",justifyContent:"center",padding:12}},
      RE("div",{onClick:e=>e.stopPropagation(),style:{background:"var(--bg2)",border:"1px solid var(--border)",borderRadius:12,padding:14,width:"100%",maxWidth:430,maxHeight:"82vh",overflowY:"auto"}},
        RE("div",{style:{display:"flex",alignItems:"center",gap:8,marginBottom:8}},
          RE("div",{style:{fontWeight:800,fontSize:13,color:"var(--txt)"}},"🟢 "+fmtD(freeModal)+" "+(SLOTL[freeModal.sl]||freeModal.sl)),
          RE("button",{onClick:()=>{setFreeModal(null);setFreeStep(null);},style:{marginLeft:"auto",background:"none",border:"none",color:"var(--txt2)",fontSize:20,cursor:"pointer",lineHeight:1}},"×")),
        (freeModal.slots||[]).length>1&&RE("div",{style:{display:"flex",gap:5,marginBottom:9}},
          (freeModal.slots||[]).map(s2=>RE("button",{key:s2,onClick:()=>{setFreeStep(null);setFreeModal(f=>({...f,sl:s2}));},
            style:{fontSize:11,padding:"3px 11px",borderRadius:11,cursor:"pointer",fontWeight:800,
              border:freeModal.sl===s2?"1.5px solid #16a34a":"1px solid var(--border)",
              background:freeModal.sl===s2?"rgba(22,163,74,.12)":"var(--bg)",color:freeModal.sl===s2?"#16a34a":"var(--txt3)"}},SLOTL[s2]||s2))),
        (()=>{
          const occ=occSalles(freeModal.y,freeModal.m,freeModal.d,freeModal.sl);
          if(freeStep){
            const fs=freeFor(freeStep.a,occ);
            return RE("div",null,
              RE("div",{style:{fontSize:11,color:"var(--txt2)",marginBottom:6}},"Salle pour ",RE("b",null,freeStep.a.label)," :"),
              RE("div",{style:{display:"flex",flexWrap:"wrap",gap:5}},
                fs.map(s=>RE("button",{key:s,onClick:()=>poseFree(freeStep.a,s,freeStep.lost),
                  style:{fontSize:12,padding:"6px 12px",borderRadius:8,cursor:"pointer",fontWeight:800,border:"1.5px solid #16a34a",background:"rgba(22,163,74,.10)",color:"#16a34a"}},s))),
              RE("button",{onClick:()=>setFreeStep(null),style:{marginTop:9,fontSize:11,padding:"4px 10px",borderRadius:6,border:"1px solid var(--border)",background:"var(--bg)",color:"var(--txt2)",cursor:"pointer",fontWeight:700}},"‹ Retour"));
          }
              const pinned=[];
              analysis.weekPairs.forEach(wp=>{if(!wp.to)wp.lost.forEach(L=>{
                const a=myActesAll.find(x=>x.id===L.acte);
                if(a&&freeFor(a,occ).length>0)pinned.push({a,lost:L});
              });});
              /* v10.49 : seules les activités pouvant se dérouler dans une salle
                 participante sont proposées ; sans salle libre ce créneau elles
                 restent visibles mais grisées, avec la raison. Le groupe « Sans
                 salle » (FMC…) disparaît : sans salle, rien à ouvrir sur un off. */
              const withRoom=myActesOff.filter(a=>freeFor(a,occ).length>0);
              const full=myActesOff.filter(a=>freeFor(a,occ).length===0);
              const go=(a,lost)=>{const fs=freeFor(a,occ);if(fs.length===1)return poseFree(a,fs[0],lost);setFreeStep({a,lost});};
              const grp=(titre,col,items,render)=>items.length===0?null:RE("div",{key:titre,style:{marginBottom:9}},
                RE("div",{style:{fontSize:9,fontWeight:800,color:col,textTransform:"uppercase",letterSpacing:.4,marginBottom:4}},titre),
                RE("div",{style:{display:"flex",flexWrap:"wrap",gap:5}},items.map(render)));
              const nSl=(a)=>{const n=freeFor(a,occ).length;return n+(n>1?" salles libres":" salle libre");};
              return RE("div",null,
                grp("📥 À reporter","#b45309",pinned,(it,i)=>RE("button",{key:"p"+i,onClick:()=>go(it.a,it.lost),
                  style:{fontSize:11,padding:"5px 10px",borderRadius:8,cursor:"pointer",fontWeight:800,border:"1.5px solid #b45309",background:"rgba(245,158,11,.12)",color:"#b45309",textAlign:"left"}},
                  (it.a.short||it.a.label)+" — report du "+fmtD(it.lost)+" "+it.lost.sl)),
                grp("Ouvrir","#16a34a",withRoom,a=>RE("button",{key:a.id,onClick:()=>go(a,null),
                  style:{fontSize:11,padding:"5px 10px",borderRadius:8,cursor:"pointer",fontWeight:800,border:"1.5px solid #16a34a",background:"rgba(22,163,74,.10)",color:"#16a34a"}},
                  (a.short||a.label)+" · "+nSl(a))),
                grp("Aucune salle libre ce créneau","var(--txt3)",full,a=>RE("span",{key:a.id,
                  style:{fontSize:11,padding:"5px 10px",borderRadius:8,fontWeight:700,border:"1px dashed var(--border)",background:"transparent",color:"var(--txt3)",opacity:.75}},
                  (a.short||a.label)+" · aucune salle libre")),
                (pinned.length+withRoom.length+full.length)===0&&RE("div",{style:{fontSize:11,color:"var(--txt3)"}},"Aucune activité ouvrable pour vous sur ce créneau."));
        })())));
}

/* ═══════════════ v10.29 : onglet CONSTRUIRE ═══════════════
   Chef d'orchestre de la construction d'un planning. N'INVENTE AUCUNE
   FONCTION : les tuiles Tour et Gardes montent les écrans EXISTANTS (mêmes
   composants, mêmes props, via tourProps/gardeProps partagés avec les onglets
   d'origine), les autres pointent à la main et renvoient vers l'onglet concerné.
   UNE SEULE PÉRIODE, choisie dans la barre figée du haut : aucune flèche de mois
   dans les tuiles (prop noNav), pour ne jamais remplir deux périodes à la fois.
   Les alertes sont NON BLOQUANTES : elles signalent, elles n'empêchent pas.
   v10.30 : pointage à UNE COCHE, étape terminée d'elle-même quand elle est
   mesurable, repli à la validation, jauge, rail numéroté, et le planning type
   s'applique SANS QUITTER l'onglet (la fenêtre reçoit la période de Construire). */
/* v10.32 — LOT 2 : les trois demandes a l'equipe.
   [identifiant, icone, ce que voit le medecin, champ de reponse]
   Le champ « pers » est CELUI DU POINTAGE A LA MAIN de l'etape 1 : quand un
   medecin repond, sa ligne se coche dans Construire — un seul etat, jamais deux. */
const BUILD_DEM=[["conges","🏖️","Poser vos congés de la période","pers","Congés"],
                 ["tour","🔄","Dire vos préférences de tour","prefT","Préférences de tour"],
                 ["garde","🌙","Dire vos préférences de gardes","prefG","Préférences de gardes"]];
/* v10.33, SA REGLE : une demande ne part qu'aux personnes CONCERNEES — les
   preferences de tour aux medecins qui tournent, celles de gardes a ceux qui en
   prennent. Les autres ne recoivent rien et ne comptent nulle part. */
const demConcerne=(m,id)=>!m?false:(id==="tour"?m.tourMed===true:id==="garde"?m.garde===true:true);
const demPop=(meds,id,jours)=>meds.filter(m=>demConcerne(m,id)&&offEtat(m,jours||[])!=="off");   /* v10.41 : hors désactivés période entière */
/* l'annee de fin est dite quand la periode change d'annee (comme _titlePeriod) :
   un bandeau se lit hors contexte, il ne doit pas laisser d'ambiguite. */
const perLibelle=(sy,sm)=>{const a=String(sy).split("_");const y=+a[0],m=(sm===undefined?+String(sy).split("_")[1]:sm);
  const ey=m+PCFG.len-1>11?y+1:y;
  return MOIS[m]+" — "+MOIS[(m+PCFG.len-1)%12]+" "+(y!==ey?y+"/"+ey:ey);};
const BUILD_SPECS=["Coro","EEP","FOP","Stim"];
const BIP_MIN_SEM=3;   /* un jour sans bip est normal ; on alerte sous 3 bips/semaine */
const BUILD_BAR_H=46;
/* v10.31 : ce qu'on retrouve en revenant dans l'onglet — periode et tuiles ouvertes.
   Volontairement en memoire de session, comme SCROLL_MEM (v9.98) : rien ne survit
   au rechargement, le defilement est memorise par goTab. */
const BUILD_MEM={per:null,ouv:null};  /* hauteur de la barre de période — les zones figées des écrans montés se calent dessous */

function BuildTile({n,icon,titre,sous,ouvert,onToggle,alerte,fait,auto,onFait,peutFaire,children}){
  const ok=!!(fait||auto);
  const col=ok?"#3fb950":(alerte?"#f59e0b":"var(--border)");
  return(
    <div style={{display:"flex",gap:8,alignItems:"stretch"}}>
      <div style={{width:24,flex:"0 0 24px",display:"flex",flexDirection:"column",alignItems:"center"}}>
        <div style={{width:24,height:24,borderRadius:12,marginTop:10,flex:"0 0 24px",display:"flex",alignItems:"center",justifyContent:"center",fontSize:11,fontWeight:800,
          border:"1px solid "+(ok?"#3fb950":"var(--border)"),background:ok?"#3fb950":"var(--bg2)",color:ok?"#fff":"var(--txt3)"}}>{ok?"✓":n}</div>
        <div style={{flex:1,width:2,background:"var(--border2)",margin:"2px 0"}}/>
      </div>
      {/* v10.31 : PAS d'overflow:hidden ici — il transformait la tuile en conteneur
           de defilement et empechait le rappel du Tour de se figer. */}
      <div style={{flex:1,minWidth:0,border:"1px solid "+col,borderRadius:9,background:"var(--bg2)",marginBottom:8}}>
        <div onClick={onToggle} style={{display:"flex",alignItems:"center",gap:9,padding:"9px 11px",cursor:"pointer"}}>
          <span style={{fontSize:13}}>{icon}</span>
          <div style={{flex:1,minWidth:0}}>
            <div style={{fontSize:13,fontWeight:800,color:"var(--txt)"}}>{titre}</div>
            {sous&&<div style={{fontSize:11,color:"var(--txt3)",marginTop:1}}>{sous}</div>}
          </div>
          {ok&&<span style={{fontSize:10,fontWeight:800,padding:"2px 8px",borderRadius:20,border:"1px solid #3fb950",color:"#3fb950",background:"rgba(63,185,80,.10)"}}>{fait?"validé":"terminé"}</span>}
          {!ok&&alerte&&<span style={{fontSize:10,fontWeight:800,padding:"2px 8px",borderRadius:20,border:"1px solid #f59e0b",color:"#b45309",background:"rgba(245,158,11,.13)"}}>à finir</span>}
          <span style={{fontSize:12,color:"var(--txt3)"}}>{ouvert?"▾":"▸"}</span>
        </div>
        {ouvert&&<div style={{padding:"0 11px 11px"}}>
          {alerte&&<div style={{margin:"0 0 9px",padding:"5px 9px",borderRadius:6,background:"rgba(245,158,11,.13)",border:"1px solid #f59e0b",color:"#b45309",fontSize:11,fontWeight:600}}>⚠ {alerte}</div>}
          {children}
          {peutFaire&&<div style={{marginTop:10,display:"flex",alignItems:"center",gap:8,flexWrap:"wrap"}}>
            <button onClick={onFait} style={{fontSize:11,padding:"4px 13px",borderRadius:6,fontWeight:800,cursor:"pointer",border:fait?"1.5px solid #3fb950":"1.5px solid var(--border)",background:fait?"rgba(63,185,80,.13)":"var(--bg3)",color:fait?"#3fb950":"var(--txt2)"}}>{fait?"✓ Étape validée":"Marquer cette étape comme faite"}</button>
            {fait&&fait.by&&<span style={{fontSize:10,color:"var(--txt3)"}}>{"par "+fait.by+" le "+fait.at}</span>}
          </div>}
        </div>}
      </div>
    </div>
  );
}

/* v10.30 : une seule coche, sa demande — « j'ai juste besoin de cocher si la
   personne a posé ses vacances ». Le oui / non / pas besoin est retiré. */
function BuildPersonList({gens,etat,onSet,peut,vide}){
  if(!gens.length)return <div style={{fontSize:11,color:"var(--txt3)"}}>{vide}</div>;
  return(
    <div style={{display:"grid",gridTemplateColumns:"repeat(auto-fill,minmax(210px,1fr))",gap:4}}>
      {gens.map(m=>{const on=!!(etat||{})[m.id];return(
        <div key={m.id} onClick={()=>{if(peut)onSet(m.id,!on);}} style={{display:"flex",alignItems:"center",gap:6,padding:"4px 7px",borderRadius:6,cursor:peut?"pointer":"default",
          background:on?"rgba(63,185,80,.10)":"var(--bg3)",border:"1px solid "+(on?"#3fb950":"transparent")}}>
          <span style={{width:15,height:15,borderRadius:4,flex:"0 0 15px",display:"flex",alignItems:"center",justifyContent:"center",fontSize:10,fontWeight:800,
            border:"1.5px solid "+(on?"#3fb950":"var(--border)"),background:on?"#3fb950":"transparent",color:"#fff"}}>{on?"✓":""}</span>
          <span style={{width:26,height:20,borderRadius:5,background:m.color||"#888",color:"#fff",fontSize:9,fontWeight:800,display:"flex",alignItems:"center",justifyContent:"center",flex:"0 0 26px"}}>{m.init}</span>
          <span style={{fontSize:11,color:"var(--txt2)",overflow:"hidden",textOverflow:"ellipsis",whiteSpace:"nowrap"}}>{m._lib||(m.prenom+" "+m.nom)}</span>
        </div>);})}
    </div>
  );
}

function BuildLien({txt,onClick}){
  return <button onClick={onClick} style={{fontSize:11,padding:"4px 12px",borderRadius:6,border:"1px solid var(--border)",background:"var(--bg3)",color:"var(--txt2)",fontWeight:700,cursor:"pointer"}}>{txt}</button>;
}

/* Cadre des ecrans montes : rappelle qu'on regarde l'onglet d'origine, entier. */
function BuildEmbed({children}){
  return <div style={{border:"1px dashed var(--border)",borderRadius:8,padding:"5px 6px 6px",background:"var(--bg)"}}>{children}</div>;
}

/* v10.32 : LE RAPPEL DU MEDECIN. Il s'affiche dans l'onglet Planning QUELLE QUE
   SOIT LA PERIODE AFFICHEE — sa regle : « les gens n'iront jamais dans la periode
   d'apres spontanement ». On balaie donc TOUTES les periodes de `build`, et le
   bandeau dit de quelle periode il s'agit, avec un bouton pour y aller. */
function BuildAsk({build,medecins,editMedId,onRepondre,onGoPer}){
  if(!editMedId)return null;
  const moi=medecins.find(m=>m.id===editMedId);
  if(!moi||(moi.role||"medecin")!=="medecin")return null;
  const att=[];
  Object.keys(build||{}).forEach(k=>{
    const B=(build||{})[k]||{};
    const jrsK=perDaysList(+String(k).split("_")[0],+String(k).split("_")[1]);   /* v10.41 */
    BUILD_DEM.forEach(([id,ic,txt,champ])=>{
      if((B.dem||{})[id]&&demConcerne(moi,id)&&offEtat(moi,jrsK)!=="off"&&!((B[champ]||{})[editMedId]))att.push({k:k,id:id,ic:ic,txt:txt,champ:champ});
    });
  });
  if(!att.length)return null;
  return(
    <div style={{marginBottom:10}}>
      {att.map(a=>(
        <div key={a.k+"|"+a.id} style={{display:"flex",alignItems:"center",gap:9,flexWrap:"wrap",padding:"7px 11px",marginBottom:5,borderRadius:8,
          border:"1px solid #f59e0b",background:"rgba(245,158,11,.13)"}}>
          <span style={{fontSize:14}}>{a.ic}</span>
          <div style={{flex:1,minWidth:150}}>
            <div style={{fontSize:12.5,fontWeight:800,color:"#b45309"}}>{a.txt}</div>
            <div style={{fontSize:11,color:"var(--txt2)"}}>{"Pour la période "+perLibelle(a.k)}</div>
          </div>
          <button onClick={()=>onGoPer(a.k)} style={{fontSize:11,padding:"4px 11px",borderRadius:6,border:"1px solid var(--border)",background:"var(--bg2)",color:"var(--txt2)",fontWeight:700,cursor:"pointer"}}>→ Voir cette période</button>
          <button onClick={()=>onRepondre(a.k,a.champ)} style={{fontSize:11,padding:"4px 13px",borderRadius:6,border:"1.5px solid #3fb950",background:"rgba(63,185,80,.13)",color:"#3fb950",fontWeight:800,cursor:"pointer"}}>✓ C'est fait</button>
        </div>
      ))}
    </div>
  );
}

function BuildTab({build,setBuild,medecins,getEntries,tourMed,isEdit,darkMode,setDarkMode,author,goTab,onOpenBip,onApplyPT,onRemovePT,tourProps,gardeProps}){
  /* période : ouverture sur la période SUIVANTE, comme repPer de ReportsView */
  const [bPer,setBPer]=React.useState(()=>{if(BUILD_MEM.per)return BUILD_MEM.per;const t=new Date();const p0=perStart(t.getFullYear(),t.getMonth());return perNext(p0.sy,p0.sm);});
  const allerA=(p)=>{BUILD_MEM.per={sy:p.sy,sm:p.sm};setBPer({sy:p.sy,sm:p.sm});};
  const pKey=bPer.sy+"_"+bPer.sm;
  const B=(build||{})[pKey]||{};
  const patchB=(patch)=>setBuild(p=>{const cur=(p||{})[pKey]||{};return {...(p||{}),[pKey]:{...cur,...patch}};});
  const sign=()=>({by:author||"?",at:new Date().toLocaleDateString("fr-FR")});
  const setPers=(medId,v)=>{const c={...(B.pers||{})};if(v)c[medId]=1;else delete c[medId];patchB({pers:c});};
  const setRep=(champ,medId,v)=>{const c={...(B[champ]||{})};if(v)c[medId]=1;else delete c[medId];patchB({[champ]:c});};
  const setDem=(id)=>{const d={...(B.dem||{})};if(d[id])delete d[id];else d[id]=sign();patchB({dem:d});};
  const setSpec=(nom)=>{const s={...(B.specs||{})};if(s[nom])delete s[nom];else s[nom]=sign();patchB({specs:s});};

  const perLbl=perLibelle(bPer.sy,bPer.sm);
  const bDays=useMemo(()=>perDaysList(bPer.sy,bPer.sm),[bPer.sy,bPer.sm,PCFG.len]);
  const bJours=React.useMemo(()=>perDaysList(bPer.sy,bPer.sm),[bPer.sy,bPer.sm,PCFG.len]);
  /* v10.41 : un médecin désactivé sur TOUTE la période sort des listes et des
     comptes de l'onglet — une étape peut se terminer sans lui. */
  /* v10.93 : la période de Construire est INDÉPENDANTE de celle qui est
     affichée ailleurs. Les rôles juniors doivent donc porter le nom du
     titulaire de CETTE période — sinon l'onglet propose l'ancienne équipe
     quand on prépare le semestre suivant (son constat du 19/08). */
  const bIso=bJours.length?dKey(bJours[0].y,bJours[0].m,bJours[0].d):null;
  const medsB=useMemo(()=>(medecins||[]).map(m=>djAff(m,bIso)),[medecins,bIso]);
  const meds=useMemo(()=>medsB.filter(m=>(m.role||"medecin")==="medecin"&&offEtat(m,bJours)!=="off"),[medsB,bJours]);
  /* v10.31 : la coche « absences a recueillir » de la fiche Equipe decide qui parait ici */
  const autres=useMemo(()=>medecins.filter(m=>(m.role||"medecin")!=="medecin"&&m.suiviAbs!==false),[medecins]);

  /* ── mesures : elles servent A LA FOIS d'alerte et de fin d'etape ── */
  const nMeds=meds.filter(m=>(B.pers||{})[m.id]).length;
  const nAutres=autres.filter(m=>(B.pers||{})[m.id]).length;

  const tour=useMemo(()=>{
    const vus={};let tot=0,ok=0;
    bDays.forEach(({y,m,d})=>{
      const wk=wKey(y,m,d);if(vus[wk])return;vus[wk]=1;tot++;
      const wm=tourMed[wk]||{};
      if(((wm.HC||[]).length)||((wm.USIC||[]).length))ok++;
    });
    return{tot:tot,ok:ok};
  },[bDays,tourMed]);

  const gardes=useMemo(()=>{
    let ok=0;
    bDays.forEach(({y,m,d})=>{
      if(medecins.some(md=>["N","JOUR"].some(sl=>getEntries(md.id,y,m,d,sl).some(e=>e&&e.acteId==="GARDE"))))ok++;
    });
    return{tot:bDays.length,ok:ok};
  },[bDays,medecins,getEntries]);

  const bips=useMemo(()=>{
    const par={};
    bDays.forEach(({y,m,d})=>{
      const wk=wKey(y,m,d);
      if(par[wk]===undefined)par[wk]=0;
      if(dow(y,m,d)===0||dow(y,m,d)===6)return;
      medecins.forEach(md=>{
        if(["M","AM"].some(sl=>getEntries(md.id,y,m,d,sl).some(e=>e&&e.acteId==="BIP")))par[wk]++;
      });
    });
    const ks=Object.keys(par);
    return{tot:ks.length,ok:ks.filter(k=>par[k]>=BIP_MIN_SEM).length};
  },[bDays,medecins,getEntries]);

  const nSpec=BUILD_SPECS.filter(s=>(B.specs||{})[s]).length;
  const valide=(n)=>(B.etapes||{})[n]||null;
  /* ETAPE TERMINEE D'ELLE-MEME des qu'elle est mesurable : sa demande du 12/08.
     L'etape 5 (planning type) est la seule qui ne se mesure pas — elle garde
     donc son bouton de validation a la main. */
  const autoOk={1:meds.length>0&&nMeds===meds.length,
    2:tour.tot>0&&tour.ok===tour.tot,
    3:gardes.tot>0&&gardes.ok===gardes.tot,
    4:autres.length>0&&nAutres===autres.length,
    5:false,
    6:nSpec===BUILD_SPECS.length,
    7:bips.tot>0&&bips.ok===bips.tot};
  const estFait=(n)=>!!(valide(n)||autoOk[n]);

  /* la premiere etape non terminee est ouverte au premier affichage ; une etape
     validee se REFERME (sa demande) et ne se rouvre jamais toute seule */
  const [ouv,setOuv]=React.useState(()=>{if(BUILD_MEM.ouv)return BUILD_MEM.ouv;for(let n=1;n<=7;n++){if(!autoOk[n])return {[n]:true};}return {};});
  const majOuv=(f)=>setOuv(o=>{const r=f(o);BUILD_MEM.ouv=r;return r;});
  const toggle=(n)=>majOuv(o=>({...o,[n]:!o[n]}));
  const setEtape=(n)=>{
    const st={...(B.etapes||{})};
    if(st[n])delete st[n];else{st[n]=sign();majOuv(o=>({...o,[n]:false}));}
    patchB({etapes:st});
  };

  const manq=(n,t)=>n<t?(t-n):0;
  const mMeds=manq(nMeds,meds.length),mAut=manq(nAutres,autres.length);
  const mTour=manq(tour.ok,tour.tot),mGar=manq(gardes.ok,gardes.tot);
  const mSpec=manq(nSpec,BUILD_SPECS.length),mBip=manq(bips.ok,bips.tot);

  const tuiles=[
    {n:1,icon:"🏖️",titre:"Congés de l'équipe",
     sous:nMeds+" médecin"+(nMeds>1?"s":"")+" sur "+meds.length+" ont posé leurs congés"+((B.dem&&Object.keys(B.dem).length)?(" · "+Object.keys(B.dem).length+" demande"+(Object.keys(B.dem).length>1?"s":"")+" ouverte"+(Object.keys(B.dem).length>1?"s":"")):""),
     alerte:mMeds?(mMeds+" médecin"+(mMeds>1?"s n'ont":" n'a")+" pas encore posé ses congés"):null,
     body:<div>
       <div style={{display:"grid",gridTemplateColumns:"repeat(auto-fill,minmax(240px,1fr))",gap:6,marginBottom:10}}>
         {BUILD_DEM.map(([id,ic,txt,champ,titre])=>{
           const ouverte=(B.dem||{})[id];
           const pop=demPop(meds,id,bJours);
           const n=pop.filter(m=>(B[champ]||{})[m.id]).length;
           return(
             <div key={id} style={{border:"1px solid "+(ouverte?"#8b5cf6":"var(--border)"),borderRadius:8,padding:"7px 9px",background:"var(--bg3)"}}>
               <div style={{fontSize:12,fontWeight:800,color:"var(--txt)"}}>{ic+" "+titre}</div>
               <div style={{fontSize:11,color:"var(--txt3)",margin:"2px 0 6px"}}>{n+" réponse"+(n>1?"s":"")+" sur "+pop.length+(id==="tour"?" qui tournent":id==="garde"?" de garde":"")}</div>
               {isEdit&&<button onClick={()=>setDem(id)} style={{fontSize:11,padding:"3px 11px",borderRadius:6,fontWeight:800,cursor:"pointer",
                 border:"1.5px solid #8b5cf6",background:ouverte?"#8b5cf6":"rgba(139,92,246,.10)",color:ouverte?"#fff":"#8b5cf6"}}>{ouverte?"✓ Demande ouverte":"Ouvrir la demande"}</button>}
               {ouverte&&ouverte.at&&<div style={{fontSize:10,color:"var(--txt3)",marginTop:4}}>{"ouverte le "+ouverte.at}</div>}
             </div>);
         })}
       </div>
       <div style={{fontSize:11,color:"var(--txt3)",marginBottom:8}}>Une coche par personne dès qu'elle a posé ses vacances — elle se coche aussi toute seule quand le médecin répond au rappel affiché dans son Planning. Les attachés et les IDE sont rappelés à l'étape 4.</div>
       <BuildPersonList gens={meds.map(m=>{const l=djNomsPeriode(m,bJours);return l?{...m,_lib:l}:m;})} etat={B.pers} onSet={setPers} peut={isEdit} vide="Aucun médecin dans l'équipe."/>
     </div>},
    {n:2,icon:"🔄",titre:"Distribution du tour",
     sous:tour.ok+" semaine"+(tour.ok>1?"s":"")+" sur "+tour.tot+" ont un tourneur",
     alerte:mTour?(mTour+" semaine"+(mTour>1?"s":"")+" sans tour attribué"):null,
     body:<BuildEmbed><TourTab key={pKey} {...tourProps} medecins={medsB} noNav={true} year={bPer.sy} month={bPer.sm}/></BuildEmbed>},
    {n:3,icon:"🌙",titre:"Gardes",
     sous:gardes.ok+" jour"+(gardes.ok>1?"s":"")+" sur "+gardes.tot+" ont une garde",
     alerte:mGar?(mGar+" jour"+(mGar>1?"s":"")+" sans garde sur la période"):null,
     body:<BuildEmbed><GardeView key={pKey} {...gardeProps} medecins={medsB} noNav={true} showFull={true} year={bPer.sy} month={bPer.sm}/></BuildEmbed>},
    {n:4,icon:"🚫",titre:"Absences de tout le monde",
     sous:nAutres+" sur "+autres.length+" renseigné"+(nAutres>1?"s":""),
     alerte:mAut?(mAut+" personne"+(mAut>1?"s":"")+" hors médecins sans réponse"):null,
     body:<div>
       <div style={{fontSize:11,color:"var(--txt3)",marginBottom:8}}>Attachés et IDE. Rappel : pour certains on recueille les ABSENCES, pour d'autres les PRÉSENCES. Seuls ceux dont la fiche Équipe porte « absences à recueillir » figurent ici.</div>
       <BuildPersonList gens={autres} etat={B.pers} onSet={setPers} peut={isEdit} vide="Aucun attaché ni IDE dans l'équipe."/>
       <div style={{marginTop:8,display:"flex",gap:6,flexWrap:"wrap"}}>
         <BuildLien txt="→ Onglet Attachés" onClick={()=>goTab("attache")}/>
       </div></div>},
    {n:5,icon:"📋",titre:"Appliquer le planning type",
     sous:"s'applique d'ici, sur la période affichée",
     alerte:null,
     body:<div>
       <div style={{display:"flex",gap:6,flexWrap:"wrap"}}>
         {isEdit&&<button onClick={()=>onApplyPT(bPer)} style={{fontSize:11,padding:"4px 13px",borderRadius:6,border:"1.5px solid #388bfd",background:"rgba(56,139,253,.10)",color:"#388bfd",fontWeight:800,cursor:"pointer"}}>📋 Appliquer le planning type</button>}
         {isEdit&&<button onClick={()=>onRemovePT(bPer)} style={{fontSize:11,padding:"4px 13px",borderRadius:6,border:"1px solid #dc2626",background:"var(--bg2)",color:"#dc2626",fontWeight:700,cursor:"pointer"}}>🗑 Retirer</button>}
         <BuildLien txt="→ Modifier le planning type" onClick={()=>goTab("plantype")}/>
       </div></div>},
    {n:6,icon:"🔬",titre:"Plannings par surspécialité",
     sous:nSpec+" sur "+BUILD_SPECS.length+" terminée"+(nSpec>1?"s":""),
     alerte:mSpec?(mSpec+" surspécialité"+(mSpec>1?"s":"")+" non terminée"+(mSpec>1?"s":"")):null,
     body:<div>
       <div style={{display:"flex",gap:4,flexWrap:"wrap",marginBottom:8}}>
         {BUILD_SPECS.map(s=>{const f=(B.specs||{})[s];return(
           <button key={s} disabled={!isEdit} onClick={()=>setSpec(s)} style={{fontSize:11,padding:"3px 11px",borderRadius:6,fontWeight:700,cursor:isEdit?"pointer":"default",border:"1px solid "+(f?"#3fb950":"var(--border)"),background:f?"rgba(63,185,80,.13)":"var(--bg3)",color:f?"#3fb950":"var(--txt2)"}}>{(f?"✓ ":"")+s}</button>);})}
       </div>
       <div style={{display:"flex",gap:6,flexWrap:"wrap"}}>
         <BuildLien txt="→ PT Cardio" onClick={()=>goTab("plateau")}/>
         <BuildLien txt="→ PT Angio" onClick={()=>goTab("angio")}/>
       </div></div>},
    {n:7,icon:"📟",titre:"Bip de Béthune",
     sous:bips.ok+" semaine"+(bips.ok>1?"s":"")+" sur "+bips.tot+" à "+BIP_MIN_SEM+" bips ou plus",
     alerte:mBip?(mBip+" semaine"+(mBip>1?"s":"")+" sous "+BIP_MIN_SEM+" bips"):null,
     body:<div>
       <div style={{fontSize:11,color:"var(--txt3)",marginBottom:8}}>Un jour sans bip est normal ; l'alerte se déclenche sous {BIP_MIN_SEM} bips dans une semaine.</div>
       <div style={{display:"flex",gap:6,flexWrap:"wrap"}}>
         {isEdit&&<button onClick={onOpenBip} style={{fontSize:11,padding:"4px 13px",borderRadius:6,border:"1.5px solid #46bdc6",background:"rgba(70,189,198,.10)",color:"#46bdc6",fontWeight:800,cursor:"pointer"}}>📟 Répartition du Bip</button>}
         <BuildLien txt="→ Onglet CHB" onClick={()=>goTab("chb")}/>
       </div></div>}
  ];

  const nFaits=tuiles.filter(t=>estFait(t.n)).length;

  return(
    <div>
      <div style={{...S.bar,position:"sticky",top:HDR_H,zIndex:60,background:"var(--bg)",paddingTop:6,paddingBottom:6,marginBottom:0,minHeight:BUILD_BAR_H}}>
        <div style={{display:"flex",alignItems:"center",gap:6}}>
          <button onClick={()=>allerA(perPrev(bPer.sy,bPer.sm))} style={S.arr}>‹</button>
          <h2 style={S.mTit}>{"🏗️ Construire — "+perLbl}</h2>
          <button onClick={()=>allerA(perNext(bPer.sy,bPer.sm))} style={S.arr}>›</button>
        </div>
        <div style={{display:"flex",gap:6,alignItems:"center",marginLeft:"auto"}}>
          <button onClick={()=>setDarkMode(d=>!d)} style={{...S.arr,fontSize:13,width:30}}>{darkMode?"☀️":"🌓"}</button>
        </div>
      </div>
      <div style={{display:"flex",alignItems:"center",gap:8,margin:"8px 0 14px"}}>
        <div style={{flex:1,height:6,borderRadius:3,background:"var(--bg3)",overflow:"hidden"}}>
          <div style={{height:"100%",width:Math.round(nFaits/7*100)+"%",background:"#3fb950"}}/>
        </div>
        <div style={{fontSize:11,color:"var(--txt2)",fontWeight:700,whiteSpace:"nowrap"}}>{nFaits+" étape"+(nFaits>1?"s":"")+" sur 7"}</div>
      </div>
      {!isEdit&&<div style={{fontSize:11,color:"var(--txt3)",marginBottom:8}}>Lecture seule : le pointage est réservé aux personnes qui peuvent modifier le planning.</div>}
      {tuiles.map(t=>(
        <BuildTile key={t.n} n={t.n} icon={t.icon} titre={t.titre} sous={t.sous} ouvert={!!ouv[t.n]} onToggle={()=>toggle(t.n)}
          alerte={t.alerte} fait={valide(t.n)} auto={autoOk[t.n]} onFait={()=>setEtape(t.n)} peutFaire={isEdit&&!autoOk[t.n]}>
          {t.body}
        </BuildTile>
      ))}
      <div style={{fontSize:10,color:"var(--txt3)",textAlign:"center",marginTop:10}}>Les alertes signalent, elles ne bloquent pas : une étape non terminée n'empêche jamais d'avancer.</div>
    </div>
  );
}

/* ═══════════════ v10.35 : SAUVEGARDE EXPLOITABLE ═══════════════
   Sortir le planning dans un fichier qu'il ouvre lui-même, pour rediffuser vite
   le jour où l'application ou Firebase tombe. Deux principes :
   — AUCUNE BIBLIOTHÈQUE : le fichier est un tableau écrit à la main, que Sheets
     et Excel ouvrent comme une feuille. Rien à télécharger au moment où le
     réseau est justement en panne.
   — AUCUNE LECTURE DUPLIQUÉE : `expEntries` est la fonction que `getEntries`
     utilise elle-même — l'export ne peut donc pas lire le planning autrement
     que l'écran. Elle sert aussi bien au planning courant qu'à une sauvegarde. */
const EXP_WE_BG="#ffd966";     /* jaune clair 1 de Google Sheets, sa demande */
const EXP_WE_VIDE="#fff9e6";   /* même teinte très diluée pour les cases vides du week-end */
const EXP_SEUIL=200;           /* cases modifiées avant rappel — réglable dans Paramètres */
const EXP_JOURS=7;             /* ou une semaine, au premier des deux atteint */
const EXP_JSEM=["dimanche","lundi","mardi","mercredi","jeudi","vendredi","samedi"];
const EXP_MOIS=["janvier","février","mars","avril","mai","juin","juillet","août","septembre","octobre","novembre","décembre"];

/* Lecture d'une case — LA MÊME que celle de l'application (getEntries l'appelle).
   `p` est le planning déjà fusionné avec les archives s'il y a lieu. */
function expEntries(p,tourMed,tourDerog,medId,y2,m2,d2,slot){
  if(slot!=="JOUR"){
    const absE=cellEs((p[sk(y2,m2,d2,"JOUR")]||{})[medId]).find(e=>e&&ABS_IDS.includes(e.acteId));
    if(absE) return slot==="M"?[{...absE,_fullDay:true}]:slot==="AM"?[{_blocked:true}]:[];
  }
  if(slot==="JOUR"){const e=(p[sk(y2,m2,d2,"JOUR")]||{})[medId];return e?(Array.isArray(e)?e:[e]):[];}
  const entries=(p[sk(y2,m2,d2,slot)]||{})[medId];
  if(entries)return Array.isArray(entries)?entries:[entries];
  if(!isWE(y2,m2,d2)&&(slot==="M"||slot==="AM")){
    const wk=wKey(y2,m2,d2),wm=(tourMed||{})[wk]||{HC:[],USIC:[]};
    const dgS=((tourDerog||{})[dKey(y2,m2,d2)]||{})[medId];
    if(dgS===true||(dgS&&dgS[slot]))return [];
    if((wm.HC||[]).includes(medId))return [{acteId:"TOUR_HC",salle:null}];
    if((wm.USIC||[]).includes(medId))return [{acteId:"TOUR_USIC",salle:null}];
  }
  return[];
}

const expEsc=(s)=>String(s).replace(/&/g,"&amp;").replace(/</g,"&lt;").replace(/>/g,"&gt;").replace(/"/g,"&quot;");
const expDate=(y,m,d)=>EXP_JSEM[new Date(y,m,d).getDay()]+" "+d+" "+EXP_MOIS[m]+" "+y;

/* Construit le tableau d'une période. Rend une chaîne, n'écrit aucun fichier :
   la même sortie sert au téléchargement et pourra servir à un aperçu. */
function expTable(per,src){
  const plan=src.plan||{},notes=src.notes||{},tourMed=src.tourMed||{},tourDerog=src.tourDerog||{};
  const medecins=src.medecins||[],actes=src.actes||[],salleReg=src.salleReg||[];
  const acte=(id)=>actes.find(a=>a.id===id)||null;
  const meds=medecins.filter(m=>(m.role||"medecin")==="medecin");
  const salles=[];
  (salleReg||[]).forEach(x=>{if(x&&x.n&&salles.indexOf(x.n)<0)salles.push(x.n);});
  const jours=perDaysList(per.sy,per.sm);

  /* libellé d'une case : le nom court de l'activité, la salle si elle en porte une */
  const libelle=(es)=>{
    const out=[];
    (es||[]).forEach(e=>{
      if(!e||e._blocked||!e.acteId)return;
      const a=acte(e.acteId);
      let t=a?(a.short||a.label||e.acteId):e.acteId;
      if(e.salle)t+=" "+e.salle;
      if(e.cond)t="? "+t;
      out.push(t);
    });
    return out.join(" + ");
  };
  const cellHTML=(txt,note,bg)=>{
    let st=bg?' style="background:'+bg+'"':"";
    let c=expEsc(txt||"");
    if(note){
      /* Un vrai commentaire de cellule n'existe pas dans ce format : on garde le
         REPÈRE visible (✎) et le texte, en plus petit, dans la cellule. */
      c=(c?c+" ":"")+'<span style="font-size:8pt;font-style:italic">✎ '+expEsc(note)+"</span>";
      st=' title="'+expEsc(note)+'"'+st;
    }
    return "<td"+st+">"+c+"</td>";
  };

  const ent=["j","Garde","Garde Interne"].concat(meds.map(m=>m.init)).concat(salles);
  const L=['<html><head><meta charset="utf-8"></head><body>',
    '<table border="1" cellspacing="0" cellpadding="2" style="border-collapse:collapse;font-family:Arial;font-size:10pt">',
    "<tr>"+ent.map(e=>'<th style="background:#efefef">'+expEsc(e)+"</th>").join("")+"</tr>"];

  jours.forEach(({y,m,d})=>{
    const we=isWE(y,m,d)||isFerie(y,m,d);
    const slots=we?["JOUR"]:["M","AM"];
    slots.forEach((sl,i)=>{
      const tds=[];
      /* colonne A : la date, une seule fois par jour */
      tds.push('<td style="background:'+(we?EXP_WE_BG:"#ffffff")+';text-align:left;white-space:nowrap">'
        +(i===0?expEsc(expDate(y,m,d)):"")+"</td>");
      /* gardes : celui qui porte GARDE sur N ou JOUR */
      let g="";
      if(i===0)meds.forEach(md=>{
        if(["N","JOUR"].some(s2=>expEntries(plan,tourMed,tourDerog,md.id,y,m,d,s2).some(e=>e&&e.acteId==="GARDE")))g=g?g+" "+md.init:md.init;
      });
      tds.push(cellHTML(g,null,we?EXP_WE_VIDE:null));
      tds.push(cellHTML("",null,we?EXP_WE_VIDE:null));   /* garde interne : tenue à la main */
      /* une colonne par médecin */
      meds.forEach(md=>{
        const es=expEntries(plan,tourMed,tourDerog,md.id,y,m,d,sl);
        const txt=libelle(es);
        const note=notes[nk(md.id,y,m,d,sl)]||null;
        const a=es.length?acte(es[0].acteId):null;
        const bg=txt?((a&&a.color)||null):(we?EXP_WE_VIDE:null);
        tds.push(cellHTML(txt,note,bg));
      });
      /* une colonne par salle du registre : on y lit les initiales */
      salles.forEach(nom=>{
        const qui=[];
        meds.forEach(md=>{
          expEntries(plan,tourMed,tourDerog,md.id,y,m,d,sl).forEach(e=>{
            if(e&&e.salle===nom&&qui.indexOf(md.init)<0)qui.push(md.init);
          });
        });
        tds.push(cellHTML(qui.join(" "),null,we?EXP_WE_VIDE:null));
      });
      L.push("<tr>"+tds.join("")+"</tr>");
    });
  });
  L.push("</table></body></html>");
  return L.join("\n");
}

/* Téléchargement — même mécanique que les exports CSV déjà présents. */
function expTelecharge(nom,contenu,type){
  const blob=new Blob(["\ufeff"+contenu],{type:type||"application/vnd.ms-excel;charset=utf-8"});
  const a=document.createElement("a");
  a.href=URL.createObjectURL(blob);a.download=nom;a.click();
  setTimeout(()=>URL.revokeObjectURL(a.href),4000);
}

/* Rappel dans le Planning de l'éditeur : premier des deux seuils atteint. */
function ExportRappel({nModifs,seuil,dernier,onAller,onPlusTard}){
  const jours=dernier?Math.floor((Date.now()-dernier)/86400000):999;
  const parTemps=jours>=EXP_JOURS, parCases=nModifs>=(seuil||EXP_SEUIL);
  if(!parTemps&&!parCases)return null;
  const motif=parCases
    ?(nModifs+" case"+(nModifs>1?"s":"")+" modifiée"+(nModifs>1?"s":"")+" depuis votre dernière sauvegarde")
    :(dernier?("dernière sauvegarde il y a "+jours+" jours"):"aucune sauvegarde sur cet ordinateur");
  return(
    <div style={{display:"flex",alignItems:"center",gap:9,flexWrap:"wrap",padding:"7px 11px",marginBottom:10,borderRadius:8,
      border:"1px solid #f59e0b",background:"rgba(245,158,11,.13)"}}>
      <span style={{fontSize:14}}>💾</span>
      <div style={{flex:1,minWidth:150}}>
        <div style={{fontSize:12.5,fontWeight:800,color:"#b45309"}}>Sauvegarde sur votre ordinateur</div>
        <div style={{fontSize:11,color:"var(--txt2)"}}>{motif}</div>
      </div>
      <button onClick={onAller} style={{fontSize:11,padding:"4px 13px",borderRadius:6,border:"1.5px solid #f59e0b",background:"var(--bg2)",color:"#b45309",fontWeight:800,cursor:"pointer"}}>→ Sauvegarder</button>
      <button onClick={onPlusTard} style={{fontSize:11,padding:"4px 11px",borderRadius:6,border:"1px solid var(--border)",background:"var(--bg2)",color:"var(--txt3)",fontWeight:700,cursor:"pointer"}}>Plus tard</button>
    </div>
  );
}

/* L'encart de Paramètres : source, période, et les deux fichiers. */
function ExportCard({per,setPer,source,setSource,backups,seuil,setSeuil,dernier,onExport,occupe}){
  const lbl=perLibelle(per.sy,per.sm);
  const dat=(ts)=>new Date(ts).toLocaleDateString("fr-FR")+" "+new Date(ts).toLocaleTimeString("fr-FR",{hour:"2-digit",minute:"2-digit"});
  return(
    <div style={{marginBottom:14,padding:10,borderRadius:8,border:"1px solid var(--border)",background:"var(--bg2)"}} id="set-export">
      <div style={{fontSize:11,fontWeight:700,color:"var(--txt2)",marginBottom:6}}>💻 Copie sur mon ordinateur</div>
      <div style={{fontSize:11,color:"var(--txt3)",marginBottom:8}}>Un fichier gardé chez vous, indépendant de l'application et de sa synchronisation. Le tableau ne couvre que la période choisie ci-dessous : il sert à rediffuser le planning. Les données brutes contiennent l'intégralité des données, toutes périodes confondues : elles servent à tout remettre en place via 📂 Importer.</div>

      <div style={{display:"flex",alignItems:"center",gap:6,marginBottom:8,flexWrap:"wrap"}}>
        <button onClick={()=>setPer(perPrev(per.sy,per.sm))} style={S.arr}>‹</button>
        <span style={{fontSize:12,fontWeight:800,color:"var(--txt)",minWidth:190,textAlign:"center"}}>{lbl}</span>
        <button onClick={()=>setPer(perNext(per.sy,per.sm))} style={S.arr}>›</button>
      </div>

      <div style={{fontSize:10,color:"var(--txt3)",fontWeight:700,textTransform:"uppercase",marginBottom:4}}>À partir de</div>
      <select value={source} onChange={e=>setSource(e.target.value)}
        style={{...S.fi,marginBottom:8}}>
        <option value="now">Le planning tel qu'il est maintenant</option>
        {(backups||[]).map((b,i)=><option key={b.id} value={b.id}>{"Sauvegarde du "+dat(b.ts)+(i===0?" (la plus récente)":"")}</option>)}
      </select>

      <div style={{display:"flex",gap:6,flexWrap:"wrap",marginBottom:8}}>
        <button disabled={occupe} onClick={()=>onExport("tableau")} style={{fontSize:11,padding:"5px 13px",borderRadius:6,border:"1.5px solid #f59e0b",background:"rgba(245,158,11,.10)",color:"#b45309",fontWeight:800,cursor:occupe?"default":"pointer",opacity:occupe?.6:1}}>📊 Le tableau (Excel / Sheets)</button>
        <button disabled={occupe} onClick={()=>onExport("donnees")} style={{fontSize:11,padding:"5px 13px",borderRadius:6,border:"1px solid var(--border)",background:"var(--bg3)",color:"var(--txt2)",fontWeight:700,cursor:occupe?"default":"pointer",opacity:occupe?.6:1}}>🗄 Les données brutes</button>
      </div>

      <div style={{fontSize:11,color:"var(--txt3)",marginBottom:6}}>{dernier?("Dernière sauvegarde : "+dat(dernier)):"Aucune sauvegarde faite depuis cet ordinateur."}</div>
      <div style={{display:"flex",alignItems:"center",gap:6,flexWrap:"wrap"}}>
        <span style={{fontSize:11,color:"var(--txt3)"}}>Me le rappeler au bout de</span>
        <input type="number" min="20" max="5000" step="10" value={seuil} onChange={e=>setSeuil(Math.max(20,parseInt(e.target.value)||EXP_SEUIL))}
          style={{...S.fi,width:80,padding:"3px 6px",textAlign:"center"}}/>
        <span style={{fontSize:11,color:"var(--txt3)"}}>cases modifiées, ou de {EXP_JOURS} jours.</span>
      </div>
    </div>
  );
}

/* ═══════════════ v10.37 : PARAMÈTRES REPLIABLES ═══════════════
   Sa question décisive : « est-ce que ce plan de visualisation va suivre ? »
   — c'est-à-dire, un encart ajouté dans six mois sera-t-il pris en compte ?
   D'où ce mécanisme posé UNE SEULE FOIS sur le conteneur, et non encart par
   encart : les titres sont LUS dans la page, le repli se fait par rang. Un
   encart écrit comme les autres est donc géré sans qu'on ait rien à ajouter,
   et cela règle aussi le fait que les deux fichiers ne rangent pas les encarts
   dans le même ordre — chacun lit le sien. */
const PSET_MAX=40;   /* rangs couverts par les règles de repli */

/* v10.39 : à l'usage, la rangée de boutons du haut ne servait pas — avec tous
   les encarts repliés, la page EST déjà son propre sommaire. Il ne reste qu'un
   bouton pour tout ouvrir d'un coup. */
function SetQuick({items,replies,onTout}){
  if(!items.length)return null;
  const tout=replies.length>=items.length;
  return(
    <div style={{display:"flex",justifyContent:"flex-end",marginBottom:8}}>
      <button onClick={onTout} style={{fontSize:11,padding:"3px 10px",borderRadius:6,fontWeight:700,cursor:"pointer",
        border:"1px solid var(--border)",background:"var(--bg3)",color:"var(--txt3)"}}>{tout?"Tout déplier":"Tout replier"}</button>
    </div>
  );
}

/* Les règles de repli : masquer tout ce qui suit le titre d'un encart replié.
   Écrites une fois pour tous les rangs — aucune n'est à ajouter plus tard. */
function setFoldCSS(){
  let out="";
  for(let i=1;i<=PSET_MAX;i++){
    out+=".pset.pf"+i+" > *:nth-child("+i+") > *:not(:first-child){display:none!important}\n";
    out+=".pset.pf"+i+" > *:nth-child("+i+"){padding-bottom:8px}\n";
  }
  out+=".pset > *[data-fold] > *:first-child{cursor:pointer}\n";
  return out;
}

/* Lit les encarts présents dans la page : rang et titre. Un encart = un enfant
   direct qui a un premier enfant porteur de texte et au moins un frère ensuite. */
function setScan(el){
  if(!el)return [];
  const out=[];
  const kids=el.children;
  for(let i=0;i<kids.length;i++){
    const k=kids[i];
    if(k.getAttribute&&k.getAttribute("data-noskip")==="1")continue;
    if(k.children.length<2)continue;
    const t=(k.children[0].textContent||"").trim();
    if(t.length<3||t.length>70)continue;   /* « Tour médical — minimums par surspécialité » fait 43 caractères */
    k.setAttribute("data-fold","1");
    out.push({i:i+1,titre:t.length>26?t.slice(0,25)+"…":t});
  }
  return out;
}

/* ═══════════════ v10.40 : DÉSACTIVER UN MÉDECIN ═══════════════
   Rotation des juniors et longs congés. Ce qui est enregistré : des DATES
   (m.off = [{du,au}] en ISO, sur la fiche), JAMAIS un numéro de période — sa
   contrainte du 13/08 : un changement de durée de période ne doit rien
   déplacer. « Sur la période » n'est qu'un raccourci qui remplit les deux
   dates avec les bornes affichées. Le champ vit sur la fiche médecin : il
   voyage avec la synchro existante de l'équipe, aucun document nouveau. */
/* v10.90 : plages saisies A LA MAIN + plages automatiques des rôles juniors
   (semestre sans nom). La fenêtre de désactivation ne lit et n'écrit que
   les manuelles — une plage automatique ne doit pas être « réactivable ». */
const medOffMan=(m)=>Array.isArray(m&&m.off)?m.off.filter(r=>r&&r.du&&r.au):[];
const medOffL=(m)=>{const a=medOffMan(m);const b=djOffRanges(m);return b.length?a.concat(b):a;};
const offOn=(m,y2,m2,d2)=>{const k=dKey(y2,m2,d2);return medOffL(m).some(r=>r.du<=k&&k<=r.au);};
/* état sur une liste de jours : null (actif), "part", ou "off" (tous couverts) */
const offEtat=(m,jours)=>{
  const L=medOffL(m);if(!L.length||!jours||!jours.length)return null;
  let n=0;jours.forEach(j=>{if(offOn(m,j.y,j.m,j.d))n++;});
  return n===0?null:n===jours.length?"off":"part";
};
const offFr=(iso)=>{const a=String(iso).split("-");return a[2]+"/"+a[1]+"/"+a[0];};

/* La fenêtre, centrée comme toutes celles de l'application. Réservée à
   l'éditeur par construction : la pastille n'est cliquable que pour lui. */
function DeactModal({med,perDays,perLbl,onSave,onClose,countActs=null,onClear=null}){
  const du0=perDays.length?dKey(perDays[0].y,perDays[0].m,perDays[0].d):"";
  const fin=perDays.length?perDays[perDays.length-1]:null;
  const au0=fin?dKey(fin.y,fin.m,fin.d):"";
  const [mode,setMode]=useState(0);
  const [d1,setD1]=useState(du0);
  const [d2,setD2]=useState(au0);
  if(!med)return null;
  const ranges=medOffMan(med);
  const ajouter=()=>{
    const r=mode===0?{du:du0,au:au0}:{du:d1,au:d2};
    if(!r.du||!r.au||r.au<r.du)return;
    onSave(ranges.concat([r]));
  };
  /* v10.42, SA CONSIGNE : les cases déjà posées persistent sous les hachures.
     Plutôt qu'une ligne d'Aide qu'on aura oubliée, la fenêtre COMPTE ce qui est
     posé sur les dates choisies et propose de le retirer d'un coup. */
  const rSel=mode===0?{du:du0,au:au0}:{du:d1,au:d2};
  const rOK=!!(rSel.du&&rSel.au&&rSel.au>=rSel.du);
  const nAct=(countActs&&rOK)?countActs(rSel.du,rSel.au):0;
  const bt=(sel)=>({display:"flex",gap:8,alignItems:"flex-start",padding:"8px 9px",border:"1px solid "+(sel?"#8b5cf6":"var(--border)"),borderRadius:8,marginBottom:6,cursor:"pointer",background:sel?"rgba(139,92,246,.08)":"transparent"});
  return(
    <div onClick={e=>{if(e.target===e.currentTarget)onClose();}} style={{position:"fixed",inset:0,background:"rgba(0,0,0,.55)",display:"flex",alignItems:"center",justifyContent:"center",zIndex:300}}>
      <div style={{background:"var(--bg2)",border:"1px solid var(--border)",borderRadius:12,padding:16,width:360,maxWidth:"94vw",maxHeight:"88vh",overflowY:"auto"}}>
        <div style={{display:"flex",alignItems:"center",gap:8,marginBottom:10}}>
          <div style={{...S.avT,background:med.color}}>{med.init}</div>
          <div style={{fontWeight:800,fontSize:14,color:"var(--txt)"}}>{(med.prenom||"")+" "+(med.nom||"")}</div>
        </div>
        {ranges.length>0&&<div style={{marginBottom:10}}>
          <div style={{fontSize:10,fontWeight:700,textTransform:"uppercase",color:"var(--txt3)",marginBottom:4}}>Indisponibilités enregistrées</div>
          {ranges.map((r,i)=>(
            <div key={i} style={{display:"flex",alignItems:"center",gap:8,padding:"6px 9px",border:"1px solid var(--border)",borderRadius:8,marginBottom:4,background:"var(--bg3)"}}>
              <span style={{flex:1,fontSize:12,color:"var(--txt)"}}>{"du "+offFr(r.du)+" au "+offFr(r.au)}</span>
              <button onClick={()=>onSave(ranges.filter((_,k)=>k!==i))} title="Réactiver sur ces dates"
                style={{fontSize:11,padding:"2px 9px",borderRadius:6,border:"1.5px solid #3fb950",background:"rgba(63,185,80,.10)",color:"#3fb950",fontWeight:800,cursor:"pointer"}}>▶ Réactiver</button>
            </div>))}
        </div>}
        <div style={{fontSize:10,fontWeight:700,textTransform:"uppercase",color:"var(--txt3)",marginBottom:4}}>{"Désactiver"+(ranges.length?" aussi":"")}</div>
        <div style={bt(mode===0)} onClick={()=>setMode(0)}>
          <input type="radio" checked={mode===0} readOnly style={{marginTop:2}}/>
          <div><div style={{fontSize:12,fontWeight:800,color:"var(--txt)"}}>Sur toute la période affichée</div>
            <div style={{fontSize:10.5,color:"var(--txt2)"}}>{"du "+offFr(du0)+" au "+offFr(au0)+" ("+perLbl+")"}</div></div>
        </div>
        <div style={bt(mode===1)} onClick={()=>setMode(1)}>
          <input type="radio" checked={mode===1} readOnly style={{marginTop:2}}/>
          <div><div style={{fontSize:12,fontWeight:800,color:"var(--txt)"}}>De date à date</div>
            <div style={{display:"flex",gap:6,alignItems:"center",marginTop:5,flexWrap:"wrap",fontSize:11,color:"var(--txt2)"}}>
              du <input type="date" value={d1} onChange={e=>setD1(e.target.value)} style={{...S.fi,width:132,padding:"3px 6px"}}/>
              au <input type="date" value={d2} onChange={e=>setD2(e.target.value)} style={{...S.fi,width:132,padding:"3px 6px"}}/>
            </div></div>
        </div>
        {nAct>0&&<div style={{border:"1px solid #ef4444",background:"rgba(239,68,68,.07)",borderRadius:8,padding:"7px 9px",margin:"2px 0 8px"}}>
          <div style={{fontSize:11.5,color:"#ef4444",fontWeight:700,marginBottom:5}}>{"⚠ "+nAct+" activité"+(nAct>1?"s":"")+" déjà posée"+(nAct>1?"s":"")+" sur ces dates (gardes, tour et absences comprises) — la désactivation ne les efface pas, elles resteraient sous les hachures."}</div>
          {onClear&&<button onClick={()=>onClear(rSel.du,rSel.au)}
            style={{fontSize:11,padding:"4px 12px",borderRadius:6,border:"1.5px solid #ef4444",background:"rgba(239,68,68,.10)",color:"#ef4444",fontWeight:800,cursor:"pointer"}}>🧹 Retirer ses activités sur ces dates</button>}
        </div>}
        <div style={{fontSize:10.5,color:"var(--txt3)",margin:"6px 0 10px"}}>Pendant ses dates : le planning type le saute et ses cases sont indisponibles. Sa fiche et son planning type sont conservés — il redevient disponible le jour de son retour.</div>
        <div style={{display:"flex",gap:6,flexWrap:"wrap"}}>
          <button onClick={ajouter} style={{fontSize:12,padding:"6px 14px",borderRadius:7,border:"1.5px solid #f59e0b",background:"rgba(245,158,11,.10)",color:"#b45309",fontWeight:800,cursor:"pointer"}}>⏸ Désactiver</button>
          <button onClick={onClose} style={{fontSize:12,padding:"6px 13px",borderRadius:7,border:"1px solid var(--border)",background:"var(--bg3)",color:"var(--txt2)",fontWeight:700,cursor:"pointer"}}>Fermer</button>
        </div>
      </div>
    </div>
  );
}

/* ═══════════ v10.59 — INTERNES, lots 1-3a : semestres et fiches (Équipe), coches d'activité, tuile Paramètres ═══════════
   Les internes ne vivent PAS dans la liste `medecins` : ils sont rangés par semestre dans intCfg.sems,
   pour ne jamais apparaître dans les filtres et listes des médecins. Leurs cases du planning utiliseront
   leurs identifiants ("I...") comme clés, exactement comme celles des médecins.
   Prise de fonction : le 2 mai et le 2 novembre, reportée au lundi suivant si elle tombe un ven/sam/dim.
   Les dates restent modifiables à la main pour affiner. */
const INT_COLS=["#2fbf9e","#f59e0b","#ec4899","#388bfd","#8b5cf6","#76a5af","#e3b341","#3fb950","#f97316","#64748b"];
function intISO(dt){return dt.getFullYear()+"-"+String(dt.getMonth()+1).padStart(2,"0")+"-"+String(dt.getDate()).padStart(2,"0");}
function intDecal(iso,n){const p=iso.split("-").map(Number);return intISO(new Date(p[0],p[1]-1,p[2]+n));}
function intSemLabel(deb){const p=deb.split("-").map(Number);const y=p[0],m=p[1];if(m>=5&&m<=10)return "Été "+y;return m>=11?("Hiver "+y+"-"+(y+1)):("Hiver "+(y-1)+"-"+y);}
function intSemsTri(cfg){return ((cfg&&cfg.sems)||[]).slice().sort((a,b)=>(a.deb<b.deb?-1:1));}
function intSemDuJour(cfg,iso){return intSemsTri(cfg).find(s=>s.deb<=iso&&iso<=s.fin)||null;}
function intFmtD(iso){const p=(iso||"").split("-");return p.length===3?(p[2]+"/"+p[1]+"/"+p[0]):iso;}
function intPrise(y,m){const d=new Date(y,m-1,2);const j=d.getDay();const dec=j===5?3:(j===6?2:(j===0?1:0));return intISO(new Date(y,m-1,2+dec));}
function intPrises(iso){const y=Number(iso.slice(0,4));const l=[];[y-1,y,y+1].forEach(yy=>{l.push(intPrise(yy,5));l.push(intPrise(yy,11));});return l;}
function intProchainePrise(iso){return intPrises(iso).find(p=>p>iso)||intDecal(iso,183);}
function intDernierePrise(iso){const l=intPrises(iso).filter(p=>p<=iso);return l.length?l[l.length-1]:iso;}

/* ═══════════ v10.95 — DOCTEURS JUNIORS : un nom par semestre ═══════════
   La fiche de l'onglet Équipe est le RÔLE (couleur, surspécialité, planning
   type, participations) ; ce sont le nom et les initiales du junior EN POSTE
   qui s'afficheront dans les onglets, semestre par semestre (lot 2).
   v10.88, SA CONSIGNE : les dates ne doivent PAS diverger de celles des
   internes. Les semestres sont donc LUS dans intCfg.sems — la liste qu'il
   règle déjà à la main dans l'onglet Équipe, bascule comprise. Le calcul
   (2 mai / 2 novembre reporté au lundi) ne sert plus que de repli quand
   aucun semestre n'existe encore. Une ligne junior porte l'ID du semestre ET
   sa date de début : l'ID survit à un déplacement de bascule, la date sert
   aux lignes écrites avant la v10.88 et au mode replié. */
const djL=(m)=>Array.isArray(m&&m.dj)?m.dj.filter(x=>x&&x.deb):[];
const djFin=(deb)=>intDecal(intProchainePrise(deb),-1);
/* pourvu = un nom, un prénom ou des initiales ; vide = personne sur ces dates */
const djPourvu=(x)=>!!(x&&(String(x.init||"").trim()||String(x.nom||"").trim()||String(x.prenom||"").trim()));
const djInit=(x)=>{
  const i=String((x&&x.init)||"").trim();
  if(i)return i.toUpperCase().slice(0,4);
  const p=String((x&&x.prenom)||"").trim(),n=String((x&&x.nom)||"").trim();
  return ((p?p[0]:"")+(n?n[0]:"")).toUpperCase();
};
const djNom=(x)=>((String((x&&x.prenom)||"")+" "+String((x&&x.nom)||"")).trim());
/* une fiche de RÔLE junior : identité allégée, noms saisis par semestre */
const djRole=(m)=>!!(m&&(m.role||"medecin")==="medecin"&&m.statut==="junior");
/* initiales internes d'un rôle (clé des activités autorisées) — jamais saisies */
const djAutoInit=(meds,selfId)=>{
  const pris=(meds||[]).filter(m=>m.id!==selfId).map(m=>String(m.init||"").toUpperCase());
  for(let i=1;i<200;i++){const c="J"+i;if(pris.indexOf(c)<0)return c;}
  return "J"+(Date.now()%1000);
};
/* LA liste des semestres : celle des internes, PROLONGÉE PAR LA RÈGLE au-delà
   du dernier enregistré jusqu'à couvrir `ref`.
   v10.91 : sans ce prolongement, une date postérieure au dernier semestre des
   internes n'appartenait à AUCUN semestre — donc ni nom substitué ni verrou :
   le rôle réapparaissait avec son code (J1, J2…) sur la période nov-février.
   Les semestres prolongés portent un identifiant "D<date>" : si le semestre
   interne correspondant est créé plus tard avec la bascule par défaut, la date
   de début coïncide et le nom déjà saisi est retrouvé. */
function djSemsList(intCfg,ref){
  const l=intSemsTri(intCfg);
  const out=l.length?l.map(s=>({id:s.id,deb:s.deb,fin:s.fin})):[];
  /* le repli s'ancre sur AUJOURD'HUI (pas sur `ref`) : sans quoi le début d'une
     période à cheval sur une bascule ne serait couvert par aucun semestre. */
  if(!out.length){const a=intDernierePrise(intISO(new Date()));out.push({id:"D"+a,deb:a,fin:djFin(a)});}
  let n=0;
  while(out[out.length-1].fin<ref&&n<24){
    const d=intDecal(out[out.length-1].fin,1);
    out.push({id:"D"+d,deb:d,fin:djFin(d)});
    n++;
  }
  return out;
}
const djTrouve=(m,s)=>djL(m).find(x=>(x.sem&&s.id&&x.sem===s.id)||x.deb===s.deb)||null;
/* le junior en poste à une date : null = personne, colonne masquée (lot 2) */
function djDuJour(m,iso,intCfg){
  const s=djSemsList(intCfg,iso).find(x=>x.deb<=iso&&iso<=x.fin);
  if(!s)return null;
  const x=djTrouve(m,s);
  return djPourvu(x)?x:null;
}
/* v10.88 : archivage — les lignes des semestres entièrement archivés partent.
   Sa consigne : « je ne peux pas rester avec une liste qui continue ».
   Rend la nouvelle liste, ou null s'il n'y a rien à retirer. */
function djPurgeMed(m,intCfg,lastMk){
  const l=djL(m);
  if(!l.length)return null;
  const sems=intSemsTri(intCfg);
  const g=l.filter(x=>{
    const s=sems.find(y=>y.id===x.sem||y.deb===x.deb);
    return String((s?s.fin:djFin(x.deb))||"").slice(0,7)>lastMk;
  });
  return g.length===l.length?null:g;
}

/* v10.89, SA DEMANDE : un rôle junior ne doit pas garder l'identité de son
   ancien titulaire (elle restait affichée sur la tuile de l'onglet Équipe).
   Le prénom est effacé et les initiales deviennent un CODE DE RÔLE (J1, J2…) ;
   le renommage de medecinsAutorise de la v9.52 suit tout seul à
   l'enregistrement, donc ni les activités autorisées ni le planning type
   (indexé par identifiant) ne bougent. */
const djCodeRole=(init,meds,selfId)=>{const t=String(init||"").trim().toUpperCase();return /^J\d+$/.test(t)?t:djAutoInit(meds,selfId);};
/* ligne grise sous le nom du rôle, sur la tuile de l'onglet Équipe */
function djTuileTxt(m,intCfg){
  const iso=intISO(new Date());
  const s=djSemsList(intCfg,iso).find(x=>x.deb<=iso&&iso<=x.fin);
  if(!s)return "Dr Junior";
  const x=djTrouve(m,s);
  return intSemLabel(s.deb)+" : "+(djPourvu(x)?(djNom(x)+" ("+djInit(x)+")"):"aucun nom saisi");
}

/* ═══ v10.90, LOT 2 : identité affichée et verrouillage des semestres vides ═══
   `medOffL` est appelé partout (grilles, tour, gardes, Construire, planning
   type) et n'a aucun moyen de recevoir intCfg : CardioPlanning dépose donc la
   liste des semestres ICI à chaque rendu, avant que les enfants ne s'en
   servent. Un rôle dont le semestre n'a pas de nom devient « indisponible »
   sur ces dates, et tout le mécanisme de la v10.40 s'applique tout seul :
   colonne masquée, cases hachurées et non cliquables, planning type qui
   saute, sortie du tour, des gardes et de Construire. */
let DJ_SEMS=[];
/* v10.94 : le registre va toujours DEUX ANS en avant. `djOffRanges` n'a aucune
   date en argument (medOffL non plus) : il ne peut verrouiller que les semestres
   PRÉSENTS dans le registre. Tant qu'il s'arrêtait à la période affichée, un rôle
   sans titulaire réapparaissait dès qu'on regardait plus loin — son constat du
   20/08 dans l'onglet Construire. */
function djSetSems(intCfg,jusqua){
  const loin=intDecal(intISO(new Date()),730);
  DJ_SEMS=djSemsList(intCfg,(jusqua&&jusqua>loin)?jusqua:loin);
}
function djOffRanges(m){
  if(!djRole(m))return [];
  const out=[];
  for(let i=0;i<DJ_SEMS.length;i++){const s=DJ_SEMS[i];if(!djPourvu(djTrouve(m,s)))out.push({du:s.deb,au:s.fin});}
  return out;
}
/* La liste affichée : le junior en poste à la date de référence prend le nom,
   le prénom et les initiales du rôle. Le CODE du rôle est conservé dans
   `initAuth` — c'est lui qui indexe les activités autorisées. */
function djSubst(meds,intCfg,refIso){
  if(!meds||!meds.some(m=>djRole(m)))return meds;
  return meds.map(m=>{
    if(!djRole(m))return m;
    const x=djDuJour(m,refIso,intCfg);
    if(!x)return m;
    return {...m,djRole0:{init:m.init,nom:m.nom,prenom:m.prenom},initAuth:m.init,init:djInit(x),nom:x.nom||m.nom,prenom:x.prenom||""};
  });
}
const authI=(m)=>(m&&m.initAuth)||(m&&m.init);

/* ═══ v10.92, LOT 3 : exactitude au JOUR ═══
   Le lot 2 substitue l'identité à UNE date de référence — c'est ce qu'il faut
   pour l'en-tête d'une colonne. Partout où une DATE existe (case, modale,
   infobulle, impression, historique), c'est elle qui doit décider et jamais la
   colonne : cliquer le 4 mai depuis avril montre le NOUVEAU junior, sa règle.
   `djAff` repart toujours de l'identité du RÔLE, gardée dans `djRole0` par la
   substitution du lot 2 — sans quoi on empilerait deux titulaires. */
const djBase=(m)=>(m&&m.djRole0)?{...m,init:m.djRole0.init,nom:m.djRole0.nom,prenom:m.djRole0.prenom}:m;
/* v10.93 : les semestres couvrant [d1,d2], PROLONGÉS PAR LA RÈGLE au-delà du
   registre. Le registre s'arrête au dernier jour de la période AFFICHÉE ; or
   l'onglet Construire travaille sur une période qu'il choisit librement, qui
   peut être plus loin. Sans ce prolongement, Construire retombait sur
   l'identité du rôle — ou pire, sur celle de la période affichée. */
function djSemsPour(d1,d2){
  const out=DJ_SEMS.filter(s=>!(s.fin<d1||s.deb>d2));
  let last=DJ_SEMS.length?DJ_SEMS[DJ_SEMS.length-1]:null;
  let n=0;
  while(last&&last.fin<d2&&n<24){
    const d=intDecal(last.fin,1);
    const c={id:"D"+d,deb:d,fin:djFin(d)};
    if(!(c.fin<d1||c.deb>d2))out.push(c);
    last=c;n++;
  }
  return out;
}
function djAff(m,iso){
  if(!djRole(m)||!iso)return m;
  const b=djBase(m);
  const s=djSemsPour(iso,iso)[0];
  const x=s?djTrouve(b,s):null;
  if(!djPourvu(x))return b;
  return {...b,djRole0:{init:b.init,nom:b.nom,prenom:b.prenom},initAuth:b.init,init:djInit(x),nom:x.nom||b.nom,prenom:x.prenom||""};
}
/* Les DEUX noms quand la période affichée contient une bascule — sa demande
   pour les congés de l'onglet Construire : il les recueille auprès des deux. */
function djNomsPeriode(m,jours){
  if(!djRole(m)||!jours||!jours.length)return null;
  const b=djBase(m);
  const a=jours[0],z=jours[jours.length-1];
  const d1=dKey(a.y,a.m,a.d),d2=dKey(z.y,z.m,z.d);
  const out=[];
  djSemsPour(d1,d2).forEach(s=>{
    const x=djTrouve(b,s);
    /* v10.94 : un semestre sans titulaire compte aussi — sur une période à
       cheval il doit VOIR qu'il n'y a personne pour la seconde moitié. */
    const n=djPourvu(x)?(djNom(x)||djInit(x)):"non pourvu";
    if(n&&out.indexOf(n)<0)out.push(n);
  });
  return out.length>1?out.join(" puis "):null;
}

/* ═══ v10.95, SA RÈGLE : un rôle junior = UNE personne sur toute la période ═══
   « je ne vais pas les différencier sur 2 lignes, sinon on compterait pour tout
   le monde sur 4 mois sauf les juniors qui auraient une période sur 2 mois ».
   Une seule ligne donc, portant les initiales des DEUX titulaires côte à côte
   quand la période contient une bascule, et le compte de semaines de tour ou de
   gardes de la période ENTIÈRE — l'algorithme répartit ensuite là où il y a le
   plus besoin, sans partage arbitraire en cas de nombre impair.
   Et ceux qui ne sont là AUCUN jour de la période sortent de la liste. */
function djListePeriode(meds,jours){
  if(!meds||!meds.length||!jours||!jours.length)return meds||[];
  const a=jours[0],z=jours[jours.length-1];
  const d1=dKey(a.y,a.m,a.d),d2=dKey(z.y,z.m,z.d);
  const sems=djSemsPour(d1,d2);
  return meds.filter(m=>offEtat(m,jours)!=="off").map(m=>{
    if(!djRole(m))return m;
    const b=djBase(m);
    const ini=[],noms=[];
    sems.forEach(s=>{
      const x=djTrouve(b,s);
      if(!djPourvu(x))return;
      const i=djInit(x);
      if(ini.indexOf(i)<0){ini.push(i);noms.push(djNom(x)||i);}
    });
    if(!ini.length)return b;
    return {...b,djRole0:{init:b.init,nom:b.nom,prenom:b.prenom},initAuth:b.init,
            init:ini.join("/"),nom:noms.join(" / "),prenom:"",_lib:noms.join(" puis ")};
  });
}

function DJEquipe({mData,setMData,countActs,onClear,prisInit,intCfg}){
  const tj=intISO(new Date());
  /* +190 jours : toujours dans le semestre SUIVANT, quel que soit le jour —
     la fiche propose donc toujours celui en cours et le prochain, même si le
     semestre des internes n'est pas encore créé. */
  const sems=djSemsList(intCfg,intDecal(tj,190));
  const propre=!intSemsTri(intCfg).length;   // repli : aucun semestre enregistré
  /* le comptage parcourt 6 mois de cases : on ne le refait que si l'état
     « pourvu / vide » d'un semestre change, pas à chaque frappe. */
  const sig=sems.map(s=>s.deb+(djPourvu(djTrouve(mData,s))?"1":"0")).join(",");
  const cnt=useMemo(()=>{
    const o={};
    sems.forEach(s=>{o[s.deb]=(countActs&&!djPourvu(djTrouve(mData,s)))?countActs(s.deb,s.fin):0;});
    return o;
  },[sig]);
  const maj=(s,patch)=>setMData(p=>{
    const l=djL(p).slice();
    const i=l.findIndex(x=>(x.sem&&s.id&&x.sem===s.id)||x.deb===s.deb);
    if(i<0)l.push({sem:s.id,deb:s.deb,nom:"",prenom:"",init:"",...patch});
    else l[i]={...l[i],sem:s.id,deb:s.deb,...patch};
    return {...p,dj:l};
  });
  const vider=(s)=>setMData(p=>({...p,dj:djL(p).filter(x=>!((x.sem&&s.id&&x.sem===s.id)||x.deb===s.deb))}));
  const chip=(col)=>({fontSize:9.5,fontWeight:800,padding:"1px 6px",borderRadius:9,border:"1px solid "+col,color:col,textTransform:"uppercase",letterSpacing:.3});
  const inp={...S.fi,padding:"4px 7px",fontSize:12};
  return(
    <div style={{marginTop:10,borderTop:"1px dashed var(--border)",paddingTop:8}}>
      <div style={{fontSize:10,fontWeight:800,color:"#8b5cf6",textTransform:"uppercase",letterSpacing:.5,marginBottom:2}}>🔁 Docteurs Juniors du rôle, semestre par semestre</div>
      <div style={{fontSize:10.5,color:"var(--txt3)",marginBottom:6}}>{propre
        ?"Aucun semestre enregistré : les dates ci-dessous suivent la règle habituelle (2 mai et 2 novembre, reportés au lundi). Dès que vous créez les semestres dans le bloc Internes de cet onglet, ce sont ces dates-là qui s'appliquent ici."
        :"Dates communes aux internes : elles se règlent dans le bloc Internes de cet onglet (bascule modifiable), jamais ici — les deux ne peuvent pas diverger."}</div>
      {sems.map(s=>{
        const x=djTrouve(mData,s)||{};
        const enCours=s.deb<=tj&&tj<=s.fin;
        const passe=s.fin<tj;
        const plein=djPourvu(x);
        const ini=djInit(x);
        const dbl=plein&&ini&&(prisInit||[]).indexOf(ini)>=0;
        const n=cnt[s.deb]||0;
        return(
          <div key={s.deb} style={{border:"1px solid "+(enCours?"#8b5cf6":"var(--border)"),borderRadius:8,padding:"7px 9px",marginBottom:6,background:enCours?"rgba(139,92,246,.07)":"var(--bg3)",opacity:passe?.72:1}}>
            <div style={{display:"flex",alignItems:"center",gap:6,marginBottom:5,flexWrap:"wrap"}}>
              <span style={{fontWeight:800,fontSize:12.5,color:"var(--txt)"}}>{intSemLabel(s.deb)}</span>
              <span style={chip(passe?"var(--txt3)":(enCours?"#8b5cf6":"#388bfd"))}>{passe?"terminé":(enCours?"en cours":"à venir")}</span>
              <span style={{fontSize:10.5,color:"var(--txt3)",flex:1}}>{intFmtD(s.deb)+" → "+intFmtD(s.fin)}</span>
              {plein&&<button type="button" onClick={()=>vider(s)} title="Effacer le nom de ce semestre"
                style={{fontSize:10.5,padding:"2px 8px",borderRadius:6,border:"1px solid var(--border)",background:"var(--bg2)",color:"var(--txt2)",fontWeight:700,cursor:"pointer"}}>🗑 Effacer</button>}
            </div>
            <div style={{display:"flex",gap:6,flexWrap:"wrap"}}>
              <input placeholder="Nom" value={x.nom||""} onChange={e=>maj(s,{nom:e.target.value})} style={{...inp,flex:"1 1 110px",minWidth:88}}/>
              <input placeholder="Prénom" value={x.prenom||""} onChange={e=>maj(s,{prenom:e.target.value})} style={{...inp,flex:"1 1 110px",minWidth:88}}/>
              <input placeholder="Init." value={x.init||""} onChange={e=>maj(s,{init:e.target.value.toUpperCase().slice(0,4)})} style={{...inp,width:66,flex:"0 0 66px",fontWeight:800,textAlign:"center"}}/>
            </div>
            {plein&&!String(x.init||"").trim()&&<div style={{fontSize:10,color:"var(--txt3)",marginTop:4}}>{"Initiales déduites du nom : "+(ini||"—")}</div>}
            {dbl&&<div style={{fontSize:10.5,color:"#b45309",fontWeight:700,marginTop:4}}>{"⚠ Les initiales "+ini+" sont déjà portées par un autre membre de l'équipe : les deux se ressembleront dans les tableaux."}</div>}
            {!plein&&<div style={{fontSize:10.5,color:"var(--txt3)",marginTop:4}}>Aucun nom : sur ces dates la colonne sera masquée et les cases verrouillées. Saisissez le nom AVANT d'appliquer le planning type, sinon il sautera ces mois.</div>}
            {n>0&&<div style={{border:"1px solid #ef4444",background:"rgba(239,68,68,.07)",borderRadius:8,padding:"6px 8px",marginTop:5}}>
              <div style={{fontSize:11,color:"#ef4444",fontWeight:700,marginBottom:onClear?4:0}}>{"⚠ "+n+" activité"+(n>1?"s":"")+" déjà posée"+(n>1?"s":"")+" sur ces dates (gardes, tour et absences comprises). Sans nom, elles restent enregistrées sous les cases verrouillées."}</div>
              {onClear&&<button type="button" onClick={()=>onClear(s.deb,s.fin)}
                style={{fontSize:11,padding:"4px 12px",borderRadius:6,border:"1.5px solid #ef4444",background:"rgba(239,68,68,.10)",color:"#ef4444",fontWeight:800,cursor:"pointer"}}>🧹 Retirer ces activités</button>}
            </div>}
          </div>
        );
      })}
    </div>
  );
}

function InternesEquipe({intCfg,setIntCfg,isEdit}){
  const [open,setOpen]=useState({});
  const [formSem,setFormSem]=useState(null);
  const [editId,setEditId]=useState(null);
  const [fNom,setFNom]=useState("");
  const [fInit,setFInit]=useState("");
  const [fCol,setFCol]=useState(INT_COLS[0]);
  const sems=intSemsTri(intCfg);
  const tj=intISO(new Date());
  const setSems=(fn)=>setIntCfg(p=>({...p,sems:fn(((p&&p.sems)||[]).slice())}));
  const majSem=(id,patch)=>setSems(l=>l.map(s=>s.id===id?{...s,...patch}:s));
  /* v10.70 : tous les internes n'ont pas acces aux activites A SALLE (consultations).
     Une coche par interne — l'activite continue de decider par sa coche 🎓, cette
     coche-ci dit seulement QUI peut y etre propose. */
  const majMed=(semId,medId,patch)=>setSems(l=>l.map(x=>x.id!==semId?x:{...x,meds:(x.meds||[]).map(m=>m.id===medId?{...m,...patch}:m)}));
  const addSem=()=>{
    const last=sems[sems.length-1];
    if(!last){const deb=intDernierePrise(tj);setSems(l=>l.concat([{id:"S"+Date.now(),deb:deb,fin:intDecal(intProchainePrise(deb),-1),meds:[]}]));return;}
    const deb=intProchainePrise(last.fin);
    setSems(l=>l.map(s=>s.id===last.id?{...s,fin:intDecal(deb,-1)}:s).concat([{id:"S"+Date.now(),deb:deb,fin:intDecal(intProchainePrise(deb),-1),meds:[]}]));
  };
  const setBascule=(i,val)=>{
    if(!val)return;
    const s=sems[i],prev=sems[i-1];
    if(prev&&val<=prev.deb){toast("La bascule doit être après le début du semestre précédent","warn");return;}
    if(val>=s.fin){toast("La bascule doit rester avant la fin du semestre","warn");return;}
    setSems(l=>l.map(x=>x.id===s.id?{...x,deb:val}:(prev&&x.id===prev.id?{...x,fin:intDecal(val,-1)}:x)));
  };
  const colLibre=(s,sauf)=>{const pris=(s.meds||[]).filter(m=>m.id!==sauf).map(m=>m.color);return INT_COLS.find(c=>pris.indexOf(c)<0)||INT_COLS[0];};
  const ouvreForm=(s)=>{setFormSem(s.id);setEditId(null);setFNom("");setFInit("");setFCol(colLibre(s,null));};
  const ouvreEdit=(s,m)=>{setFormSem(s.id);setEditId(m.id);setFNom(m.nom);setFInit(m.init);setFCol(m.color);};
  const fermeForm=()=>{setFormSem(null);setEditId(null);};
  const valideForm=(semId)=>{
    const nom=fNom.trim(),init=fInit.trim().toUpperCase();
    if(!nom||!init){toast("Nom et initiales requis","warn");return;}
    const s=sems.find(x=>x.id===semId);
    if(s&&(s.meds||[]).some(m=>m.init===init&&m.id!==editId)){toast("Initiales déjà prises dans ce semestre","warn");return;}
    if(editId){
      setSems(l=>l.map(x=>x.id!==semId?x:{...x,meds:(x.meds||[]).map(m=>m.id===editId?{...m,nom:nom,init:init,color:fCol}:m)}));
      fermeForm();return;
    }
    setSems(l=>l.map(x=>x.id!==semId?x:{...x,meds:(x.meds||[]).concat([{id:"I"+Date.now(),nom:nom,init:init,color:fCol}])}));
    setFNom("");setFInit("");
    if(s){const pris=(s.meds||[]).map(m=>m.color).concat([fCol]);setFCol(INT_COLS.find(c=>pris.indexOf(c)<0)||INT_COLS[0]);}
  };
  /* v10.86 : un semestre PAS ENCORE COMMENCE se supprime. Sans cela, une date de
     bascule mal saisie bloquait tout : la fin d'un semestre n'est modifiable que
     sur le DERNIER, et son debut ne peut pas passer avant le precedent. La fin du
     semestre precedent est recollee — sur le suivant s'il en reste un, sinon sur sa
     fin naturelle (veille de la prochaine prise de fonction). */
  const delSem=(i)=>{
    const s=sems[i],prev=sems[i-1],next=sems[i+1];
    const nM=(s.meds||[]).length;
    if(!confirm("Supprimer le semestre "+intSemLabel(s.deb)+" ("+intFmtD(s.deb)+" → "+intFmtD(s.fin)+")"+(nM?(" et ses "+nM+" interne(s)"):"")+" ? Les cases déjà posées dans le planning ne sont pas touchées."))return;
    const finPrev=prev?(next?intDecal(next.deb,-1):intDecal(intProchainePrise(prev.deb),-1)):null;
    setSems(l=>l.filter(x=>x.id!==s.id).map(x=>(prev&&x.id===prev.id&&finPrev)?{...x,fin:finPrev}:x));
  };
  const nFinis=sems.filter(s=>s.fin<tj).length;
  /* v10.86 : au plus DEUX semestres ouverts (celui en cours et le suivant) — sa
     regle : il ne connait les internes que 3 a 4 semaines avant leur arrivee. */
  const nOuv=sems.filter(s=>s.fin>=tj).length;
  return <div style={{marginBottom:18}}>
    <div style={{fontSize:10,fontWeight:700,color:"var(--txt3)",textTransform:"uppercase",letterSpacing:.5,marginBottom:7}}>🎓 Internes — par semestre</div>
    {sems.length===0&&<div style={{fontSize:12,color:"var(--txt3)",marginBottom:8}}>Aucun semestre saisi. Créez le premier pour y ranger les internes ; le suivant se préparera à l'avance et prendra le relais tout seul à la date de bascule.</div>}
    {sems.map((s,i)=>{
      const fini=s.fin<tj,futur=s.deb>tj,cours=!fini&&!futur;
      if(fini&&!open[s.id])return <div key={s.id} style={{...S.card,marginBottom:8,opacity:.62,cursor:"pointer"}} onClick={()=>setOpen(o=>({...o,[s.id]:true}))}>
        <span style={{fontWeight:700,fontSize:13,color:"var(--txt)"}}>▸ {intSemLabel(s.deb)} — terminé</span>
        <span style={{fontSize:11,color:"var(--txt3)",marginLeft:8}}>{(s.meds||[]).length} interne(s) · un clic déplie</span>
      </div>;
      return <div key={s.id} style={{...S.card,marginBottom:8}}>
        <div style={{display:"flex",alignItems:"center",gap:8,flexWrap:"wrap",marginBottom:8}}>
          <span style={{fontWeight:800,fontSize:13,color:"var(--txt)"}}>{intSemLabel(s.deb)}</span>
          <Chp bg={cours?"#dcfce7":futur?"#dbeafe":"#f0f2f7"} c={cours?"#15803d":futur?"#1d4ed8":"#64748b"}>{cours?"en cours":futur?"préparé":"terminé"}</Chp>
          {fini&&<button style={{...S.icnBtn,fontSize:10}} onClick={()=>setOpen(o=>({...o,[s.id]:false}))}>replier</button>}
          {futur&&isEdit&&<button title="Supprimer ce semestre — il n'a pas encore commencé" onClick={()=>delSem(i)}
            style={{...S.icnBtn,fontSize:10,marginLeft:"auto",borderColor:"#dc2626",color:"#dc2626",fontWeight:800}}>🗑 Supprimer ce semestre</button>}
        </div>
        <div style={{display:"flex",alignItems:"center",gap:6,flexWrap:"wrap",marginBottom:8,fontSize:12,color:"var(--txt2)"}}>
          <span>Du</span>
          {isEdit?<input type="date" value={s.deb} onChange={e=>{const v=e.target.value;if(!v)return;if(i===0){if(v<s.fin)majSem(s.id,{deb:v});else toast("Le début doit précéder la fin","warn");}else setBascule(i,v);}} style={{...S.fi,width:135}}/>:<b>{intFmtD(s.deb)}</b>}
          <span>au</span>
          {isEdit&&i===sems.length-1?<input type="date" value={s.fin} onChange={e=>{const v=e.target.value;if(v&&v>s.deb)majSem(s.id,{fin:v});}} style={{...S.fi,width:135}}/>:<b>{intFmtD(s.fin)}</b>}
          {i>0&&isEdit&&<span style={{fontSize:10,color:"var(--txt3)"}}>— changer ce début décale la fin du semestre précédent (une seule date de bascule)</span>}
          {i<sems.length-1&&<span style={{fontSize:10,color:"var(--txt3)"}}>— la fin est la veille du semestre suivant</span>}
        </div>
        <div style={{display:"flex",gap:6,flexWrap:"wrap",alignItems:"center"}}>
          {(s.meds||[]).map(m=><span key={m.id} title={isEdit?"Cliquer pour renommer ou changer la couleur":undefined} onClick={isEdit?(()=>ouvreEdit(s,m)):undefined} style={{display:"inline-flex",alignItems:"center",gap:6,background:m.color,color:"#fff",borderRadius:8,padding:"4px 10px",fontSize:12,fontWeight:800,cursor:isEdit?"pointer":"default",outline:editId===m.id?"2.5px solid var(--txt)":"none"}}>
            {isEdit
              ?<button onClick={e=>{e.stopPropagation();majMed(s.id,m.id,{salles:!m.salles});}} title={(m.salles?"Proposé":"Non proposé")+" dans les salles (CHL, CHB, PT Cardio, PT Angio) — cliquer pour changer"} style={{border:"none",background:"transparent",color:"#fff",cursor:"pointer",padding:0,fontSize:13,lineHeight:1,opacity:m.salles?1:.55}}>{m.salles?"☑":"☐"}</button>
              :(m.salles?<span title="Proposé dans les salles" style={{fontSize:12,lineHeight:1}}>☑</span>:null)}
            {m.init} · {m.nom}
            {isEdit&&<button onClick={e=>{e.stopPropagation();if(confirm("Retirer "+m.nom+" de ce semestre ? Ses cases passées du planning ne sont pas touchées."))setSems(l=>l.map(x=>x.id!==s.id?x:{...x,meds:(x.meds||[]).filter(y=>y.id!==m.id)}));}} style={{border:"none",background:"transparent",color:"#fff",fontWeight:900,cursor:"pointer",padding:0,fontSize:12}}>✕</button>}
          </span>)}
          {(s.meds||[]).length===0&&<span style={{fontSize:11,color:"var(--txt3)"}}>aucun interne pour l'instant</span>}
          {isEdit&&formSem!==s.id&&<button style={{...S.icnBtn,fontSize:11}} onClick={()=>ouvreForm(s)}>+ Ajouter un interne</button>}
        </div>
        {isEdit&&formSem===s.id&&<div style={{marginTop:9,display:"flex",gap:6,flexWrap:"wrap",alignItems:"center"}}>
          <input placeholder="Nom" value={fNom} onChange={e=>setFNom(e.target.value)} style={{...S.fi,width:150}}/>
          <input placeholder="Init." value={fInit} onChange={e=>setFInit(e.target.value)} style={{...S.fi,width:56}}/>
          {INT_COLS.filter(c=>(s.meds||[]).filter(m=>m.id!==editId).map(m=>m.color).indexOf(c)<0).concat(INT_COLS.filter(c=>(s.meds||[]).filter(m=>m.id!==editId).map(m=>m.color).indexOf(c)>=0)).map(c=>
            <button key={c} onClick={()=>setFCol(c)} title={c} style={{width:20,height:20,borderRadius:"50%",background:c,border:fCol===c?"2.5px solid var(--txt)":"2.5px solid transparent",cursor:"pointer",padding:0}}/>)}
          <button style={{...S.icnBtn,fontWeight:800,color:"#16a34a"}} onClick={()=>valideForm(s.id)}>{editId?"✓ Modifier":"✓ Ajouter"}</button>
          <button style={{...S.icnBtn}} onClick={fermeForm}>annuler</button>
        </div>}
      </div>;
    })}
    {isEdit&&<div style={{display:"flex",gap:8,flexWrap:"wrap",marginTop:2}}>
      <button disabled={nOuv>=2} title={nOuv>=2?"Deux semestres sont déjà ouverts (celui en cours et le suivant) — supprimez le semestre préparé pour en créer un autre":"Créer le semestre suivant"}
        style={{fontSize:11,padding:"3px 12px",borderRadius:6,border:"1.5px solid #16a34a",background:"rgba(22,163,74,.10)",color:"#16a34a",fontWeight:800,cursor:nOuv>=2?"not-allowed":"pointer",opacity:nOuv>=2?.4:1}}
        onClick={()=>{if(nOuv>=2)return;addSem();}}>+ Semestre suivant</button>
      {nFinis>0&&<button style={{fontSize:11,padding:"3px 12px",borderRadius:6,border:"1.5px solid #dc2626",background:"rgba(220,38,38,.08)",color:"#dc2626",fontWeight:800,cursor:"pointer"}} onClick={()=>{if(confirm(nFinis+" semestre(s) terminé(s) — supprimer leurs fiches ? Les cases passées du planning ne sont pas touchées."))setSems(l=>l.filter(s=>!(s.fin<tj)));}}>🗑 Supprimer les semestres terminés</button>}
    </div>}
    {isEdit&&nOuv>=2&&<div style={{fontSize:10,color:"var(--txt3)",marginTop:6}}>Deux semestres sont ouverts (celui en cours et le suivant) : c'est le maximum. Pour en préparer un autre, supprimez d'abord le semestre préparé (🗑 dans son cadre).</div>}
    {isEdit&&<div style={{fontSize:10,color:"var(--txt3)",marginTop:6}}>☑ devant un interne : il est proposé dans les modales des salles (CHL, CHB, PT Cardio, PT Angio) et les activités à salle lui sont proposées dans l'onglet Internes. Décoché : il n'apparaît pas dans ces listes — ce qui lui a déjà été posé reste en place et retirable.</div>}
    {isEdit&&<div style={{fontSize:10,color:"var(--txt3)",marginTop:6}}>Prise de fonction proposée : le 2 mai et le 2 novembre, reportée au lundi suivant quand elle tombe un vendredi, samedi ou dimanche. Les dates restent modifiables ci-dessus.</div>}
  </div>;
}

function InternesTile({intCfg,setIntCfg,actes=[],pins=[]}){
  const num=(v)=>Math.max(0,Math.min(9,parseInt(v||"0",10)||0));
  const maj=(patch)=>setIntCfg(p=>({...p,...patch}));
  const inp=(k,def)=><input type="number" min={0} max={9} value={intCfg[k]===undefined?def:intCfg[k]} onChange={e=>{const o={};o[k]=num(e.target.value);maj(o);}} style={{...S.fi,width:52,textAlign:"center"}}/>;
  return <div style={{...S.card,marginBottom:10}}>
    <div style={{fontWeight:700,fontSize:13,color:"var(--txt)",marginBottom:8}}>🎓 Internes</div>
    <label style={{display:"flex",alignItems:"center",gap:9,fontSize:12.5,fontWeight:700,marginBottom:4,cursor:"pointer"}}>
      <input type="checkbox" checked={intCfg.show===true} onChange={e=>maj({show:e.target.checked})} style={{width:15,height:15}}/>
      Afficher l'onglet Internes
    </label>
    <div style={{fontSize:11,color:"var(--txt3)",margin:"0 0 10px 24px"}}>Décoché : l'onglet disparaît de la barre. Aucune donnée n'est perdue, les fiches restent dans Équipe.</div>
    <label style={{display:"flex",alignItems:"center",gap:9,fontSize:12.5,fontWeight:700,marginBottom:10,cursor:"pointer"}}>
      <input type="checkbox" checked={intCfg.jaugeDef!==false} onChange={e=>maj({jaugeDef:e.target.checked})} style={{width:15,height:15}}/>
      Jauge visible par défaut dans l'onglet
    </label>
    <div style={{fontSize:12,color:"var(--txt2)",display:"flex",gap:6,alignItems:"center",flexWrap:"wrap",marginBottom:6}}>
      <span>Semaine : alerte si moins de</span>{inp("sHC",2)}<span>en HC ou moins de</span>{inp("sUS",2)}<span>en USIC</span>
    </div>
    <div style={{fontSize:12,color:"var(--txt2)",display:"flex",gap:6,alignItems:"center",flexWrap:"wrap",marginBottom:6}}>
      <span>Samedi matin : alerte si moins de</span>{inp("sSam",1)}<span>en HC</span>
    </div>
    <div style={{fontSize:11,color:"var(--txt3)"}}>0 = pas d'alerte pour ce compteur. La jauge s'appuiera sur ces seuils dans l'onglet Internes.</div>
    <div style={{marginTop:10,paddingTop:9,borderTop:"1px solid var(--border)"}}>
      <div style={{fontSize:12.5,fontWeight:700,color:"var(--txt)",marginBottom:3}}>🔑 Code des internes</div>
      <div style={{fontSize:11,color:"var(--txt3)",marginBottom:7}}>Un seul code, partagé par tous les internes. À la connexion, il ouvre l'onglet Internes et demande un prénom (pour savoir qui modifie quoi). Les onglets Planning, CHL, CHB, PT Cardio, PT Angio et Aide restent consultables, sans modification possible.</div>
      <div style={{display:"flex",gap:6,alignItems:"center",flexWrap:"wrap"}}>
        <input type="password" id="nintp" placeholder={intCfg.pin?"Code défini — nouveau code":"Définir le code"} style={{...S.fi,flex:1,minWidth:150,textAlign:"center",letterSpacing:4}}/>
        <button style={S.btnP} onClick={()=>{const v=(document.getElementById("nintp").value||"").trim();
          if(v.length<4){toast("Min 4 car.","warn");return;}
          if((pins||[]).filter(Boolean).indexOf(v)>=0){toast("Ce code est déjà utilisé par un autre rôle","warn");return;}
          setIntCfg(p=>({...p,pin:v}));document.getElementById("nintp").value="";toast("Code des internes mis à jour");}}>OK</button>
        {intCfg.pin&&<button style={{...S.icnBtn,fontSize:11}} onClick={()=>{setIntCfg(p=>({...p,pin:""}));toast("Code des internes supprimé — l'accès est fermé");}}>Supprimer</button>}
      </div>
      <div style={{fontSize:11,color:"var(--txt3)",marginTop:5}}>{intCfg.pin?("Code actuel : "+intCfg.pin):"Aucun code : les internes ne peuvent pas se connecter."}</div>
    </div>
    {(()=>{ /* v10.68 : SEULEMENT les colonnes du tableau 📊 — la disponibilité des
       activités se règle dans l'onglet Activités (coche 🎓), pas ici. */
      const off=intCfg.statsOff||[];
      const cols=[{id:"TOUR_HC",short:"HC",color:"#388bfd"},{id:"TOUR_USIC",short:"USIC",color:"#4285f4"}]
        .concat(actes.filter(a=>a.interneOk===true&&!a.isSystem&&!a.hasSalle&&ABS_IDS.indexOf(a.id)<0).map(a=>({id:a.id,short:a.short||a.label,color:a.color})));
      const bascule=(id)=>maj({statsOff:off.indexOf(id)>=0?off.filter(x=>x!==id):off.concat([id])});
      return <div style={{marginTop:10,paddingTop:9,borderTop:"1px solid var(--border)"}}>
        <div style={{fontSize:12.5,fontWeight:700,color:"var(--txt)",marginBottom:3}}>Colonnes des statistiques 📊</div>
        <div style={{fontSize:11,color:"var(--txt3)",marginBottom:7}}>Décochée : la colonne disparaît du tableau de statistiques de l'onglet Internes — rien d'autre ne change. Les gardes restent toujours affichées ; les activités disponibles pour les internes se règlent dans l'onglet Activités (coche 🎓).</div>
        <div style={{display:"flex",flexWrap:"wrap",gap:"5px 16px"}}>
          {cols.map(t=><label key={t.id} style={{display:"flex",alignItems:"center",gap:5,fontSize:11.5,fontWeight:600,color:"var(--txt)",cursor:"pointer"}}>
            <input type="checkbox" checked={off.indexOf(t.id)<0} onChange={()=>bascule(t.id)} style={{width:13,height:13}}/>
            <span style={{width:9,height:9,borderRadius:3,background:t.color,display:"inline-block",flexShrink:0}}/>
            {t.short}
          </label>)}
        </div>
      </div>;
    })()}
  </div>;
}

/* ── v10.58 (v10.57 revue) : LOT 2 après son test : la grille prend la MISE EN PAGE DU
   PLANNING des médecins (TableScroll, mêmes en-têtes figés, mêmes pastilles
   Badge, fonds week-end/aujourd'hui, trait des lundis), avec une barre de
   période figée en haut (‹ › mêmes périodes que les autres onglets). La modale
   reprend la présentation de celle des médecins : date en titre, pastille +
   nom + créneau, section Activités avec retrait, tuiles d'ajout à deux lignes.
   Le remplissage de semaine se choisit DANS la modale (plus de popup). Absence
   et FMC suivent le créneau (matin, après-midi ou journée) ; le repos de garde
   couvre toujours la journée. Le contenu posé sur la journée (repos, absence)
   s'affiche désormais dans la grille. */
function intISO2(y,m0,d){return y+"-"+String(m0+1).padStart(2,"0")+"-"+String(d).padStart(2,"0");}
function intTxt(bg){try{return hexToLum(bg)>0.35?"#111":"#fff";}catch(e){return "#fff";}}
function intActesTuiles(actes,sam,self){
  /* v10.68 : ce que l'onglet propose se règle UNIQUEMENT par la coche 🎓 de
     l'onglet Activités — le réglage de Paramètres ne concerne que les stats. */
  const hc={id:"TOUR_HC",short:"HC",label:sam?"Samedi matin":"Tour HC",color:"#388bfd"};
  if(sam)return [hc,{id:"ABSENCE",short:"ABS",label:"Absence / Congé",color:"#e06666"},{id:"FORMATION",short:"FMC",label:"Formation",color:"#a3e635"},{id:"REPOS_GARDE",short:"RG",label:"Repos de garde",color:"#ffe599"}];
  /* v10.69, lot 5 : self = un interne connecte avec le PIN interne — il ne voit
     que les activites cochees « posable par eux » (interneSelf). */
  const perso=actes.filter(a=>a.interneOk===true&&!a.isSystem&&!a.hasSalle&&ABS_IDS.indexOf(a.id)<0&&(!self||a.interneSelf===true)).map(a=>({id:a.id,short:a.short||a.label,label:a.label,color:a.color}));
  return [hc,{id:"TOUR_USIC",short:"USIC",label:"Tour USIC",color:"#4285f4"}].concat(perso)
    .concat([{id:"ABSENCE",short:"ABS",label:"Absence / Congé",color:"#e06666"},{id:"FORMATION",short:"FMC",label:"Formation",color:"#a3e635"},{id:"REPOS_GARDE",short:"RG",label:"Repos de garde",color:"#ffe599"}]);
}
function intJourBloque(getEntries,mid,y,m,d){
  return getEntries(mid,y,m,d,"JOUR").some(e=>e&&e.acteId&&(ABS_IDS.indexOf(e.acteId)>=0||e.acteId==="REPOS_GARDE"));
}
function intSlotProtege(getEntries,mid,y,m,d,sl){
  if(intJourBloque(getEntries,mid,y,m,d))return true;
  return getEntries(mid,y,m,d,sl).some(e=>e&&(e._blocked||(e.acteId&&(ABS_IDS.indexOf(e.acteId)>=0||e.acteId==="REPOS_GARDE"))));
}
function intGardeVeille(getEntries,mid,y,m,d){
  const v=intDecal(intISO2(y,m,d),-1).split("-").map(Number);
  return ["N","JOUR"].some(sl=>getEntries(mid,v[0],v[1]-1,v[2],sl).some(e=>e&&e.acteId==="GARDE"));
}

function InternesCellModal({med,y,m,d,slot0,onClose,actes,acteById,getEntries,setEntry,canSalle=false,salleReg=[],intSelf=false}){
  const [cren,setCren]=useState(slot0==="AM"?"AM":"M");
  const [per,setPer]=useState(null);
  const [pd1,setPd1]=useState(intISO2(y,m,d));
  const [pd2,setPd2]=useState(intISO2(y,m+1,0));
  const [pSel,setPSel]=useState(null);
  const [semQ,setSemQ]=useState(null);   /* lundi : {id,salle} en attente du choix semaine / créneau */
  const [salleQ,setSalleQ]=useState(null); /* v10.62 : activité à salle en attente du choix de salle */
  const iso=intISO2(y,m,d);
  const dw=dow(y,m,d);
  const sam=dw===6;
  const tuiles=intActesTuiles(actes,sam,intSelf);
  /* v10.62, lot Salles : activités à salle cochées 🎓 — posables ici par l'éditeur,
     un intermédiaire ou un cadre uniquement, jamais par les internes ni l'administratif.
     Le choix de salle est obligatoire, la salle s'affiche ensuite sur la pastille. */
  const tuilesSalle=(canSalle&&!sam&&med.salles===true)?actes.filter(a=>a.interneOk===true&&!a.isSystem&&a.hasSalle&&ABS_IDS.indexOf(a.id)<0).map(a=>({id:a.id,short:a.short||a.label,label:a.label,color:a.color,salles:a.salles||[],fixedSalle:a.fixedSalle||null})):[];
  const salleSite=(s)=>{const r=(salleReg||[]).find(x=>x.n===s);return r?(Array.isArray(r.s)?r.s.join("/"):r.s):"";};
  const mid=med.id;
  const dansSem=(iso2)=>iso2>=med.sDeb&&iso2<=med.sFin;
  /* v10.69 : ce qu'un interne connecte peut retirer lui-meme. Le reste (consultations
     posees par le service) reste VISIBLE mais sans croix. */
  const posable=(id)=>(!intSelf)||(["TOUR_HC","TOUR_USIC","ABSENCE","FORMATION","REPOS_GARDE"].indexOf(id)>=0)||(((acteById(id)||{}).interneSelf)===true);
  const contenu=[];
  (sam?["M"]:["M","AM"]).forEach(sl=>{
    getEntries(mid,y,m,d,sl).forEach(e=>{
      if(e&&e.acteId&&!e._blocked&&!e._fullDay)contenu.push({sl:sl,acteId:e.acteId,salle:e.salle||null});
    });
  });
  getEntries(mid,y,m,d,"JOUR").forEach(e=>{if(e&&e.acteId)contenu.push({sl:"JOUR",acteId:e.acteId});});
  const gardeV=intGardeVeille(getEntries,mid,y,m,d);
  const retire=(c)=>{setEntry(mid,y,m,d,c.sl,null);};
  const crenLbl=sam?"Samedi matin":(cren==="M"?"Matin":cren==="AM"?"Après-midi":"Journée");
  const cycleCren=()=>{if(sam)return;setCren(c=>c==="M"?"AM":c==="AM"?"J":"M");};
  const slotsDuCren=()=>cren==="J"?["M","AM"]:[cren];
  const poseCren=(acteId,salle)=>{
    const ent=()=>salle?{acteId:acteId,salle:salle}:{acteId:acteId};
    if(sam){setEntry(mid,y,m,d,"M",ent());toast("Posé — samedi matin");onClose();return;}
    if(cren==="J"){setEntry(mid,y,m,d,"M",ent());setEntry(mid,y,m,d,"AM",ent());}
    else setEntry(mid,y,m,d,cren,ent());
    toast("Posé");onClose();
  };
  const poseJour=(acteId)=>{
    setEntry(mid,y,m,d,"M",null);
    if(!sam)setEntry(mid,y,m,d,"AM",null);
    setEntry(mid,y,m,d,"JOUR",{acteId:acteId});
    toast((acteById(acteId)||{label:acteId}).label+" — journée");onClose();
  };
  const remplirSemaine=(acteId,salle)=>{
    const abs=acteId==="ABSENCE"||acteId==="FORMATION";
    let poses=0,sautes=0;
    for(let i=0;i<5;i++){
      const iso3=intDecal(iso,i);
      const p=iso3.split("-").map(Number);
      if(!dansSem(iso3)){sautes++;continue;}
      if(abs){ /* journées entières, comme l'écran de période — remplace, repos compris */
        setEntry(mid,p[0],p[1]-1,p[2],"M",null);setEntry(mid,p[0],p[1]-1,p[2],"AM",null);
        setEntry(mid,p[0],p[1]-1,p[2],"JOUR",{acteId:acteId});poses++;continue;
      }
      ["M","AM"].forEach(sl=>{
        if(intSlotProtege(getEntries,mid,p[0],p[1]-1,p[2],sl)){sautes++;return;}
        setEntry(mid,p[0],p[1]-1,p[2],sl,salle?{acteId:acteId,salle:salle}:{acteId:acteId});poses++;
      });
    }
    toast(abs?(poses+" journée(s) posée(s)"+(sautes?", "+sautes+" hors semestre":""))
             :(poses+" demi-journée(s) posée(s)"+(sautes?", "+sautes+" préservée(s) (repos, absence, FMC ou hors semestre)":"")));
    onClose();
  };
  const poseSimple=(acteId,salle)=>{
    if((acteId==="ABSENCE"||acteId==="FORMATION")&&!sam&&cren==="J"){poseJour(acteId);return;}
    poseCren(acteId,salle);
  };
  const clic=(acteId)=>{
    /* v10.60 : le lundi, TOUTE activité propose de remplir la semaine — sauf le repos de garde */
    if(acteId==="REPOS_GARDE"){poseJour(acteId);return;}
    if(acteId==="ABSENCE"||acteId==="FORMATION"){
      if(dw===1&&!sam){setSemQ({id:acteId,salle:null});return;}
      poseSimple(acteId);return;
    }
    if(intJourBloque(getEntries,mid,y,m,d)){toast("La journée porte une absence, une FMC ou un repos — retirez-les d'abord (croix ci-dessus)","warn");return;}
    if(dw===1&&!sam){setSemQ({id:acteId,salle:null});return;}
    poseCren(acteId);
  };
  const clicSalle=(t)=>{
    if(intJourBloque(getEntries,mid,y,m,d)){toast("La journée porte une absence, une FMC ou un repos — retirez-les d'abord (croix ci-dessus)","warn");return;}
    if(t.fixedSalle){poseCren(t.id,t.fixedSalle);return;}
    if(!(t.salles||[]).length){toast("Cette activité n'a pas de salle définie — réglez-la dans l'onglet Activités","warn");return;}
    setSalleQ(t);
  };
  /* v10.67 : les activités à salle se posent au créneau, jamais à la semaine — sa règle */
  const choisitSalle=(s)=>{
    const t=salleQ;setSalleQ(null);
    poseCren(t.id,s);
  };
  const appliquePeriode=()=>{
    if(!pSel){toast("Choisissez une tuile à appliquer","warn");return;}
    if(!pd1||!pd2||pd2<pd1){toast("Vérifiez les deux dates","warn");return;}
    let poses=0,sautes=0,it=pd1,n=0;
    while(it<=pd2&&n<92){
      n++;
      const p=it.split("-").map(Number);const yy=p[0],mm=p[1]-1,dd=p[2];
      const t=dow(yy,mm,dd);const fer=isFerie(yy,mm,dd);
      if(!dansSem(it)){sautes++;it=intDecal(it,1);continue;}
      if(pSel==="EFF"){
        const repos=getEntries(mid,yy,mm,dd,"JOUR").some(e=>e&&e.acteId==="REPOS_GARDE");
        if(repos&&intGardeVeille(getEntries,mid,yy,mm,dd)){sautes++;}
        else{setEntry(mid,yy,mm,dd,"M",null);setEntry(mid,yy,mm,dd,"AM",null);setEntry(mid,yy,mm,dd,"JOUR",null);poses++;}
      }else if(pSel==="ABSENCE"||pSel==="FORMATION"||pSel==="REPOS_GARDE"){
        setEntry(mid,yy,mm,dd,"M",null);setEntry(mid,yy,mm,dd,"AM",null);setEntry(mid,yy,mm,dd,"JOUR",{acteId:pSel});poses++;
      }else{
        if(t===0||t===6||fer){it=intDecal(it,1);continue;}
        ["M","AM"].forEach(sl=>{
          if(intSlotProtege(getEntries,mid,yy,mm,dd,sl)){sautes++;return;}
          setEntry(mid,yy,mm,dd,sl,{acteId:pSel});poses++;
        });
      }
      it=intDecal(it,1);
    }
    toast(poses+" élément(s) modifié(s)"+(sautes?", "+sautes+" sauté(s) (protégé ou hors semestre)":""));
    onClose();
  };
  const btnO={fontSize:11,padding:"5px 12px",borderRadius:7,border:"1.5px solid #1d4ed8",background:"rgba(29,78,216,.08)",color:"#1d4ed8",fontWeight:800,cursor:"pointer"};
  return <Ov onClose={onClose}>
    <div style={{minWidth:320,maxWidth:540}} onClick={e=>e.stopPropagation()}>
      <div style={S.mHd}>
        <div style={S.mTit2}>{JOURSL[dw]+" "+d+" "+MOIS[m]+" "+y}</div>
        <button onClick={onClose} style={S.xBtn}>×</button>
      </div>
      <div style={{display:"flex",alignItems:"center",gap:7,marginBottom:10,fontSize:12.5}}>
        <span style={{display:"inline-flex",width:24,height:24,borderRadius:"50%",background:med.color,color:"#fff",fontSize:9,fontWeight:800,alignItems:"center",justifyContent:"center"}}>{med.init}</span>
        <span style={{fontWeight:700,color:"var(--txt)"}}>{med.nom}</span>
        <span style={{color:"var(--txt3)"}}>·</span>
        <button onClick={cycleCren} title={sam?undefined:"Changer de créneau"} style={{border:"none",background:"transparent",color:"#388bfd",fontWeight:800,fontSize:12.5,cursor:sam?"default":"pointer",padding:0}}>{crenLbl}{sam?"":" ▾"}</button>
      </div>
      {contenu.length>0&&<div style={{marginBottom:10}}>
        <div style={{fontSize:10,fontWeight:800,color:"var(--txt3)",textTransform:"uppercase",letterSpacing:.4,marginBottom:5}}>Activités</div>
        {contenu.map((c,i)=>{
          const a=acteById(c.acteId)||{short:c.acteId,color:"#8b949e",label:c.acteId};
          const reposAuto=c.acteId==="REPOS_GARDE"&&gardeV;
          return <div key={i} style={{display:"flex",alignItems:"center",gap:7,marginBottom:4,fontSize:12}}>
            <span style={{background:a.color,color:intTxt(a.color),borderRadius:4,padding:"2px 8px",fontSize:10,fontWeight:800,fontFamily:"'JetBrains Mono',monospace"}}>{a.short}</span>
            <span style={{fontSize:10,color:"var(--txt3)"}}>{c.sl==="JOUR"?"journée":c.sl==="M"?"matin":"après-midi"}</span>
            {c.salle&&<span style={{fontSize:9,fontWeight:800,fontFamily:"'JetBrains Mono',monospace",border:"1px solid var(--border)",background:"var(--bg)",color:"var(--txt2)",borderRadius:4,padding:"1px 5px"}}>{c.salle}</span>}
            {reposAuto
              ?<span style={{fontSize:10,color:"var(--txt3)"}}>posé par la garde de la veille — retirez la garde pour l'enlever</span>
              :!posable(c.acteId)?<span style={{fontSize:10,color:"var(--txt3)"}}>posé par le service</span>
              :<button onClick={()=>retire(c)} style={{width:18,height:18,borderRadius:9,border:"1px solid #fecdd3",background:"#fff1f2",color:"#dc2626",fontSize:10,fontWeight:800,cursor:"pointer",lineHeight:1,padding:0}}>×</button>}
          </div>;
        })}
      </div>}
      {semQ&&<div style={{border:"1.5px solid #388bfd",background:"rgba(56,139,253,.07)",borderRadius:9,padding:"10px 12px",marginBottom:10}}>
        <div style={{fontSize:12.5,fontWeight:800,color:"var(--txt)",marginBottom:3}}>{"Lundi + "+((acteById(semQ.id)||{}).short||semQ.id)+(semQ.salle?" ("+semQ.salle+")":"")+" : remplir toute la semaine ?"}</div>
        <div style={{fontSize:11,color:"var(--txt2)",marginBottom:8}}>{(semQ.id==="ABSENCE"||semQ.id==="FORMATION")
          ?"Journées entières du lundi au vendredi — remplace ce qui s\u2019y trouve, repos de garde compris. Les jours hors semestre sont sautés."
          :"Du lundi au vendredi, matin et après-midi. Les repos de garde, absences et FMC déjà posés sont préservés."}</div>
        <div style={{display:"flex",gap:6,flexWrap:"wrap"}}>
          <button onClick={()=>remplirSemaine(semQ.id,semQ.salle)} style={{fontSize:12,padding:"7px 13px",borderRadius:7,border:"none",background:"#1d4ed8",color:"#fff",fontWeight:800,cursor:"pointer"}}>📅 Toute la semaine</button>
          <button onClick={()=>{const a=semQ;setSemQ(null);poseSimple(a.id,a.salle);}} style={btnO}>{"Seulement "+crenLbl.toLowerCase()}</button>
          <button onClick={()=>setSemQ(null)} style={{...S.icnBtn,fontSize:11}}>annuler</button>
        </div>
      </div>}
      {per===null&&!semQ&&<div>
        <div style={{fontSize:10,fontWeight:800,color:"var(--txt3)",textTransform:"uppercase",letterSpacing:.4,marginBottom:5}}>Ajouter</div>
        {!salleQ&&<div style={{display:"grid",gridTemplateColumns:"1fr 1fr",gap:7,marginBottom:10}}>
          {tuiles.map(t=>{
            const j=t.id==="REPOS_GARDE";
            return <button key={t.id} onClick={()=>clic(t.id)} style={{padding:"9px 11px",borderRadius:9,border:"none",cursor:"pointer",textAlign:"left",background:t.color,color:intTxt(t.color)}}>
              <span style={{display:"block",fontSize:11,fontWeight:800,fontFamily:"'JetBrains Mono',monospace"}}>{t.short}</span>
              <span style={{display:"block",fontSize:11.5,fontWeight:700}}>{t.label}{j?" · journée":""}</span>
            </button>;
          })}
        </div>}
        {tuilesSalle.length>0&&!salleQ&&<div style={{marginBottom:10}}>
          <div style={{fontSize:10,fontWeight:800,color:"var(--txt3)",textTransform:"uppercase",letterSpacing:.4,marginBottom:5}}>Avec salle</div>
          <div style={{display:"grid",gridTemplateColumns:"1fr 1fr",gap:7}}>
            {tuilesSalle.map(t=>
              <button key={t.id} onClick={()=>clicSalle(t)} style={{padding:"9px 11px",borderRadius:9,border:"none",cursor:"pointer",textAlign:"left",background:t.color,color:intTxt(t.color)}}>
                <span style={{display:"block",fontSize:11,fontWeight:800,fontFamily:"'JetBrains Mono',monospace"}}>{t.short}</span>
                <span style={{display:"block",fontSize:11.5,fontWeight:700}}>{t.label} · salle…</span>
              </button>)}
          </div>
        </div>}
        {salleQ&&<div style={{border:"1.5px solid #1d4ed8",background:"rgba(29,78,216,.06)",borderRadius:9,padding:"10px 12px",marginBottom:10}}>
          <div style={{fontSize:12.5,fontWeight:800,color:"var(--txt)",marginBottom:6}}>{(salleQ.short||salleQ.id)+" — choisir la salle"}</div>
          {(()=>{
            const grpsS=[];
            (salleQ.salles||[]).forEach(s=>{const st=salleSite(s)||"Autres";let g=grpsS.find(x=>x.st===st);if(!g){g={st:st,l:[]};grpsS.push(g);}g.l.push(s);});
            return grpsS.map(g=><div key={g.st} style={{marginBottom:6}}>
              {grpsS.length>1&&<div style={{fontSize:9,fontWeight:800,color:"var(--txt3)",textTransform:"uppercase",marginBottom:3}}>{g.st==="ANGIO"?"PT Angio":g.st}</div>}
              <div style={{display:"flex",flexWrap:"wrap",gap:5}}>
                {g.l.map(s=><button key={s} onClick={()=>choisitSalle(s)} style={{padding:"5px 10px",borderRadius:5,border:"1px solid var(--border)",cursor:"pointer",fontFamily:"'JetBrains Mono',monospace",fontSize:11,fontWeight:700,background:"var(--bg2)",color:"var(--txt)"}}>{s}</button>)}
              </div>
            </div>);
          })()}
          <button onClick={()=>setSalleQ(null)} style={{...S.icnBtn,fontSize:11}}>annuler</button>
        </div>}
        {sam&&<div style={{fontSize:10,color:"var(--txt3)",marginBottom:8}}>Samedi : une seule case — le HC se pose sur le matin.</div>}
        {!salleQ&&<button onClick={()=>setPer(1)} style={{...btnO,width:"100%",textAlign:"center",padding:"7px"}}>📅 Modifier sur une période…</button>}
      </div>}
      {per!==null&&<div>
        <div style={{display:"flex",gap:6,alignItems:"center",flexWrap:"wrap",marginBottom:8,fontSize:12,color:"var(--txt2)"}}>
          <span>Du</span><input type="date" value={pd1} onChange={e=>{if(e.target.value)setPd1(e.target.value);}} style={{...S.fi,width:135}}/>
          <span>au</span><input type="date" value={pd2} onChange={e=>{if(e.target.value)setPd2(e.target.value);}} style={{...S.fi,width:135}}/>
          <button onClick={()=>{const l=intDecal(intISO2(y,m,d),-((dow(y,m,d)+6)%7));setPd1(l);setPd2(intDecal(l,6));}} style={{...S.icnBtn,fontSize:10}}>la semaine</button>
          <button onClick={()=>{setPd1(intISO2(y,m,1));setPd2(intISO2(y,m+1,0));}} style={{...S.icnBtn,fontSize:10}}>le mois</button>
        </div>
        <div style={{display:"grid",gridTemplateColumns:"1fr 1fr",gap:6,marginBottom:8}}>
          {intActesTuiles(actes,false,intSelf).map(t=>
            <button key={t.id} onClick={()=>setPSel(t.id)} style={{padding:"7px 10px",borderRadius:8,cursor:"pointer",textAlign:"left",background:t.color,color:intTxt(t.color),border:pSel===t.id?"2.5px solid var(--txt)":"2.5px solid transparent"}}>
              <span style={{display:"block",fontSize:10.5,fontWeight:800,fontFamily:"'JetBrains Mono',monospace"}}>{t.short}</span>
              <span style={{display:"block",fontSize:11,fontWeight:700}}>{t.label}</span>
            </button>)}
          {!intSelf&&<button onClick={()=>setPSel("EFF")} style={{padding:"7px 10px",borderRadius:8,cursor:"pointer",fontWeight:800,fontSize:12,background:"var(--bg2)",color:"var(--txt2)",border:pSel==="EFF"?"2.5px solid var(--txt)":"2.5px solid var(--border)"}}>🧹 Effacer</button>}
        </div>
        <div style={{fontSize:10,color:"var(--txt3)",marginBottom:8,lineHeight:1.5}}>
          HC, USIC et les activités se posent du lundi au vendredi (matin + après-midi), en préservant repos, absences et FMC. Absence, FMC et repos couvrent chaque journée de la période. Les activités à salle ne se posent pas ici. Un repos issu d'une garde posée dans l'application n'est jamais effacé.
        </div>
        <div style={{display:"flex",gap:6}}>
          <button onClick={appliquePeriode} style={{flex:1,padding:"8px",borderRadius:8,border:"none",background:"#1d4ed8",color:"#fff",fontWeight:800,fontSize:12,cursor:"pointer"}}>✓ Appliquer</button>
          <button onClick={()=>setPer(null)} style={{...S.icnBtn,fontSize:11,padding:"8px 12px"}}>‹ Retour</button>
        </div>
      </div>}
    </div>
  </Ov>;
}

/* ── v10.59, LOT 3a : LA COLONNE DE GARDE de l'onglet Internes ──
   Une garde par jour, posée UNIQUEMENT depuis cette colonne (pas de tuile garde
   dans la modale de case). Poser une garde pose le REPOS le lendemain (journée,
   en remplaçant ce qui s'y trouve) ; si le lendemain porte une absence ou une
   FMC, la garde est posée SANS repos avec une alerte (règle validée) ; retirer
   la garde retire le repos. Garde EXTÉRIEURE : un nom libre, hors liste, sans
   repos chez nous (clé de plan "IEXT", jamais listée ailleurs). Un jour sans
   interne de garde : case ROUGE. Bloc ⇄ Échanger entre deux jours. La colonne
   « Garde int. » du Planning viendra au lot suivant (3b), puis les salles, la
   jauge et les statistiques, et le PIN. */
function intGardeDuJour(getEntries,intCfg,y,m,d){
  const sems=(intCfg&&intCfg.sems)||[];
  for(let i=0;i<sems.length;i++){
    const l=sems[i].meds||[];
    for(let k=0;k<l.length;k++){
      if(getEntries(l[k].id,y,m,d,"N").some(e=>e&&e.acteId==="GARDE"))return {med:l[k],sDeb:sems[i].deb,sFin:sems[i].fin};
    }
  }
  const ex=getEntries("IEXT",y,m,d,"N").find(e=>e&&e.acteId==="GARDE");
  if(ex)return {ext:ex.ext||"Ext."};
  return null;
}
function intAbsCeJour(getEntries,mid,y,m,d){
  return ["M","AM","JOUR"].some(sl=>getEntries(mid,y,m,d,sl).some(e=>e&&e.acteId&&ABS_IDS.indexOf(e.acteId)>=0));
}
/* v10.62, lot Salles : les internes du semestre couvrant un jour donné — sert aux
   modales des 4 onglets salles et à l'affichage des occupants dans leurs grilles. */
function intMedsDuJour(intCfg,y,m,d){
  const s=intCfg?intSemDuJour(intCfg,intISO2(y,m,d)):null;
  return (s&&(s.meds||[]).length)?{lbl:intSemLabel(s.deb),meds:s.meds}:null;
}
/* v10.65, lot 4 : jauge par demi-journée — comptes HC et USIC séparés parmi les
   internes dont le semestre couvre le jour (variante 2 validée). Un interne dont
   le créneau porte les deux ne compte qu'une fois, côté HC. */
function intJauge(getEntries,cols,y,m,d,sl){
  let hc=0,us=0;
  const iso=intISO2(y,m,d);
  cols.forEach(c=>{
    if(!(iso>=c.sDeb&&iso<=c.sFin))return;
    const es=(getEntries(c.id,y,m,d,sl)||[]).filter(e=>e&&e.acteId&&!e._blocked);
    if(es.some(e=>e.acteId==="TOUR_HC"))hc++;
    else if(es.some(e=>e.acteId==="TOUR_USIC"))us++;
  });
  return {hc:hc,us:us};
}
/* v10.66 : catégorie d'un jour de garde — même règle que le tableau des médecins
   (férié = dimanche, veille de férié = vendredi). */
function intCatGarde(y,m,d){
  if(isFerie(y,m,d))return "dim";
  const dw=dow(y,m,d);
  if(dw===6)return "sam";
  if(dw===0)return "dim";
  const nx=new Date(y,m,d+1);
  if(isFerie(nx.getFullYear(),nx.getMonth(),nx.getDate()))return "ven";
  return dw===5?"ven":dw===4?"jeu":"sem";
}
/* v10.65, revu v10.66 : statistiques par interne sur une liste de jours — gardes
   posées (total + par catégorie, comme le tableau des médecins), puis demi-journées
   de HC, d'USIC et de chaque activité de la liste extras. */
const GCATS_INT=["sem","jeu","ven","sam","dim"];
function intStats(getEntries,cols,jours,extras){
  const st={};
  cols.forEach(c=>{st[c.id]={gardes:0,cat:{sem:0,jeu:0,ven:0,sam:0,dim:0},hc:0,us:0,ex:{}};extras.forEach(a=>{st[c.id].ex[a.id]=0;});});
  jours.forEach(o=>{
    const iso=intISO2(o.y,o.m,o.d);
    const dedans=cols.filter(c=>iso>=c.sDeb&&iso<=c.sFin);
    if(!dedans.length)return;
    const t=dow(o.y,o.m,o.d),fer=isFerie(o.y,o.m,o.d);
    const off=t===0||fer,sam=!off&&t===6;
    const slots=off?[]:sam?["M"]:["M","AM"];
    dedans.forEach(c=>{
      if((getEntries(c.id,o.y,o.m,o.d,"N")||[]).some(e=>e&&e.acteId==="GARDE")){st[c.id].gardes++;st[c.id].cat[intCatGarde(o.y,o.m,o.d)]++;}
      slots.forEach(sl=>{
        const es=(getEntries(c.id,o.y,o.m,o.d,sl)||[]).filter(e=>e&&e.acteId&&!e._blocked);
        if(es.some(e=>e.acteId==="TOUR_HC"))st[c.id].hc++;
        else if(es.some(e=>e.acteId==="TOUR_USIC"))st[c.id].us++;
        extras.forEach(a=>{if(es.some(e=>e.acteId===a.id))st[c.id].ex[a.id]++;});
      });
    });
  });
  return st;
}

function InternesGardeModal({y,m,d,jours,onClose,intCfg,getEntries,setEntry}){
  const [exOpen,setExOpen]=useState(false);
  const [extNom,setExtNom]=useState("");
  const iso=intISO2(y,m,d);
  const holder=intGardeDuJour(getEntries,intCfg,y,m,d);
  const sem=intSemDuJour(intCfg,iso);
  const eligibles=(sem?(sem.meds||[]):[]).map(mm=>({...mm,sDeb:sem.deb,sFin:sem.fin}));
  const retire=(yy,mm,dd)=>{
    const h=intGardeDuJour(getEntries,intCfg,yy,mm,dd);
    if(!h)return null;
    if(h.ext){setEntry("IEXT",yy,mm,dd,"N",null);return h;}
    setEntry(h.med.id,yy,mm,dd,"N",null);
    const L=intDecal(intISO2(yy,mm,dd),1).split("-").map(Number);
    if(getEntries(h.med.id,L[0],L[1]-1,L[2],"JOUR").some(e=>e&&e.acteId==="REPOS_GARDE"))setEntry(h.med.id,L[0],L[1]-1,L[2],"JOUR",null);
    return h;
  };
  const pose=(h,yy,mm,dd,silencieux)=>{
    if(h.ext){setEntry("IEXT",yy,mm,dd,"N",{acteId:"GARDE",ext:h.ext});return;}
    const md=h.med;
    setEntry(md.id,yy,mm,dd,"N",{acteId:"GARDE"});
    const iso1=intDecal(intISO2(yy,mm,dd),1);
    const L=iso1.split("-").map(Number);
    if(h.sDeb&&(iso1<h.sDeb||iso1>h.sFin)){if(!silencieux)toast("Garde posée — le lendemain sort de son semestre, pas de repos posé","info");return;}
    if(intAbsCeJour(getEntries,md.id,L[0],L[1]-1,L[2])){toast("⚠ "+md.init+" est absent ou en FMC le lendemain : garde posée SANS repos","warn");return;}
    setEntry(md.id,L[0],L[1]-1,L[2],"M",null);
    setEntry(md.id,L[0],L[1]-1,L[2],"AM",null);
    setEntry(md.id,L[0],L[1]-1,L[2],"JOUR",{acteId:"REPOS_GARDE"});
    if(!silencieux)toast("Garde posée — repos le "+intFmtD(iso1));
  };
  const choisir=(md)=>{retire(y,m,d);pose({med:md,sDeb:md.sDeb,sFin:md.sFin},y,m,d,false);onClose();};
  const poseExt=()=>{
    const n=extNom.trim();
    if(!n){toast("Saisissez le nom de l'interne extérieur","warn");return;}
    retire(y,m,d);pose({ext:n},y,m,d,false);
    toast("Garde extérieure posée — sans repos chez nous");onClose();
  };
  /* v10.60 : échange sur le modèle des médecins (v9.82) — la liste des gardes posées
     de la période affichée, un clic pour échanger, plus de date à saisir. Un absent
     n'est pas bloqué (règle interne validée) ; les repos sont recalculés par retire/pose. */
  const swap=(o,h2)=>{
    retire(y,m,d);retire(o.y,o.m,o.d);
    pose(h2,y,m,d,true);
    pose(holder,o.y,o.m,o.d,true);
    toast("Gardes échangées");onClose();
  };
  const autresGardes=(jours||[]).map(o=>{
    if(o.y===y&&o.m===m&&o.d===d)return null;
    const h2=intGardeDuJour(getEntries,intCfg,o.y,o.m,o.d);
    if(!h2)return null;
    if(h2.med&&holder&&holder.med&&h2.med.id===holder.med.id)return null;
    return {o:o,h:h2};
  }).filter(Boolean);
  const nomH=(h)=>h?(h.ext?(h.ext+" (extérieur)"):(h.med.init+" · "+h.med.nom)):"personne";
  return <Ov onClose={onClose}>
    <div style={{minWidth:320,maxWidth:520}} onClick={e=>e.stopPropagation()}>
      <div style={S.mHd}>
        <div style={S.mTit2}>{"🌙 Garde — "+JOURSL[dow(y,m,d)]+" "+d+" "+MOIS[m]+" "+y}</div>
        <button onClick={onClose} style={S.xBtn}>×</button>
      </div>
      <div style={{display:"flex",alignItems:"center",gap:8,marginBottom:10,fontSize:12.5,flexWrap:"wrap"}}>
        {holder
          ?<span style={{display:"inline-flex",alignItems:"center",gap:7}}>
            {holder.med&&<span style={{display:"inline-flex",width:24,height:24,borderRadius:"50%",background:holder.med.color,color:"#fff",fontSize:9,fontWeight:800,alignItems:"center",justifyContent:"center"}}>{holder.med.init}</span>}
            <span style={{fontWeight:700,color:"var(--txt)"}}>{nomH(holder)}</span>
            <button onClick={()=>{retire(y,m,d);toast("Garde retirée — le repos du lendemain aussi");onClose();}} style={{fontSize:10,padding:"3px 9px",borderRadius:6,border:"1px solid #fecdd3",background:"#fff1f2",color:"#dc2626",fontWeight:800,cursor:"pointer"}}>✕ Retirer la garde</button>
          </span>
          :<span style={{fontWeight:800,color:"#dc2626",fontSize:12}}>Aucun interne de garde ce jour</span>}
      </div>
      <div style={{fontSize:10,fontWeight:800,color:"var(--txt3)",textTransform:"uppercase",letterSpacing:.4,marginBottom:5}}>{sem?("Internes — "+intSemLabel(sem.deb)):"Internes"}</div>
      {eligibles.length===0&&<div style={{fontSize:11,color:"var(--txt3)",marginBottom:8}}>Aucun semestre ne couvre ce jour — saisissez-le dans Équipe.</div>}
      <div style={{display:"grid",gridTemplateColumns:"1fr 1fr",gap:6,marginBottom:10}}>
        {eligibles.map(md=>{
          const absJ=intAbsCeJour(getEntries,md.id,y,m,d);
          const L=intDecal(iso,1).split("-").map(Number);
          const absL=intAbsCeJour(getEntries,md.id,L[0],L[1]-1,L[2]);
          const cur=holder&&holder.med&&holder.med.id===md.id;
          return <button key={md.id} onClick={()=>choisir(md)} style={{display:"flex",alignItems:"center",gap:7,padding:"7px 9px",borderRadius:8,cursor:"pointer",textAlign:"left",
            border:"2px solid "+(cur?"#16a34a":"var(--border2)"),background:cur?"rgba(22,163,74,.10)":"var(--bg)",opacity:absJ?.6:1}}>
            <span style={{display:"inline-flex",width:24,height:24,borderRadius:"50%",background:md.color,color:"#fff",fontSize:9,fontWeight:800,alignItems:"center",justifyContent:"center",flexShrink:0}}>{md.init}</span>
            <span style={{flex:1,minWidth:0}}>
              <span style={{display:"block",fontSize:12,fontWeight:700,color:"var(--txt)",overflow:"hidden",textOverflow:"ellipsis",whiteSpace:"nowrap"}}>{md.nom}</span>
              {(absJ||absL)&&<span style={{display:"block",fontSize:9,color:"#b45309",fontWeight:700}}>{absJ?"absent / FMC ce jour":""}{absJ&&absL?" · ":""}{absL?"⚠ demain absent : sans repos":""}</span>}
            </span>
          </button>;
        })}
      </div>
      <div style={{display:"flex",gap:6,alignItems:"center",flexWrap:"wrap",marginBottom:10,padding:"8px 10px",borderRadius:8,border:"1px dashed var(--border)",background:"var(--bg2)"}}>
        <span style={{fontSize:11,fontWeight:800,color:"var(--txt2)"}}>Interne extérieur :</span>
        <input placeholder="Nom" value={extNom} onChange={e=>setExtNom(e.target.value)} style={{...S.fi,width:150}}/>
        <button onClick={poseExt} style={{fontSize:11,padding:"5px 11px",borderRadius:6,border:"1.5px solid #64748b",background:"rgba(100,116,139,.10)",color:"var(--txt2)",fontWeight:800,cursor:"pointer"}}>Poser</button>
      </div>
      {holder&&<button onClick={()=>setExOpen(v=>!v)} style={{width:"100%",padding:"6px",borderRadius:6,border:"1.5px solid #388bfd",background:"rgba(56,139,253,.10)",color:"#388bfd",fontWeight:800,cursor:"pointer",fontSize:11,marginBottom:8}}>⇄ Échanger cette garde…</button>}
      {holder&&exOpen&&<div style={{marginBottom:8,padding:"8px 10px",borderRadius:8,border:"1.5px solid #388bfd",background:"rgba(56,139,253,.05)"}}>
        <div style={{fontSize:11,fontWeight:800,color:"#388bfd",marginBottom:6}}>{"⇄ Échanger la garde de "+(holder.ext?holder.ext:holder.med.init)+" ("+JOURSL[dow(y,m,d)].slice(0,3)+" "+d+" "+MOIS[m].slice(0,4)+") avec :"}</div>
        <div style={{maxHeight:"38vh",overflowY:"auto"}}>
          {autresGardes.map((g,i2)=>{
            const abs1=g.h.med?intAbsCeJour(getEntries,g.h.med.id,y,m,d):false;
            const abs2=holder.med?intAbsCeJour(getEntries,holder.med.id,g.o.y,g.o.m,g.o.d):false;
            return <div key={i2} onClick={()=>swap(g.o,g.h)} style={{display:"flex",alignItems:"center",gap:7,padding:"6px 9px",borderRadius:7,marginBottom:4,cursor:"pointer",border:"1px solid var(--border2)",background:"var(--bg2)"}}>
              <span style={{fontSize:11,fontWeight:700,color:"var(--txt)",width:88,flexShrink:0}}>{JOURSL[dow(g.o.y,g.o.m,g.o.d)].slice(0,3)+" "+g.o.d+" "+MOIS[g.o.m].slice(0,4)}</span>
              {g.h.med
                ?<span style={{width:26,height:26,borderRadius:"50%",background:g.h.med.color,color:"#fff",fontSize:10,fontWeight:800,display:"inline-flex",alignItems:"center",justifyContent:"center",flexShrink:0}}>{g.h.med.init}</span>
                :<span style={{fontSize:8,fontWeight:800,color:"var(--txt2)",background:"var(--bg2)",border:"1px dashed var(--border)",borderRadius:5,padding:"2px 4px",flexShrink:0}}>ext</span>}
              <span style={{flex:1,minWidth:0}}>
                <span style={{display:"block",fontSize:11,fontWeight:600,color:"var(--txt)",overflow:"hidden",textOverflow:"ellipsis",whiteSpace:"nowrap"}}>{g.h.ext?(g.h.ext+" (extérieur)"):g.h.med.nom}</span>
                {(abs1||abs2)&&<span style={{display:"block",fontSize:8,color:"#b45309",fontWeight:700}}>{abs1?((g.h.med?g.h.med.init:"")+" absent/FMC le "+d):""}{abs1&&abs2?" · ":""}{abs2?(holder.med.init+" absent/FMC le "+g.o.d):""}</span>}
              </span>
              <span style={{fontSize:11,color:"#388bfd",fontWeight:800}}>⇄</span>
            </div>;
          })}
          {autresGardes.length===0&&<div style={{fontSize:11,color:"var(--txt3)"}}>Aucune autre garde posée sur la période affichée.</div>}
        </div>
      </div>}
      <div style={{fontSize:10,color:"var(--txt3)",lineHeight:1.5}}>Le repos du lendemain est posé automatiquement avec la garde et remplace ce qui s'y trouve ; il s'enlève en retirant la garde. Un interne peut être absent ou en FMC le jour de sa garde. Les repos des deux jours sont recalculés lors d'un échange.</div>
    </div>
  </Ov>;
}

function InternesView({intCfg,setIntCfg=null,actes,acteById,getEntries,setEntry,isVac,year,month,allDays,viewPeriod,showFull,setShowFull,canEdit,canSalle=false,salleReg=[],intSelf=false,prevM,nextM,darkMode,setDarkMode}){
  const [sel,setSel]=useState(null);
  const [gm,setGm]=useState(null);
  const [jaugeOn,setJaugeOn]=useState(intCfg.jaugeDef!==false); /* v10.65 : affichage en nominal réglé dans Paramètres */
  const [statsOpen,setStatsOpen]=useState(false);
  /* v10.71 : l'onglet vit au SEMESTRE (6 mois), plus sur la periode de 4 mois de
     l'application — les internes tournent par semestre et echangent leurs gardes
     dessus. Les fleches ne touchent donc plus le mois GLOBAL (prevM/nextM ne sont
     plus appeles) : sortir de l'onglet ne deplace plus les autres onglets.
     La liste des jours avance date a date entre les deux bornes du semestre —
     aucun calcul par mois, donc pas de decalage possible (famille du bug v9.26). */
  const sems=useMemo(()=>intSemsTri(intCfg),[intCfg]);
  const [semIdx,setSemIdx]=useState(()=>{
    const t=intISO(new Date());
    const l=intSemsTri(intCfg);
    let i=l.findIndex(s=>s.deb<=t&&t<=s.fin);      /* celui du jour */
    if(i<0)i=l.findIndex(s=>s.deb>t);              /* sinon le prochain prepare */
    if(i<0)i=l.length-1;                           /* sinon le dernier termine */
    return i<0?0:i;
  });
  const semI=sems.length?Math.max(0,Math.min(semIdx,sems.length-1)):-1;
  const sem=semI>=0?sems[semI]:null;
  const jours=useMemo(()=>{
    if(!sem)return [];
    const out=[];let iso=sem.deb,n=0;
    while(iso<=sem.fin&&n<400){const p=iso.split("-").map(Number);out.push({y:p[0],m:p[1]-1,d:p[2]});iso=intDecal(iso,1);n++;}
    if(!showFull){const tod=intISO(new Date());return out.filter(o=>intISO2(o.y,o.m,o.d)>=tod);}
    return out;
  },[sem,showFull]);
  const cols=useMemo(()=>{
    if(!sem)return [];
    return (sem.meds||[]).map(mm=>({...mm,sDeb:sem.deb,sFin:sem.fin,sLbl:intSemLabel(sem.deb)}));
  },[sem]);
  const today=new Date();
  const titre=sem?intSemLabel(sem.deb):"aucun semestre";
  const C0=42,CG=44;
  const C1=jaugeOn?60:24; /* v10.65 : place pour les deux compteurs côte à côte */
  const cellEntree=(c,o,sl)=>{
    const es=getEntries(c.id,o.y,o.m,o.d,sl);
    let e=es.find(x=>x&&x.acteId&&!x._blocked)||null;
    if(!e)e=getEntries(c.id,o.y,o.m,o.d,"JOUR").find(x=>x&&x.acteId)||null;
    return e;
  };
  return <div>
    <div style={{...S.bar,position:"sticky",top:HDR_H,zIndex:40,background:"var(--bg)",paddingTop:6,paddingBottom:6}}>
      <div style={{display:"flex",alignItems:"center",gap:6}}>
        <button onClick={()=>setSemIdx(Math.max(0,semI-1))} disabled={semI<=0} style={{...S.arr,opacity:semI<=0?.35:1}} title="Semestre precedent">‹</button>
        <h2 style={S.mTit}>{"🎓 Internes — "+titre}</h2>
        <button onClick={()=>setSemIdx(Math.min(sems.length-1,semI+1))} disabled={semI<0||semI>=sems.length-1} style={{...S.arr,opacity:(semI<0||semI>=sems.length-1)?.35:1}} title="Semestre suivant">›</button>
      </div>
      <div style={{display:"flex",gap:6,alignItems:"center",marginLeft:"auto"}}>
        {sem&&<Chp bg="rgba(56,139,253,.12)" c="#1d4ed8">{intFmtD(sem.deb)+" → "+intFmtD(sem.fin)}</Chp>}
        <button onClick={()=>setStatsOpen(true)} title="Statistiques" style={{...S.arr,fontSize:13,width:30}}>📊</button>
        <button onClick={()=>setJaugeOn(v=>!v)} title="Jauge HC/USIC" style={{...S.arr,fontSize:13,width:30,color:jaugeOn?"#1d4ed8":"var(--txt2)",border:`1px solid ${jaugeOn?"#1d4ed8":"var(--border)"}`}}>🚦</button>
        <button onClick={()=>setShowFull(f=>!f)} title={showFull?"Depuis aujourd'hui":"Tout le semestre"} style={{...S.arr,fontSize:16,width:32,color:showFull?"var(--today-c)":"var(--txt2)",border:`1px solid ${showFull?"var(--today-c)":"var(--border)"}`}}>{showFull?"📅":"🗓️"}</button>
        <button onClick={()=>setDarkMode(d=>!d)} style={{...S.arr,fontSize:13,width:30}}>{darkMode?"☀️":"🌓"}</button>
      </div>
    </div>
    <div style={{fontSize:10,color:"var(--txt3)",margin:"2px 0 8px"}}>Jauge : internes en HC et en USIC sur le créneau, rouge sous le seuil (Paramètres). Case garde rouge : personne de garde ce jour. Samedi : une seule case (matin).{canEdit?" Cliquez la colonne 🌙 pour la garde (repos posé automatiquement le lendemain), une case pour le reste.":""}</div>
    {cols.length===0
      ?<div style={{...S.card}}>
        <div style={{fontSize:12,color:"var(--txt3)"}}>Aucun interne sur ce semestre — saisissez les semestres et les fiches dans l'onglet Équipe, section « 🎓 Internes ».</div>
      </div>
      :<TableScroll memId="internes" fit>
      <table style={{borderCollapse:"collapse",tableLayout:"fixed"}}>
        <thead>
          <tr>
            <th style={{...S.thFix,position:"sticky",top:0,left:0,zIndex:40,minWidth:C0}}>Jour</th>
            <th style={{...S.thFix,position:"sticky",top:0,left:C0,zIndex:40,minWidth:C1}}>Sl</th>
            <th style={{...S.thFix,position:"sticky",top:0,zIndex:20,minWidth:CG,borderRight:"2px solid var(--border)",fontSize:9,color:"#93c47d"}}>Garde</th>
            {cols.map(c=><th key={c.id} style={{...S.th,minWidth:52,position:"sticky",top:0,zIndex:20}} title={c.nom+" — "+c.sLbl+" ("+intFmtD(c.sDeb)+" → "+intFmtD(c.sFin)+")"}>
              <div style={{...S.avT,background:c.color,margin:"0 auto"}}>{c.init}</div>
            </th>)}
          </tr>
        </thead>
        <tbody>
          {jours.map((o,di)=>{
            const t=dow(o.y,o.m,o.d),fer=isFerie(o.y,o.m,o.d);
            const off=t===0||fer,samJ=!off&&t===6;
            const we=off||samJ;
            const isT=o.d===today.getDate()&&o.m===today.getMonth()&&o.y===today.getFullYear();
            const isMon=!we&&t===1;
            const slots=off?["JOUR"]:samJ?["M"]:["M","AM"];
            const vac=isVac(o.y,o.m,o.d);
            const gard=intGardeDuJour(getEntries,intCfg,o.y,o.m,o.d);
            return slots.map((sl,si)=>(
              <tr key={o.y+"-"+o.m+"-"+o.d+sl} data-day={o.y+"-"+o.m+"-"+o.d} style={{height:28,borderBottom:si===slots.length-1?"1px solid var(--border)":"1px solid var(--border2)",
                ...(we?{background:"var(--bg-we)"}:{}),...(isT?{background:"var(--bg-td)"}:{}),...(si===0&&isMon?{boxShadow:"0 -2px 0 0 var(--border)"}:{})}}>
                {si===0&&<td rowSpan={slots.length} style={{...S.tdFix,position:"sticky",left:0,zIndex:10,minWidth:C0,background:vac?"var(--vac-bg)":(we?"var(--bg-we)":"var(--td-fix)")}}>
                  <div style={{fontWeight:800,color:isT?"var(--today-c)":we?"#92400e":"var(--txt)",fontSize:12,fontFamily:"'JetBrains Mono',monospace",textAlign:"center"}}>{o.d}<div style={{fontSize:10,color:"var(--txt2)",fontWeight:700,fontFamily:"sans-serif",lineHeight:1.2}}>{MOIS[o.m]}</div>
                    <div style={{fontSize:8,color:"var(--txt3)",fontWeight:700,fontFamily:"sans-serif"}}>{JOURSL[t].slice(0,3)}{fer?" F":""}</div>
                  </div>
                </td>}
                <td style={{...S.tdFix,position:"sticky",left:C0,zIndex:9,fontSize:9,color:"var(--txt3)",fontWeight:700,textAlign:"center",background:we?"var(--bg-we)":"var(--td-fix)",minWidth:C1,padding:"2px"}}>{off?"":(jaugeOn?(()=>{
                  const jg=intJauge(getEntries,cols,o.y,o.m,o.d,sl);
                  const seuilH=parseInt(samJ?intCfg.sSam:intCfg.sHC)||0;
                  const seuilU=parseInt(intCfg.sUS)||0;
                  const badH=seuilH>0&&jg.hc<seuilH;      /* seuil 0 = pas d'alerte, sa règle */
                  const badU=!samJ&&seuilU>0&&jg.us<seuilU;
                  const chip=(lbl,n,bad)=><span style={{fontSize:8,fontWeight:800,fontFamily:"'JetBrains Mono',monospace",borderRadius:4,padding:"1px 3px",background:bad?"rgba(239,68,68,.18)":"var(--bg2)",color:bad?"#ef4444":"var(--txt3)",border:`1px solid ${bad?"#ef444466":"var(--border)"}`}}>{lbl}{n}</span>;
                  return <div style={{display:"flex",alignItems:"center",gap:2,justifyContent:"center"}}>
                    <span>{SLOTS[sl]}</span>{chip("H",jg.hc,badH)}{!samJ&&chip("U",jg.us,badU)}
                  </div>;
                })():SLOTS[sl])}</td>
                {si===0&&<td rowSpan={slots.length} onClick={canEdit?()=>setGm({y:o.y,m:o.m,d:o.d}):undefined}
                  style={{...S.tdFix,borderRight:"2px solid var(--border)",minWidth:CG,padding:"2px",verticalAlign:"middle",cursor:canEdit?"pointer":"default",
                    background:gard?(we?"var(--bg-we)":"var(--garde-bg)"):"rgba(248,81,73,.16)"}}>
                  {gard&&gard.med&&<div style={{width:26,height:26,borderRadius:"50%",background:gard.med.color,display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:10,fontWeight:800,margin:"0 auto"}}>{gard.med.init}</div>}
                  {gard&&gard.ext&&<div title={gard.ext+" (interne extérieur)"} style={{fontSize:8,fontWeight:800,color:"var(--txt2)",background:"var(--bg2)",border:"1px dashed var(--border)",borderRadius:5,padding:"2px 2px",textAlign:"center",overflow:"hidden",textOverflow:"ellipsis",whiteSpace:"nowrap"}}>{gard.ext}</div>}
                </td>}
                {cols.map(c=>{
                  const iso=intISO2(o.y,o.m,o.d);
                  const inR=iso>=c.sDeb&&iso<=c.sFin;
                  const horsSem={background:"repeating-linear-gradient(45deg,rgba(140,150,160,.14),rgba(140,150,160,.14) 3px,transparent 3px,transparent 7px)"};
                  if(off){ /* v10.60 : le repos de garde s'affiche aussi le dimanche/férié */
                    const eJ=inR?(getEntries(c.id,o.y,o.m,o.d,"JOUR").find(x=>x&&x.acteId)||null):null;
                    const aJ=eJ?acteById(eJ.acteId):null;
                    return <td key={c.id} style={{...S.td,...S.tdWE,...(inR?{}:horsSem)}}>
                      {aJ&&<div style={{display:"flex",flexWrap:"wrap",justifyContent:"center",alignItems:"center",gap:1}}><Badge a={aJ} hideSalle/></div>}
                    </td>;
                  }
                  const e=inR?cellEntree(c,o,sl):null;
                  const a=e?acteById(e.acteId):null;
                  return <td key={c.id} onClick={(canEdit&&inR)?()=>setSel({med:c,y:o.y,m:o.m,d:o.d,slot0:sl}):undefined}
                    style={{...S.td,...(we?S.tdWE:{}),...(inR?{cursor:canEdit?"pointer":"default"}:horsSem)}}>
                    {a&&<div style={{display:"flex",flexWrap:"wrap",justifyContent:"center",alignItems:"center",gap:1}}><Badge a={a} salle={e.salle} hideSalle={!e.salle}/></div>}
                  </td>;
                })}
              </tr>
            ));
          })}
        </tbody>
      </table>
    </TableScroll>}
    {statsOpen&&(()=>{
      /* v10.65 : mêmes activités « techniques » que les tuiles de la modale de case —
         Technique apparaîtra d'elle-même quand il l'aura créée ; les activités à
         salle restent hors stats (« pas indispensables », sa règle). */
      const statsOff=intCfg.statsOff||[];
      const exActes=actes.filter(a=>a.interneOk===true&&!a.isSystem&&!a.hasSalle&&ABS_IDS.indexOf(a.id)<0&&a.id!=="REPOS_GARDE");
      const exVis=exActes.filter(a=>statsOff.indexOf(a.id)<0);
      const showHC=statsOff.indexOf("TOUR_HC")<0,showUS=statsOff.indexOf("TOUR_USIC")<0;
      const st=intStats(getEntries,cols,jours,exVis);
      const fmtJ=n=>n===0?"—":(n/2).toString().replace(".",","); /* v10.67 : virgule, sa préférence */
      const CAT_L={sem:"Sem",jeu:"Jeu",ven:"Ven",sam:"Sam",dim:"Dim"};
      const num={textAlign:"center",fontFamily:"'JetBrains Mono',monospace",fontWeight:700,fontSize:12,color:"var(--txt)",padding:"4px 3px"};
      return <Ov onClose={()=>setStatsOpen(false)}>
        <div style={{...S.modal,maxWidth:720,maxHeight:"85vh",overflowY:"auto"}} onClick={e=>e.stopPropagation()}>
          <div style={S.mHd}><div style={S.mTit2}>{"📊 Statistiques — "+titre}</div><button onClick={()=>setStatsOpen(false)} style={S.xBtn}>×</button></div>
          <div style={{fontSize:10,color:"var(--txt3)",margin:"4px 0 8px"}}>{"Sur le semestre affiché ("+jours.length+" jours"+(showFull?"":", depuis aujourd'hui")+"). Gardes : total puis par catégorie (férié = dimanche, veille de férié = vendredi, comme chez les médecins). Le reste en jours (0,5 = demi-journée). Colonnes affichées : Paramètres, tuile Internes."}</div>
          <table style={{borderCollapse:"collapse",width:"100%"}}>
            <thead><tr>
              <th style={{...S.th,textAlign:"left",paddingLeft:8}}>Interne</th>
              <th style={{...S.th,padding:"4px 3px"}} title="Gardes posées (total)">🌙</th>
              {GCATS_INT.map(c2=><th key={c2} style={{...S.th,padding:"4px 3px",fontSize:9}}>{CAT_L[c2]}</th>)}
              {showHC&&<th style={{...S.th,padding:"4px 3px"}}>HC</th>}{showUS&&<th style={{...S.th,padding:"4px 3px"}}>USIC</th>}
              {exVis.map(a=><th key={a.id} style={{...S.th,padding:"4px 3px"}}>{a.short||a.label}</th>)}
            </tr></thead>
            <tbody>
              {cols.map(c=>{const s=st[c.id];return <tr key={c.id} style={{borderBottom:"1px solid var(--border2)"}}>
                <td style={{padding:"4px 8px"}}><div style={{display:"flex",alignItems:"center",gap:6}}><div style={{...S.avT,background:c.color,flexShrink:0}}>{c.init}</div><span style={{fontSize:12,fontWeight:700,color:"var(--txt)",maxWidth:110,overflow:"hidden",textOverflow:"ellipsis",whiteSpace:"nowrap"}}>{c.nom}</span></div></td>
                <td style={{...num,fontWeight:800}}>{s.gardes}</td>
                {GCATS_INT.map(c2=><td key={c2} style={{...num,color:s.cat[c2]?"var(--txt)":"var(--txt3)",fontWeight:s.cat[c2]?700:500}}>{s.cat[c2]||"·"}</td>)}
                {showHC&&<td style={num}>{fmtJ(s.hc)}</td>}
                {showUS&&<td style={num}>{fmtJ(s.us)}</td>}
                {exVis.map(a=><td key={a.id} style={num}>{fmtJ(s.ex[a.id])}</td>)}
              </tr>;})}
            </tbody>
          </table>
        </div>
      </Ov>;
    })()}
    {sel&&<InternesCellModal med={sel.med} y={sel.y} m={sel.m} d={sel.d} slot0={sel.slot0} onClose={()=>setSel(null)} actes={actes} acteById={acteById} getEntries={getEntries} setEntry={setEntry} canSalle={canSalle} salleReg={salleReg} intSelf={intSelf}/>}
    {gm&&<InternesGardeModal y={gm.y} m={gm.m} d={gm.d} jours={jours} onClose={()=>setGm(null)} intCfg={intCfg} getEntries={getEntries} setEntry={setEntry}/>}
  </div>;
}

/* ════ ARCHIVAGE PAR PÉRIODE (v10.110) ═════════════════════════════════════════
   L'archive est un DOCUMENT PAR PÉRIODE (`archives/per-<sy>-<sm>`, sm technique
   0-based — les arguments de perDaysList), et plus un par mois : le verrou, la
   navigation et Construire raisonnent déjà en périodes, l'archive parle enfin
   la même langue. Une seule lecture Firestore par période consultée au lieu de
   cinq (4 mois + le débordement). `planning/main` reste plafonné à 1 Mo par
   Firestore (la jauge des Paramètres) : au-delà, Firebase REFUSE l'écriture.

   DEUX FORMATS DE CLÉS cohabitent dans les données datées, et les confondre est
   exactement le bug v10.4 :
     — « clair »      YYYY-MM-DD  (mois 1-based padé, dKey)
     — « technique »  Y-M-D       (mois 0-based non padé, wKey / dk3)
   Chaque famille déclare donc SON lecteur de période. Jamais de slice aveugle.

   RÈGLE DES SEMAINES (la sienne, v10.109) : les semaines d'une période vont du
   lundi ≤ premier jour au dimanche ≤ dernier jour. Ici c'est donc le DIMANCHE
   (lundi + 6) qui décide de la période d'une semaine — équivalence avec
   perWeeksList prouvée au banc, y compris lundi férié et fin de vacances en
   milieu de semaine.

   L'ASTREINTE reste volontairement en place : ses clés de jour et de semaine
   ont le MÊME format et ne se distinguent pas. Moins de 1 Ko en jeu. */
const arPad=(y,m0)=>{const dt=new Date(y,m0,1);return dt.getFullYear()+"-"+String(dt.getMonth()+1).padStart(2,"0");};
const perIdOf=(sy,sm)=>sy+"-"+sm;
/* La PÉRIODE d'un jour. perStart donne la période « calendaire » de son mois ;
   un pas de correction suffit ensuite : un débordement (dimanche de clôture,
   lundi férié, extension vacances plafonnée à 21 j) reste dans le PREMIER mois
   de la période suivante — prouvé au banc sur 2026→2030. */
function perOfDay(y,m0,d){
  let p=perStart(y,m0);
  const dt=new Date(y,m0,d);
  const l=perDaysList(p.sy,p.sm);
  if(l.length&&dt<new Date(l[0].y,l[0].m,l[0].d))p=perPrev(p.sy,p.sm);
  else if(dt>perEnd(p.sy,p.sm))p=perNext(p.sy,p.sm);
  return p;
}
/* période d'une clé au format clair YYYY-MM-DD (cases, tourDerog, gardeWish, gardeAvoid) */
function arPerClair(k){const s=String(k);if(!/^\d{4}-\d{2}-\d{2}/.test(s))return null;
  const p=perOfDay(+s.slice(0,4),+s.slice(5,7)-1,+s.slice(8,10));return perIdOf(p.sy,p.sm);}
/* notes : "medId|YYYY-MM-DD|SLOT" — le medId peut contenir n'importe quoi */
function arPerNote(k){const p=String(k).split("|");return p.length>=2?arPerClair(p[1]):null;}
/* clé technique Y-M-D, éventuellement suivie de "|SLOT" */
function arNums(k){const p=String(k).split("|")[0].split("-");
  if(p.length!==3)return null;
  const y=+p[0],m=+p[1],d=+p[2];
  return (isFinite(y)&&isFinite(m)&&isFinite(d)&&y>1900&&m>=0&&m<=11&&d>=1&&d<=31)?[y,m,d]:null;}
function arPerTechJour(k){const n=arNums(k);if(!n)return null;
  const p=perOfDay(n[0],n[1],n[2]);return perIdOf(p.sy,p.sm);}
/* semaine (clé = son lundi) : le DIMANCHE décide — équivalent de perWeeksList */
function arPerTechSem(k){const n=arNums(k);if(!n)return null;
  const p=perOfDay(n[0],n[1],n[2]+6);return perIdOf(p.sy,p.sm);}
/* build : clé "sy_sm" = DÉJÀ une clé de période, correspondance directe
   (la règle « c'est son dernier mois qui décide » disparaît d'elle-même) */
function arPerPeriode(k){const p=String(k).split("_");
  if(p.length!==2)return null;const y=+p[0],m=+p[1];
  return (isFinite(y)&&isFinite(m)&&y>1900&&m>=0&&m<=11)?perIdOf(y,m):null;}

/* familles à plat. `lu` = relue à la consultation d'une période archivée (le
   tour et les notes s'affichent dans la grille ; les souhaits, reports et
   Construire n'ont aucune valeur pour une période passée, ils partent sans
   retour d'écran). */
const AR_FAM=[
  {ch:"tourMed",    per:arPerTechSem, lu:true,  lib:"semaine de tour|semaines de tour"},
  {ch:"tourDerog",  per:arPerClair,   lu:true,  lib:"dérogation de tour|dérogations de tour"},
  {ch:"notes",      per:arPerNote,    lu:true,  lib:"note|notes"},
  {ch:"tourWish",   per:arPerTechSem, lu:false, lib:"souhait de tour|souhaits de tour"},
  {ch:"tourAvoid",  per:arPerTechSem, lu:false, lib:"tour à éviter|tours à éviter"},
  {ch:"gardeWish",  per:arPerClair,   lu:false, lib:"souhait de garde|souhaits de garde"},
  {ch:"gardeAvoid", per:arPerClair,   lu:false, lib:"garde à éviter|gardes à éviter"},
  {ch:"build",      per:arPerPeriode, lu:false, lib:"période de Construire|périodes de Construire"},
];
/* familles indexées PAR MÉDECIN, avec les clés datées au deuxième niveau
   (toutes au format technique) : csBlanches[mid][cle], csRep[mid].done/.to[cle] */
const AR_MED=[
  {ch:"csBlanches", sous:null,          lib:"semaine blanche|semaines blanches"},
  {ch:"csRep",      sous:["done","to"], lib:"report de consultation|reports de consultation"},
];
const AR_LU=AR_FAM.filter(f=>f.lu).map(f=>f.ch);

/* Découpe les données datées en fonction des périodes archivées.
   Rend {parts:{periode:{champ:…}}, cnt:{champ:n}, n, lib} — `parts` part en
   archive, `lib` est la phrase annoncée dans la confirmation AVANT tout retrait. */
function arDecoupe(src,pers){
  const ok=(pid)=>!!pid&&pers.indexOf(pid)>=0;
  const parts={},cnt={};
  const met=(pid,ch,k,v,mid,sous)=>{
    const P=parts[pid]=parts[pid]||{};
    if(mid===undefined){(P[ch]=P[ch]||{})[k]=v;return;}
    const M=(P[ch]=P[ch]||{});const O=(M[mid]=M[mid]||{});
    if(sous){(O[sous]=O[sous]||{})[k]=v;}else O[k]=v;
  };
  AR_FAM.forEach(f=>{
    const o=src[f.ch]||{};let n=0;
    Object.keys(o).forEach(k=>{const pid=f.per(k);if(ok(pid)){met(pid,f.ch,k,o[k]);n++;}});
    cnt[f.ch]=n;
  });
  AR_MED.forEach(f=>{
    const o=src[f.ch]||{};let n=0;
    Object.keys(o).forEach(mid=>{
      const cur=o[mid]||{};
      if(!f.sous){Object.keys(cur).forEach(k=>{const pid=arPerTechJour(k);if(ok(pid)){met(pid,f.ch,k,cur[k],mid);n++;}});}
      else f.sous.forEach(s=>{const s2=cur[s]||{};
        Object.keys(s2).forEach(k=>{const pid=arPerTechJour(k);if(ok(pid)){met(pid,f.ch,k,s2[k],mid,s);n++;}});});
    });
    cnt[f.ch]=n;
  });
  let tot=0;const lib=[];
  AR_FAM.concat(AR_MED).forEach(f=>{const n=cnt[f.ch]||0;if(!n)return;tot+=n;
    const w=f.lib.split("|");lib.push(n+" "+(n>1?w[1]:w[0]));});
  return {parts,cnt,n:tot,lib:lib.join(", ")};
}

/* Retire d'un état les clés des périodes archivées. Toujours appelé DANS un
   updater setX(o=>…) : entre le rendu et le clic, le serveur peut avoir livré
   des modifications, et une valeur figée au rendu les écraserait (leçon v10.3). */
function arPurge(o,per,ok){const g={};Object.keys(o||{}).forEach(k=>{const pid=per(k);if(!ok(pid))g[k]=o[k];});return g;}
function arPurgeMed(o,sous,ok){const g={};
  Object.keys(o||{}).forEach(mid=>{const cur=o[mid]||{};
    if(!sous){const gg=arPurge(cur,arPerTechJour,ok);if(Object.keys(gg).length)g[mid]=gg;}
    else{const gg={};sous.forEach(s=>{const gs=arPurge(cur[s]||{},arPerTechJour,ok);if(Object.keys(gs).length)gg[s]=gs;});
      if(Object.keys(gg).length)g[mid]=gg;}});
  return g;}

/* Réinjecte un fragment d'annexe dans un état : ce qui est ACTIF gagne toujours,
   comme la restauration des cases au désarchivage. */
function arFusion(ch,cur,frag){
  if(!frag||Object.keys(frag).length===0)return cur||{};
  const med=AR_MED.filter(f=>f.ch===ch)[0];
  if(!med)return Object.assign({},frag,cur||{});
  const out=Object.assign({},cur||{});
  Object.keys(frag).forEach(mid=>{
    const f2=frag[mid]||{},c2=out[mid]||{};
    if(!med.sous){out[mid]=Object.assign({},f2,c2);return;}
    const o={};
    med.sous.forEach(s=>{const m2=Object.assign({},f2[s]||{},c2[s]||{});if(Object.keys(m2).length)o[s]=m2;});
    out[mid]=o;});
  return out;}

/* ════ VERROU DES PÉRIODES CLOSES (v10.106) ════════════════════════════════════
   Sa règle : « on ne modifie pas le passé », et la borne est la PÉRIODE — tout ce
   qui précède le PREMIER JOUR de la période en cours (celle qui contient
   aujourd'hui) est clos. Une période va du lendemain de la fin de la précédente
   au dimanche qui la clôt, donc jamais du 1er au 31 : c'est perDaysList qui fait foi.

   VOLONTAIREMENT INDÉPENDANT DE L'ARCHIVAGE. L'ancien bandeau violet se fondait sur
   les archives CHARGÉES, or une archive n'est lue que si l'on navigue vers son mois :
   il apparaissait après l'archivage puis disparaissait au changement de session. La
   période, elle, est connue dès l'ouverture — l'indicateur est donc toujours juste,
   même avant tout archivage.

   SA DÉCISION DU 24/08/2026 : le verrou vaut pour TOUT LE MONDE, éditeur compris
   (« changer une case passée n'a aucun sens »). Le verrou porte sur TOUT, absences
   et FMC comprises. Seule échappatoire : l'interrupteur de Paramètres, réservé à
   l'éditeur, éteint par défaut et NON persisté — il se réarme au rechargement.
   C'est lui, et lui seul, qui alimente `passe` ci-dessous ; `ed` ne sert qu'au
   texte du message. */
function verrouDebut(){
  const t=new Date();
  const p=perStart(t.getFullYear(),t.getMonth());
  const l=perDaysList(p.sy,p.sm);
  return l.length?dKey(l[0].y,l[0].m,l[0].d):"0000-00-00";
}
/* La borne et le droit de passer outre sont lus dans une REF : les fonctions
   d'écriture ont des dépendances vides et ne doivent pas être recréées à chaque
   changement de mode, sous peine de casser toutes les mémoïsations en aval. */
function vBloque(r,y,m,d){return dKey(y,m,d)<r.current.deb&&!r.current.passe;}
function vAvertit(r,y,m,d){return dKey(y,m,d)<r.current.deb&&r.current.passe;}

function CardioPlanning(){
  const today=new Date();
  const [accessMode,setAccessMode]=useState("ask");
  const [pinInput,setPinInput]=useState("");
  const [pinError,setPinError]=useState(false);
  const [editPin,setEditPin]=useState(EDIT_PIN_DEFAULT);
  /* ── v9.8 : rôle Administratif (secrétaires + cadres) ── */
  const [adminPin,setAdminPin]=useState("");
  const [cadrePin,setCadrePin]=useState("");
  const [isCadre,setIsCadre]=useState(false);
  /* ── v9.35 : effectifs IDE ── */
  const [ideCfg,setIdeCfg]=useState({def:{},ov:{}});
  const [intCfg,setIntCfg]=useState({sems:[],show:false,jaugeDef:true,sHC:2,sUS:2,sSam:1}); // v10.54 internes
  const [prefOn,setPrefOn]=useState(false);   // v10.81 : coloration des preferences — session seulement
  const [intGardeOn,setIntGardeOn]=useState(false); // v10.61 lot 3b : colonne garde int. du Planning — session seulement, cachée en nominal
  const [ptOrder,setPtOrder]=useState([]);
  const [specColors,setSpecColors]=useState({});
  const [colOrder,setColOrder]=useState({});
  const [colModal,setColModal]=useState(null);
  /* ── v9.40 : impression ── */
  const [printWk,setPrintWk]=useState(null);
  const [printWhat,setPrintWhat]=useState("plateau");
  const [printSel,setPrintSel]=useState(()=>{const t=new Date();return mondayOf(t.getFullYear(),t.getMonth(),t.getDate());});
  const [ideOn,setIdeOn]=useState(()=>{try{return localStorage.getItem("cp6_ide_on")==="1";}catch{return false;}});
  useEffect(()=>{try{localStorage.setItem("cp6_ide_on",ideOn?"1":"0");}catch{}},[ideOn]);
  const [adminEnabled,setAdminEnabled]=useState(true);
  const [adminCanReports,setAdminCanReports]=useState(true);
  const [adminCanNotes,setAdminCanNotes]=useState(false);
  const [adminName,setAdminName]=useState(()=>{try{return localStorage.getItem("cp6_adminName")||"";}catch(e){return "";}});
  const [adminAsk,setAdminAsk]=useState(false);
  const [adminNameInput,setAdminNameInput]=useState(()=>{try{return localStorage.getItem("cp6_adminName")||"";}catch(e){return "";}});
  /* v10.69, lot 5 : acces INTERNE (code partage, defini dans Parametres > tuile
     Internes). Le prenom est demande a la connexion et retenu sur l'appareil,
     exactement comme pour les secretaires et les cadres. */
  const [interneAsk,setInterneAsk]=useState(false);
  const [interneName,setInterneName]=useState(()=>{try{return localStorage.getItem("cp6_interneName")||"";}catch(e){return "";}});
  const [interneNameInput,setInterneNameInput]=useState(()=>{try{return localStorage.getItem("cp6_interneName")||"";}catch(e){return "";}});
  const [showPins,setShowPins]=useState(false);
  const [pinsAsk,setPinsAsk]=useState(false);
  const [pinsTry,setPinsTry]=useState("");
  const validatePins=()=>{const v=pinsTry;const okEd=medecins.some(m=>((m.niveau)||"basic")==="editeur"&&(medPins[String(m.id)]||"").length>=3&&medPins[String(m.id)]===v);if(v===editPin||okEd){setShowPins(true);setPinsAsk(false);setPinsTry("");}else toast("PIN incorrect","warn");};
  /* ── v9.10 : mode hors ligne (lecture seule) ── */
  const [netOff,setNetOff]=useState(()=>typeof navigator!=="undefined"&&navigator.onLine===false);
  useEffect(()=>{
    const on=()=>setNetOff(false),off=()=>setNetOff(true);
    window.addEventListener("online",on);window.addEventListener("offline",off);
    return()=>{window.removeEventListener("online",on);window.removeEventListener("offline",off);};
  },[]);
  const [histModal,setHistModal]=useState(null);
  /* ── v9.9 : journal des cases — document Firestore séparé (planning/journal), jamais archivé ── */
  const authorRef=useRef("?");
  const logCell=useCallback((action,medId2,y2,m2,d2,sl2,acteId2)=>{
    try{
      if(!window.firebaseDB||!window.firebaseDoc)return;
      const jdoc=window.firebaseDoc(window.firebaseDB,"planning","journal");
      const eid="e"+Date.now().toString(36)+Math.random().toString(36).slice(2,6);
      const je={t:Date.now(),k:sk(y2,m2,d2,sl2),md:medId2,x:action,act:acteId2||null,a:authorRef.current};
      if(updatePaths)Promise.resolve(updatePaths(jdoc,[[["entries",eid],je]])).catch(()=>{if(setDoc)Promise.resolve(setDoc(jdoc,{entries:{[eid]:je}},{merge:true})).catch(()=>{});});
      else if(setDoc)Promise.resolve(setDoc(jdoc,{entries:{[eid]:je}},{merge:true})).catch(()=>{});
    }catch(e){}
  },[]);
  const [editMedId,setEditMedId]=useState(null); // medecin logged in with personal PIN
  /* v9.99 : l'onglet Paramètres défile avec la PAGE, pas dans un cadre — la mémoire de
     TableScroll ne le couvre donc pas. C'est le seul onglet où la perte de position le
     gêne réellement (il est long : droits, tour, salles, sauvegardes, archives). On
     mémorise le défilement de la fenêtre à la sortie et on le restaure au retour.
     Volontairement limité à cet onglet. */
  const [tab,setTab]=useState("planning");
  const pageMem=useRef({});
  const goTab=useCallback((next)=>{
    setTab(cur=>{
      if(cur===next)return cur;
      /* v10.31 : Construire rejoint Paramètres — on retrouve l'endroit où on était.
         La période et les tuiles ouvertes, elles, sont retenues par BUILD_MEM. */
      if(cur==="partage"||cur==="construire")pageMem.current[cur]=window.scrollY||0;
      const y=(next==="partage"||next==="construire")?(pageMem.current[next]||0):0;
      setTimeout(()=>window.scrollTo(0,y),0);
      return next;
    });
  },[]);
  const [ym,setYM]=useState(()=>({year:new Date().getFullYear(),month:new Date().getMonth()}));
  const year=ym.year, month=ym.month;
  const setYear=y=>setYM(p=>({...p,year:typeof y==="function"?y(p.year):y}));
  const setMonth=m=>setYM(p=>({...p,month:typeof m==="function"?m(p.month):m}));
  const setYearMonth=(y,m)=>setYM({year:y,month:m});
  /* v9.90 : l'affichage horizontal, inutilisé, a été supprimé — il ne reste que la vue
     « jours en lignes ». Le réglage d'orientation n'a donc plus lieu d'être. */
  const [darkMode,setDarkModeRaw]=useState(()=>{
    try{const v=localStorage.getItem("cp6_theme");if(v==="dark")return true;if(v==="light")return false;}catch(e){}
    try{return window.matchMedia&&window.matchMedia("(prefers-color-scheme: dark)").matches;}catch(e){return false;} // auto : reglage clair/sombre du telephone
  });
  const setDarkMode=(fn)=>{setDarkModeRaw(prev=>{const nv=typeof fn==="function"?fn(prev):fn;try{localStorage.setItem("cp6_theme",nv?"dark":"light");}catch(e){}return nv;});};
  useEffect(()=>{
    if(!window.matchMedia)return;
    const mq=window.matchMedia("(prefers-color-scheme: dark)");
    const onChg=(e)=>{try{if(localStorage.getItem("cp6_theme"))return;}catch(err){}setDarkModeRaw(e.matches);};
    if(mq.addEventListener)mq.addEventListener("change",onChg);else if(mq.addListener)mq.addListener(onChg);
    return ()=>{if(mq.removeEventListener)mq.removeEventListener("change",onChg);else if(mq.removeListener)mq.removeListener(onChg);};
  },[]);
  const DEFAULT_TABS=[["planning","📅 Planning"],["chl","🏥 CHL"],["chb","🏥 CHB"],["plateau","❤️ PT Cardio"],["angio","🔬 PT Angio"],["internes","🎓 Internes"],["construire","🏗️ Construire"],["tourmedical","🔄 Tour"],["garde","🌙 Gardes"],["astreinte","📞 Astreinte"],["reports","📥 Reports"],["attache","👔 Attachés"],["plantype","📋 Type"],["equipe","👥 Équipe"],["activites","⚙️ Activités"],["stats","📊 Stats"],["aide","❓ Aide"],["partage","⚙️ Paramètres"]];
  /* v10.78 : « Internes » rejoint « PT Angio ». L'ordre ENREGISTRE sur l'appareil fait foi
     (cp6_taborder_v3), donc changer DEFAULT_TABS ne suffisait pas : sur un appareil deja
     utilise, l'onglet serait reste en fin de liste. On passe donc a une nouvelle cle et,
     au premier chargement, on DEPLACE simplement « internes » derriere « angio » dans
     l'ordre deja enregistre — le reste du rangement personnel de l'appareil est conserve. */
  const [tabOrder,setTabOrder]=useState(()=>{ try{
    const all=DEFAULT_TABS.map(t=>t[0]);
    const compl=ids=>[...ids.filter(id=>all.includes(id)),...all.filter(id=>!ids.includes(id))];
    const v=localStorage.getItem("cp6_taborder_v4");
    if(v) return compl(JSON.parse(v));
    const anc=localStorage.getItem("cp6_taborder_v3");
    if(anc){ const m=compl(JSON.parse(anc)).filter(id=>id!=="internes");
      const i=m.indexOf("angio"); m.splice(i>=0?i+1:m.length,0,"internes"); return m; }
    return all;
  }catch{ return DEFAULT_TABS.map(t=>t[0]); } });
  const [dragTab,setDragTab]=useState(null);
  useEffect(()=>{ try{ localStorage.setItem("cp6_taborder_v4",JSON.stringify(tabOrder)); }catch{} },[tabOrder]);

  const [modal,setModal]=useState(null);
  const [mData,setMData]=useState(null);
  const [notif,setNotif]=useState(null);
  const [planFilter,setPlanFilter]=useState([]);
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
  /* v10.29 : etat de l'onglet Construire, un objet par periode (pointage, etapes, surspecialites) */
  const [build,setBuild]=useState({});
  const [tourAvoid,setTourAvoid]=useState({}); // {weekKey:{medId:true}} préférences "ne pas tourner"
  const [tourWish,setTourWish]=useState({});   // {weekKey:{medId:true}} souhaite tourner
  const [gardeAvoid,setGardeAvoid]=useState({}); // {dateKey:{medId:true}} préfère pas de garde ce jour
  const [gardeWish,setGardeWish]=useState({});   // {dateKey:{medId:true}} souhaite la garde ce jour
  const [csBlanches,setCsBlanches]=useState({}); // {medId:{"y-m-d":true}} jours sans consultation (logiciel métier)
  const [csRep,setCsRep]=useState({}); // v9.14 {medId:{done:{wk:true},to:{"dKey|sl":{d,sl,n}}}}
  const [csActsSel,setCsActsSel]=useState({});   // {medId:[acteIds]} activités comptées comme consultation
  const [csActsGlobal,setCsActsGlobal]=useState(["CS_CHL","CS_CHB","DOBU","DOBU_CHB","ETO_CHL","PM_CS","DEFIB_CS","RYTHMO_CHB"]); // activités proposables dans l'onglet Reports (réglé dans Paramètres)
  const [tourDerog,setTourDerog]=useState({});   // {dateKey:{medId:true}} affecté au tour cette semaine mais ne tourne PAS ce jour
  const [tourReport,setTourReport]=useState(null); // rapport persistant de la dernière répartition auto du tour
  const [astReport,setAstReport]=useState(null);
  /* v10.35 : sauvegarde sur SON ordinateur. Tout est LOCAL a l'appareil
     (localStorage) — la date de derniere sauvegarde et le compteur de cases n'ont
     de sens que pour la machine qui detient le fichier. */
  const [expPer,setExpPer]=useState(()=>{const t=new Date();return perStart(t.getFullYear(),t.getMonth());});
  const [expSrc,setExpSrc]=useState("now");
  const [expBusy,setExpBusy]=useState(false);
  const [expSnooze,setExpSnooze]=useState(false);
  const [expSeuil,setExpSeuil]=useState(()=>{try{return parseInt(localStorage.getItem("cp6_expSeuil"))||EXP_SEUIL;}catch(e){return EXP_SEUIL;}});
  const [expLast,setExpLast]=useState(()=>{try{return parseInt(localStorage.getItem("cp6_expLast"))||0;}catch(e){return 0;}});
  const [expN,setExpN]=useState(()=>{try{return parseInt(localStorage.getItem("cp6_expN"))||0;}catch(e){return 0;}});
  const expBump=useCallback((n)=>{if(!n)return;setExpN(v=>{const t=v+n;try{localStorage.setItem("cp6_expN",String(t));}catch(e){}return t;});},[]);
  useEffect(()=>{try{localStorage.setItem("cp6_expSeuil",String(expSeuil));}catch(e){}},[expSeuil]);
  const [salleReg,setSalleReg]=useState([]); // registre central des salles [{n:"Angio-1",s:"ANGIO"},...]
  const [salleEdit,setSalleEdit]=useState(null); // salle en cours d'édition (activités associées)
  const [archPlan,setArchPlan]=useState({});   // cases archivées chargées pour consultation (lecture)
  /* v10.105 : annexes archivées relues pour la consultation (tour, dérogations, notes) */
  const [archAnx,setArchAnx]=useState({tourMed:{},tourDerog:{},notes:{}});
  const archFetched=useRef({});                // périodes d'archives déjà demandées   // rapport persistant de la dernière répartition auto des astreintes
  const [periodCfg,setPeriodCfg]=useState({len:4,startM:6});
  PCFG.len=periodCfg.len;PCFG.startM=periodCfg.startM; // config répartition par période {perKey:{weeks,excl,p2hc,p2usic,mins}}
  const [astreinte,setAstreinte]=useState({}); // {wKey: medId}
  const [astDayModal,setAstDayModal]=useState(null); // legacy
  const [astPickModal,setAstPickModal]=useState(null); // {dayKey,wKey,isWeek,label}
  const [bipModal,setBipModal]=useState(null); // v9.16 répartition du Bip
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
  const [astSemOuv,setAstSemOuv]=useState({}); // v10.22 : semaines dépliées dans l'onglet Astreinte
  const [tourYear,setTourYear]=useState(()=>new Date().getFullYear());
  const [tourMonth,setTourMonth]=useState(()=>new Date().getMonth());
  const [fbStatus,setFbStatus]=useState("connecting");
  /* v10.18 : les vacances sont désormais SAISIES (onglet Paramètres) et enregistrées avec
     le reste. Plus de téléchargement : il échouait le plus souvent, et surtout il arrivait
     APRÈS l'affichage — les bornes de période auraient changé en cours d'usage. */
  const [vacs,setVacs]=useState([]);          // [{an,nom,d1,d2}]
  const [vacRule,setVacRule]=useState(false); // étendre la période jusqu'à la fin des vacances
  const [vacOuv,setVacOuv]=useState({});      // années dépliées dans le panneau
  useEffect(()=>{VAC_LIST=vacs;},[vacs]);
  useEffect(()=>{VAC_RULE=vacRule;},[vacRule]);
  const vacDates=React.useMemo(()=>{
    const set=new Set();
    vacs.forEach(v=>{
      if(!v.d1||!v.d2)return;
      const a=new Date(v.d1+"T00:00:00"),b=new Date(v.d2+"T00:00:00");
      for(let dt=new Date(a);dt<=b;dt.setDate(dt.getDate()+1)){
        set.add(dt.getFullYear()+"-"+String(dt.getMonth()+1).padStart(2,"0")+"-"+String(dt.getDate()).padStart(2,"0"));
      }
    });
    return set;
  },[vacs]);
  const isVac=(y,m,d)=>vacDates.has(`${y}-${String(m+1).padStart(2,"0")}-${String(d).padStart(2,"0")}`);
  const isFirstLoad=useRef(true);
  /* v9.71 : la persistance hors ligne fait que le TOUT PREMIER message vient du CACHE
     LOCAL, pas du serveur. Il peut être en retard. Tant qu'un message serveur n'est pas
     arrivé, on affiche ce cache mais on n'écrit RIEN : sinon une modification faite dans
     cette fenêtre serait écrite par-dessus une base périmée et effacerait tout ce qui a
     été ajouté depuis — le planning type étant enregistré d'un bloc, la perte est totale. */
  const serverSeen=useRef(false);
  const localChange=useRef(false);
  /* ── v9.44 : suivi par champ.
     fieldSync = dernière valeur connue de chaque champ (envoyée ou reçue) : sert à
     ne pas renvoyer au serveur ce qu'on vient d'en recevoir.
     pendF = champs dont une écriture est en vol : seuls ceux-là sont ignorés
     quand un message arrive, au lieu du message entier comme avant. ── */
  const fieldSync=useRef({});
  const pendF=useRef({});
  const planSynced=useRef(null);
  const planPending=useRef({});
  const planMigrated=useRef(false);
  /* v9.72 : le planning type était enregistré d'un SEUL bloc — une écriture partant d'une
     base périmée réécrivait tout et effaçait ce qui avait été ajouté depuis. Il suit
     désormais le même découpage que le plan (v9.7) : un champ par médecin, écrit
     séparément, et ré-appliqué tant que le serveur ne l'a pas confirmé. */
  const ptSynced=useRef(null);
  const ptPending=useRef({});
  const ptMigrated=useRef(false);
  /* ── v9.7 : écriture du plan en delta — seules les cases modifiées partent vers Firebase,
     la fusion se fait champ par champ côté serveur : zéro écrasement entre éditeurs simultanés ── */
  const flushPlan=useCallback((cur)=>{
    if(!PLANNING_DOC||!updatePaths)return;
    const prev=planSynced.current||{};
    const pairs=[];
    Object.keys(cur).forEach(k=>{const v=fbSafeCell(cur[k]);if(JSON.stringify(v)!==JSON.stringify(prev[k])){pairs.push([["planV2",k],v]);planPending.current[k]=v;}});
    Object.keys(prev).forEach(k=>{if(!(k in cur)){pairs.push([["planV2",k],"__DELETE__"]);planPending.current[k]=null;}});
    planSynced.current=cur;
    if(pairs.length===0)return;
    expBump(pairs.length);   /* v10.35 : cases modifiees depuis la derniere sauvegarde */
    localChange.current=true;
    (async()=>{
      try{for(let i=0;i<pairs.length;i+=200)await updatePaths(PLANNING_DOC,pairs.slice(i,i+200));}
      /* v10.111 : le repli {merge:true} FUSIONNAIT — les SUPPRESSIONS (celles de
         l'archivage !) étaient perdues en silence et les cases ressuscitaient au
         rechargement suivant. mergeFields remplace le champ planV2 en entier :
         les retraits comptent. Lots ramenés à 200 par prudence. */
      catch(e){console.error("sync plan ("+pairs.length+" paires):",e);setFbStatus("error");if(setDoc)Promise.resolve(setDoc(PLANNING_DOC,{planV2:cur},{mergeFields:["planV2"]})).then(()=>setFbStatus("ok")).catch(e2=>{console.error("sync plan (repli):",e2);setFbStatus("error");});}
    })();
  },[]);

  /* Écriture du planning type, médecin par médecin (v9.72). */
  /* v9.78 : les LISTES (activités, médecins) étaient enregistrées d'un seul bloc, donc
     vulnérables au même effacement que le planning type : une écriture partant d'une base
     incomplète réécrivait tout. Elles suivent désormais le même découpage — un
     enregistrement par élément, plus un champ d'ordre — via `flushList`. */
  const listSynced=useRef({});
  const listPending=useRef({});
  const listMigrated=useRef({});
  const flushList=useCallback((field,arr)=>{
    if(!PLANNING_DOC||!updatePaths)return;
    if(!serverSeen.current)return;
    const cur={};(arr||[]).forEach(x=>{if(x&&x.id!==undefined&&x.id!==null)cur[String(x.id)]=x;});
    const prev=listSynced.current[field]||{};
    const pend=listPending.current[field]||(listPending.current[field]={});
    const pairs=[];
    Object.keys(cur).forEach(k=>{
      if(JSON.stringify(cur[k])!==JSON.stringify(prev[k])){pairs.push([[field,k],cur[k]]);pend[k]=cur[k];}
    });
    Object.keys(prev).forEach(k=>{if(!(k in cur)){pairs.push([[field,k],"__DELETE__"]);pend[k]=null;}});
    const ordK=field+"Order",ord=(arr||[]).map(x=>String(x&&x.id));
    if(JSON.stringify(ord)!==JSON.stringify(listSynced.current[ordK]))pairs.push([[ordK],ord]);
    listSynced.current[field]=cur;listSynced.current[ordK]=ord;
    if(pairs.length===0)return;
    localChange.current=true;
    (async()=>{
      try{for(let i=0;i<pairs.length;i+=400)await updatePaths(PLANNING_DOC,pairs.slice(i,i+400));}
      catch(e){console.log("sync "+field+":",e);setFbStatus("error");}
    })();
  },[]);
  /* Réception d'une liste découpée : on ré-applique nos modifications non confirmées. */
  const readList=useCallback((field,incMap,incOrder)=>{
    const merged={...(incMap||{})};
    const pend=listPending.current[field]||{};
    Object.keys(pend).forEach(k=>{
      const pv=pend[k];
      const okc=pv===null?!(k in merged):JSON.stringify(merged[k])===JSON.stringify(pv);
      if(okc)delete pend[k];
      else{if(pv===null)delete merged[k];else merged[k]=pv;}
    });
    listSynced.current[field]=merged;
    const ord=(incOrder||[]).filter(k=>k in merged);
    Object.keys(merged).forEach(k=>{if(ord.indexOf(k)<0)ord.push(k);});
    listSynced.current[field+"Order"]=ord;
    return ord.map(k=>merged[k]).filter(Boolean);
  },[]);

  const flushPT=useCallback((cur)=>{
    if(!PLANNING_DOC||!updatePaths)return;
    if(!serverSeen.current)return;                 // jamais sur une base venant du seul cache
    const prev=ptSynced.current||{};
    const pairs=[];
    Object.keys(cur||{}).forEach(k=>{
      const v=cur[k];
      if(JSON.stringify(v)!==JSON.stringify(prev[k])){pairs.push([["planningTypeV2",k],v]);ptPending.current[k]=v;}
    });
    Object.keys(prev).forEach(k=>{if(!(k in (cur||{}))){pairs.push([["planningTypeV2",k],"__DELETE__"]);ptPending.current[k]=null;}});
    ptSynced.current=cur||{};
    if(pairs.length===0)return;
    localChange.current=true;
    (async()=>{
      try{for(let i=0;i<pairs.length;i+=400)await updatePaths(PLANNING_DOC,pairs.slice(i,i+400));}
      catch(e){console.log("sync PT:",e);setFbStatus("error");}
    })();
  },[]);

  useEffect(()=>{
    if(!PLANNING_DOC||!onSnapshot){setFbStatus("offline");return;}
    setFbStatus("connecting");
    const unsub=onSnapshot(PLANNING_DOC,
      (snap)=>{
        fromServer.current=true;   /* v10.28 : tout ce qui suit vient du serveur */
        if(snap.metadata&&snap.metadata.fromCache===false)serverSeen.current=true;
        if(snap.exists){
          const data0=snap.data();
          const data=data0;
          /* ── plan V2 (objet) : toujours appliqué, modifications locales en attente ré-appliquées jusqu'à confirmation ── */
          if(data.planV2){
            const incoming=data.planV2;
            const merged={...incoming};
            Object.keys(planPending.current).forEach(k=>{
              const pv=planPending.current[k];
              const confirmed=pv===null?!(k in incoming):JSON.stringify(incoming[k])===JSON.stringify(pv);
              if(confirmed)delete planPending.current[k];
              else{if(pv===null)delete merged[k];else merged[k]=pv;}
            });
            planSynced.current=merged;
            setPlan(merged);
            if(data.plan&&updatePaths)Promise.resolve(updatePaths(PLANNING_DOC,[[["plan"],"__DELETE__"]])).catch(()=>{}); // purge de l'ancien format (économie de stockage)
          }else if(data.plan&&!planMigrated.current){
            /* ── migration douce : première lecture de l'ancien format chaîne → écriture unique en V2 ── */
            const legacy=JSON.parse(data.plan);
            planSynced.current=legacy;setPlan(legacy);
            planMigrated.current=true;
            if(setDoc)Promise.resolve(setDoc(PLANNING_DOC,{planV2:legacy},{merge:true})).catch(e=>console.log("migration plan:",e));
          }
          /* ── planning type V2 : même mécanique que le plan ── */
          if(data.planningTypeV2){
            const incPT=data.planningTypeV2;
            const mergedPT={...incPT};
            Object.keys(ptPending.current).forEach(k=>{
              const pv=ptPending.current[k];
              const confirmed=pv===null?!(k in incPT):JSON.stringify(incPT[k])===JSON.stringify(pv);
              if(confirmed)delete ptPending.current[k];
              else{if(pv===null)delete mergedPT[k];else mergedPT[k]=pv;}
            });
            ptSynced.current=mergedPT;
            setPlanningType(mergedPT);
          }else if(data.planningType&&!ptMigrated.current){
            /* migration douce : ancien bloc unique → écriture unique en V2, l'ancien champ
               est CONSERVÉ (jamais purgé) comme filet de sécurité */
            const legacyPT=JSON.parse(data.planningType);
            ptSynced.current=legacyPT;setPlanningType(legacyPT);
            ptMigrated.current=true;
            if(serverSeen.current&&setDoc)Promise.resolve(setDoc(PLANNING_DOC,{planningTypeV2:legacyPT},{merge:true})).catch(e=>console.log("migration PT:",e));
          }
          /* ── v9.44 : on n'écarte plus le message entier dès qu'une sauvegarde locale est en
             vol — on n'écarte que les champs qu'on est justement en train d'écrire. Tout le
             reste est appliqué, y compris ce qui vient d'un autre poste. ── */
          {
            const resend={};
            const data=(()=>{const o={};Object.keys(data0).forEach(k=>{
              const inc=JSON.stringify(data0[k]);
              const p=pendF.current[k];
              if(p){
                if(p.s===inc)delete pendF.current[k];            // notre écriture est arrivée : on peut suivre le serveur
                else if(p.n<3){p.n++;resend[k]=p.v;return;}      // écho en retard : on garde le local ET on le renvoie
                else return;                                     // renvois épuisés : on garde le local, jamais d'écrasement
              }
              o[k]=data0[k];
              fieldSync.current[k]=inc;                          // reçu = déjà au serveur, inutile de le renvoyer
            });return o;})();
            if(Object.keys(resend).length){Object.keys(resend).forEach(k=>{delete fieldSync.current[k];});setTimeout(()=>saveToFirebase(resend),400);}
            if(data.tourMed)setTourMed(JSON.parse(data.tourMed));
            if(data.notes)setNotes(JSON.parse(data.notes));
            /* ── médecins : version découpée si elle existe, sinon migration ── */
            if(data.medecinsV2){setMedecins(readList("medecinsV2",data.medecinsV2,data.medecinsV2Order));}
            else if(data.medecins&&!listMigrated.current.medecinsV2){
              const arrM=JSON.parse(data.medecins);listMigrated.current.medecinsV2=1;setMedecins(arrM);
              if(serverSeen.current&&setDoc){const mp={};arrM.forEach(x=>{if(x&&x.id!==undefined)mp[String(x.id)]=x;});
                Promise.resolve(setDoc(PLANNING_DOC,{medecinsV2:mp,medecinsV2Order:arrM.map(x=>String(x.id))},{merge:true})).catch(e=>console.log("migration medecins:",e));}
            }
            if(data.actesV2||data.actes){
            const arrA=data.actesV2?readList("actesV2",data.actesV2,data.actesV2Order):JSON.parse(data.actes);
            arrA.forEach(a=>{if(a&&a.id==="BIP"&&a.recapSite===undefined&&!(a.recapSites&&a.recapSites.length))a.recapSites=["CHB"];});
            if(!arrA.some(a=>a&&a.id==="TP"))arrA.push({id:"TP",label:"Temps partiel",short:"TP",color:"#8b949e",bg:"#8b949e",hasSalle:false,salles:[]});
            setActes(arrA);
            if(!data.actesV2&&!listMigrated.current.actesV2){
              listMigrated.current.actesV2=1;
              if(serverSeen.current&&setDoc){const mp={};arrA.forEach(x=>{if(x&&x.id!==undefined)mp[String(x.id)]=x;});
                Promise.resolve(setDoc(PLANNING_DOC,{actesV2:mp,actesV2Order:arrA.map(x=>String(x.id))},{merge:true})).catch(e=>console.log("migration actes:",e));}
            }
          }
            if(data.editPin)setEditPin(data.editPin);
            if(data.adminPin!==undefined)setAdminPin(data.adminPin);
          if(data.cadrePin!==undefined)setCadrePin(data.cadrePin);
          if(data.ideCfg){try{setIdeCfg(JSON.parse(data.ideCfg));}catch(e){}}
          if(data.intCfg){try{setIntCfg(pv=>({...pv,...JSON.parse(data.intCfg)}));}catch(e){}}
          if(data.ptOrder){try{setPtOrder(JSON.parse(data.ptOrder)||[]);}catch(e){}}
          if(data.specColors){try{setSpecColors(JSON.parse(data.specColors)||{});}catch(e){}}
          if(data.vacs!==undefined){try{setVacs(JSON.parse(data.vacs)||[]);}catch(e){}}
          if(data.vacRule!==undefined)setVacRule(!!data.vacRule);
          if(data.colOrder){try{setColOrder(JSON.parse(data.colOrder)||{});}catch(e){}}
            if(data.adminEnabled!==undefined)setAdminEnabled(data.adminEnabled);
            if(data.adminCanReports!==undefined)setAdminCanReports(data.adminCanReports);
            if(data.adminCanNotes!==undefined)setAdminCanNotes(data.adminCanNotes);
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
          if(data.build){try{setBuild(JSON.parse(data.build)||{});}catch(e){}}
          if(data.tourAvoid)setTourAvoid(JSON.parse(data.tourAvoid));
          if(data.tourWish)setTourWish(JSON.parse(data.tourWish));
          if(data.gardeAvoid)setGardeAvoid(JSON.parse(data.gardeAvoid));
          if(data.gardeWish)setGardeWish(JSON.parse(data.gardeWish));
          if(data.csBlanches)setCsBlanches(JSON.parse(data.csBlanches));
          if(data.csRep)setCsRep(JSON.parse(data.csRep));
          if(data.csActsSel)setCsActsSel(JSON.parse(data.csActsSel));
          if(data.csActsGlobal)setCsActsGlobal(JSON.parse(data.csActsGlobal));
          if(data.tourDerog)setTourDerog(JSON.parse(data.tourDerog));
          if(data.tourReport!==undefined&&data.tourReport!=="")setTourReport(data.tourReport);
          if(data.astReport!==undefined&&data.astReport!=="")setAstReport(data.astReport);
          /* v9.89 : le champ ABSENT signifie « jamais configuré » (on déduit alors les
             salles des activités) ; un champ PRÉSENT, même vide, est un choix délibéré. */
          if(data.salleReg!==undefined&&data.salleReg!==null&&data.salleReg!==""){setSalleReg(JSON.parse(data.salleReg)||[]);}
          else{
            const acts=data.actes?JSON.parse(data.actes):[];
            const found=acts.flatMap(a=>a.salles||[]).filter((s,i2,arr)=>arr.indexOf(s)===i2);
            const guess=(s)=>s.indexOf("Angio")===0?"ANGIO":(s.indexOf("CHB")===0||/B[eé]thune/i.test(s))?"CHB":(/Stim|EEP|Echo|ETO|Dobu/i.test(s)&&s.indexOf("CHL")!==0)?"PLATEAU":"CHL";
            if(found.length>0)setSalleReg(found.map(s=>({n:s,s:guess(s)})));
          }
          if(data.periodCfg)setPeriodCfg(JSON.parse(data.periodCfg));
          if(data.medPins)setMedPins(JSON.parse(data.medPins));
          }
          isFirstLoad.current=!serverSeen.current;
          localChange.current=false;
        }else{isFirstLoad.current=!serverSeen.current;}
        setFbStatus("ok");
      },
      (err)=>{console.error("Firebase:",err);setFbStatus("error");}
    );
    return()=>unsub();
  },[]);

  /* ── Sauvegardes automatiques : une par jour, 45 conservées (v10.0) ──
     Coût vérifié avant de changer : le document pèse ~227 Ko, donc 45 copies ≈ 10 Mo,
     soit 1 % du gigaoctet gratuit. La contrainte n'est pas le stockage. Règle unique
     et facile à expliquer : « les 45 derniers jours ». */
  const [backupList,setBackupList]=useState([]); // [{id,ts}]
  const [bkOpen,setBkOpen]=useState("");        // sauvegarde ancienne dépliée
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
      for(const it of items.slice(BK_KEEP)){
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
        if(cellHasAny(dm2[mid],["GARDE"]))nGardes++;
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
      /* v10.101 : l'aperçu lisait les champs d'AVANT la v9.7 (plan, medecins), purgés depuis —
         il annonçait donc une sauvegarde vide et toutes les cases actuelles « perdues ».
         Lecture du format actuel, avec repli sur l'ancien pour de très vieilles sauvegardes. */
      const bPlan=d.planV2?d.planV2:(d.plan?JSON.parse(d.plan):{});
      const bTour=d.tourMed?JSON.parse(d.tourMed):{};
      const bMeds=d.medecinsV2?Object.keys(d.medecinsV2).map(k2=>{const v2=d.medecinsV2[k2];return typeof v2==="string"?JSON.parse(v2):v2;}):(d.medecins?JSON.parse(d.medecins):[]);
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
  const [docDet,setDocDet]=useState(null);   /* v10.101 : poids par champ, pour le détail de la jauge */
  const [impWait,setImpWait]=useState(null);  /* v10.103 : fichier d'import lu, en attente de confirmation dans la page */
  const [archivedList,setArchivedList]=useState([]);
  const refreshArchList=useCallback(async()=>{
    try{
      const snap=await window.firebaseDB.collection("archives").get();
      const ids=[];snap.forEach(d2=>{if(d2.id&&d2.id.indexOf("per-")===0)ids.push(d2.id.slice(4));});
      ids.sort((a,b)=>{const x=a.split("-"),y2=b.split("-");return (+x[0]-+y2[0])||(+x[1]-+y2[1]);});setArchivedList(ids);return ids;
    }catch(e){return [];}
  },[]);
  useEffect(()=>{refreshArchList();},[refreshArchList]); /* v10.111 : le badge « période archivée » a besoin de la liste dès l'ouverture */
  useEffect(()=>{
    if(tab!=="partage")return;
    refreshBackupList();
    refreshArchList();
    (async()=>{
      try{
        const d=(await window.firebaseDB.collection("planning").doc("main").get()).data()||{};
        let bytes=0;const det={};
        Object.keys(d).forEach(k=>{
          const v=d[k];
          const s=typeof v==="string"?v:JSON.stringify(v);
          const b2=new Blob([k]).size+new Blob([s||""]).size+2;
          bytes+=b2;det[k]=b2;
        });
        setDocSize(bytes);setDocDet(det);
      }catch(e){setDocSize(null);setDocDet(null);}
    })();
  },[tab]);
  /* v10.0 : RESTAURATION CIBLÉE — un médecin, sur une période. La restauration globale
     existante remplace TOUT : utilisable après une catastrophe, pas après une maladresse,
     car elle écrase aussi le travail des autres depuis la sauvegarde. Ici on ne touche
     qu'aux cases du médecin choisi, sur les dates choisies : ce qui a été fait ailleurs
     est préservé. C'est le filet qui manquait maintenant qu'effacer une période est facile. */
  const restoreMedPeriod=useCallback(async(id,medId,dateFrom,dateTo)=>{
    try{
      const d=await window.firebaseDB.collection("backups").doc(id).get();
      const data=d.data();
      if(!data){toast("Sauvegarde introuvable","warn");return 0;}
      const old=data.planV2?data.planV2:(data.plan?JSON.parse(data.plan):null);
      if(!old){toast("Cette sauvegarde ne contient pas de planning","warn");return 0;}
      const [fy,fm,fd]=parseDate(dateFrom);
      const fromT=new Date(fy,fm,fd).getTime(),toT=new Date(...parseDate(dateTo)).getTime();
      /* calcul synchrone sur l'état courant : setPlan ne s'exécute pas immédiatement */
      const cles={};Object.keys(old).forEach(k=>cles[k]=1);Object.keys(plan).forEach(k=>cles[k]=1);
      const maj={};const pairs=[];let n=0;
      Object.keys(cles).forEach(k=>{
        const parts=k.split("|");if(parts.length<2)return;
        /* v10.4 : la clé s'écrit « 2026-08-10 » — mois EN CLAIR, donc 1-based. Je le
           relisais comme un mois technique (0-based), ce qui décalait tout d'un mois :
           aucune clé ne tombait dans la fenêtre demandée, d'où « rien à restaurer ». */
        const [yy,mm,dd]=parts[0].split("-").map(Number);
        const t=new Date(yy,mm-1,dd).getTime();
        if(t<fromT||t>toT)return;
        const av=(old[k]||{})[medId], mt=(plan[k]||{})[medId];
        if(cellKey(av)===cellKey(mt))return;
        const dm={...(plan[k]||{})};
        if(av===undefined||av===null||cellEs(av).length===0)delete dm[medId];
        else dm[medId]=av;
        maj[k]=dm;pairs.push([["planV2",k],dm]);n++;
      });
      if(n===0){toast("Rien à restaurer — déjà identique","info");return 0;}
      setPlan(p=>{const next={...p};Object.keys(maj).forEach(k=>{next[k]=maj[k];});return next;});
      if(updatePaths){
        for(let i2=0;i2<pairs.length;i2+=400)await updatePaths(PLANNING_DOC,pairs.slice(i2,i2+400));
      }
      toast(n+" case"+(n>1?"s":"")+" restaurée"+(n>1?"s":""),"info");
      return n;
    }catch(e){console.log("restore ciblee:",e);toast("Échec de la restauration","warn");return 0;}
  },[plan]);
  const restoreBackup=useCallback(async(id)=>{
    try{
      const d=await window.firebaseDB.collection("backups").doc(id).get();
      const data=d.data();
      if(!data){toast("Sauvegarde introuvable","warn");return;}
      const{_ts,...rest}=data;
      planPending.current={};planSynced.current=null;
      await window.firebaseDB.collection("planning").doc("main").set(rest); // remplacement complet : une restauration EST l'état intégral
      toast("Sauvegarde restaurée — rechargez la page si besoin","info");
    }catch(e){console.log("restore:",e);toast("Échec de la restauration","warn");}
  },[]);
  useEffect(()=>{
    // Au chargement : backup auto si la dernière date de plus de 72 h
    const t=setTimeout(async()=>{
      try{
        const d=await window.firebaseDB.collection("planning").doc("main").get();
        const last=(d.data()||{})._lastBackupAt||0;
        if(Date.now()-last>24*3600*1000)await makeBackup(false);   /* v10.0 : une par jour au lieu d'une tous les 3 jours */
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
            if(cellHasAny(dm2[mid],["TOUR_HC","TOUR_USIC"])){const r=cellDrop(dm2[mid],["TOUR_HC","TOUR_USIC"]);if(r)dm2[mid]=r;else delete dm2[mid];ch=true;}
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
    const PROT2=["ABSENCE","GARDE","REPOS_GARDE","FORM","FORMATION"]; // sans TP : il est retiré exprès des nouveaux tourneurs
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
            if(cellHasAny(e,PROT2))return;
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
    const PROT2=PROT_TOUR;
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
          if(cellHasAny(ex,PROT2))return;
          if(isOff){
            if(!next[k])next[k]={};
            next[k]={...next[k],[medId]:{acteId:"TP",salle:null}};
            return;
          }
          if(!pt||!pt[dw2])return;
          const[acteId,salle,a2x=null,s2x=null,a3x=null,s3x=null,c1x=null]=(pt[dw2][sl])||[null,null];
          if(!acteId)return;
          if(!next[k])next[k]={};
          next[k]={...next[k],[medId]:ptCell(acteId,salle,a2x,s2x,a3x,s3x,c1x)};
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
        if(cellHasAny(dm2[j.id],["TOUR_USIC"]))replCount[j.id]++;
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
        return !["M","AM"].some(sl=>cellHasAny((plan[sk(dy,dm3,dd,sl)]||{})[j.id],ABS_IDS.concat(["GARDE","REPOS_GARDE"])));
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
        if(cellHasAny(dm2[medId],["TP"])){const r=cellDrop(dm2[medId],["TP"]);if(r)dm2[medId]=r;else delete dm2[medId];ch=true;}
        Object.keys(dm2).forEach(mid=>{
          if(cellHasAny(dm2[mid],["TOUR_USIC"])){const r=cellDrop(dm2[mid],["TOUR_USIC"]);if(r)dm2[mid]=r;else delete dm2[mid];ch=true;}
        });
        if(ch)next[k]=dm2;
      });
      return next;
    });
  },[medecins]);

    const saveToFirebase=useCallback(async(data)=>{
    if(!PLANNING_DOC||!setDoc)return;
    if(!serverSeen.current)return;   // v9.71 : jamais d'écriture sur une base venant du seul cache
    /* v9.44 : on n'envoie que ce qui a réellement changé depuis la dernière valeur
       connue du champ — sinon chaque message reçu déclenchait sa propre réécriture. */
    const out={},ks=[];
    Object.keys(data||{}).forEach(k=>{
      const s=JSON.stringify(data[k]===undefined?null:data[k]);
      if(fieldSync.current[k]===s)return;
      fieldSync.current[k]=s;out[k]=data[k];ks.push(k);
    });
    if(ks.length===0)return;
    /* v9.70 : on retient la VALEUR envoyée, plus un simple compteur relâché après 1,5 s.
       Un champ n'est repris du serveur QUE lorsque l'écho confirme exactement ce qu'on a
       écrit ; sinon on garde la version locale et on la renvoie. Un message serveur en
       retard ne peut donc plus effacer une saisie récente — c'est déjà le principe de
       planPending pour le plan, qui lui n'a jamais perdu de données. */
    ks.forEach(k=>{const p=pendF.current[k];pendF.current[k]={v:data[k],s:fieldSync.current[k],n:p?p.n:0};});
    try{localChange.current=true;await setDoc(PLANNING_DOC,out,{merge:true});}
    catch(err){console.error("Save:",err);setFbStatus("error");ks.forEach(k=>{delete fieldSync.current[k];});}
  },[]);

  useEffect(()=>{if(!isFirstLoad.current)flushPlan(plan);},[plan]);
  useEffect(()=>{if(!isFirstLoad.current)saveToFirebase({tourMed:JSON.stringify(tourMed)});},[tourMed]);
  useEffect(()=>{if(!isFirstLoad.current)saveToFirebase({tourMins:JSON.stringify(tourMins)});},[tourMins]);
  useEffect(()=>{if(!isFirstLoad.current)saveToFirebase({tourMinsHard:JSON.stringify(tourMinsHard)});},[tourMinsHard]);
  useEffect(()=>{if(!isFirstLoad.current)saveToFirebase({tourCfg:JSON.stringify(tourCfg)});},[tourCfg]);
  useEffect(()=>{if(!isFirstLoad.current)saveToFirebase({build:JSON.stringify(build)});},[build]);
  useEffect(()=>{if(!isFirstLoad.current)saveToFirebase({tourAvoid:JSON.stringify(tourAvoid)});},[tourAvoid]);
  useEffect(()=>{if(!isFirstLoad.current)saveToFirebase({tourWish:JSON.stringify(tourWish)});},[tourWish]);
  useEffect(()=>{if(!isFirstLoad.current)saveToFirebase({gardeAvoid:JSON.stringify(gardeAvoid)});},[gardeAvoid]);
  useEffect(()=>{if(!isFirstLoad.current)saveToFirebase({gardeWish:JSON.stringify(gardeWish)});},[gardeWish]);
  useEffect(()=>{if(!isFirstLoad.current)saveToFirebase({csBlanches:JSON.stringify(csBlanches)});},[csBlanches]);
  useEffect(()=>{if(!isFirstLoad.current)saveToFirebase({csRep:JSON.stringify(csRep)});},[csRep]);
  useEffect(()=>{if(!isFirstLoad.current)saveToFirebase({csActsSel:JSON.stringify(csActsSel)});},[csActsSel]);
  useEffect(()=>{if(!isFirstLoad.current)saveToFirebase({csActsGlobal:JSON.stringify(csActsGlobal)});},[csActsGlobal]);
  useEffect(()=>{if(!isFirstLoad.current)saveToFirebase({tourDerog:JSON.stringify(tourDerog)});},[tourDerog]);
  useEffect(()=>{if(!isFirstLoad.current)saveToFirebase({tourReport:tourReport||""});},[tourReport]);
  useEffect(()=>{if(!isFirstLoad.current)saveToFirebase({astReport:astReport||""});},[astReport]);
  useEffect(()=>{if(!isFirstLoad.current)saveToFirebase({salleReg:JSON.stringify(salleReg)});},[salleReg]);
  // Consultation des archives : charge le DOCUMENT DE PÉRIODE de la période affichée
  // (v10.110 : un doc par période — une seule lecture au lieu de cinq, débordement compris).
  useEffect(()=>{
    const p=perStart(year,month);
    const pid=p.sy+"-"+p.sm;
    /* v10.108 : on ne devine pas « cette période n'est pas archivée » par la présence
       d'une case vivante ; on demande l'archive une fois par période et par session. */
    if(archFetched.current[pid])return;
    archFetched.current[pid]=true;
    window.firebaseDB.collection("archives").doc("per-"+pid).get().then(snap=>{
      const d=snap&&snap.data&&snap.data();
      if(d&&d.plan){const frag=JSON.parse(d.plan);if(Object.keys(frag).length>0)setArchPlan(pp=>Object.assign({},pp,frag));}
      /* les annexes RELUES rejoignent le cache — sans elles, une période archivée
         s'afficherait sans son tour et sans ses notes. */
      if(d&&d.annex){try{const an=JSON.parse(d.annex)||{};const add={};
        AR_LU.forEach(ch=>{if(an[ch]&&Object.keys(an[ch]).length)add[ch]=an[ch];});
        if(Object.keys(add).length)setArchAnx(pp=>{const o=Object.assign({},pp);Object.keys(add).forEach(ch=>{o[ch]=arFusion(ch,o[ch]||{},add[ch]);});return o;});
      }catch(e2){}}
    }).catch(()=>{});
  },[year,month]);
  useEffect(()=>{if(!isFirstLoad.current)saveToFirebase({periodCfg:JSON.stringify(periodCfg)});},[periodCfg]);
  useEffect(()=>{if(!isFirstLoad.current)flushPT(planningType);},[planningType]);
  useEffect(()=>{if(!isFirstLoad.current)saveToFirebase({notes:JSON.stringify(notes)});},[notes]);
  useEffect(()=>{if(!isFirstLoad.current)flushList("medecinsV2",medecins);},[medecins]);
  useEffect(()=>{if(!isFirstLoad.current)flushList("actesV2",actes);},[actes]);
  // ── Source de vérité : coche "Garde" de l'onglet Équipe → médecins autorisés des activités GARDE et REPOS_GARDE ──
  useEffect(()=>{
    const gInits=medecins.filter(m=>m.garde===true).map(m=>m.init);
    const tpInits=medecins.filter(m=>m.partTime===true).map(m=>m.init);
    const gKey=[...gInits].sort().join(","),tpKey=[...tpInits].sort().join(",");
    setActes(prev=>{
      let changed=false;
      const next=prev.map(a=>{
        const syncG=(a.id==="GARDE"||a.id==="REPOS_GARDE"),syncTP=a.id==="TP";
        if(!syncG&&!syncTP)return a;
        const target=syncG?gInits:tpInits,key=syncG?gKey:tpKey;
        const cur=a.medecinsAutorise||[];
        if([...cur].sort().join(",")===key)return a;
        changed=true;return {...a,medecinsAutorise:target};
      });
      return changed?next:prev;
    });
  },[medecins]);
  useEffect(()=>{if(!isFirstLoad.current)saveToFirebase({editPin});},[editPin]);
  useEffect(()=>{if(!isFirstLoad.current)saveToFirebase({adminPin,cadrePin,adminEnabled,adminCanReports,adminCanNotes});},[adminPin,cadrePin,adminEnabled,adminCanReports,adminCanNotes]);
  useEffect(()=>{if(!isFirstLoad.current)saveToFirebase({ideCfg:JSON.stringify(ideCfg)});},[ideCfg]);
  useEffect(()=>{if(!isFirstLoad.current)saveToFirebase({intCfg:JSON.stringify(intCfg)});},[intCfg]);
  useEffect(()=>{if(!isFirstLoad.current)saveToFirebase({ptOrder:JSON.stringify(ptOrder)});},[ptOrder]);
  useEffect(()=>{if(!isFirstLoad.current)saveToFirebase({specColors:JSON.stringify(specColors)});},[specColors]);
  useEffect(()=>{if(!isFirstLoad.current)saveToFirebase({vacs:JSON.stringify(vacs),vacRule:vacRule?1:0});},[vacs,vacRule]);
  useEffect(()=>{if(!isFirstLoad.current)saveToFirebase({colOrder:JSON.stringify(colOrder)});},[colOrder]);
  const moveCol=(siteKey,key,dir)=>{
    const cur=(colOrder[siteKey]&&colOrder[siteKey].length)?colOrder[siteKey].slice():((colModal&&colModal.cols)?colModal.cols.slice():[]);
    const i=cur.indexOf(key),j=i+dir;
    if(i<0||j<0||j>=cur.length)return;
    const nx=cur.slice();nx[i]=cur[j];nx[j]=cur[i];
    setColOrder(p=>({...p,[siteKey]:nx}));
    setColModal(m=>m?{...m,cols:nx}:m);
  };
  /* Les lignes de PT Cardio, fixes et automatiques réunies, rangées selon ptOrder. */
  /* v9.77 — SOURCE DES COLONNES DE PT CARDIO. Jusqu'ici PT Cardio était le seul
     onglet dont 6 colonnes étaient écrites en dur ; les 3 autres déduisent tout des
     données. Désormais lui aussi : une colonne par salle déclarée (les activités qui
     partagent une salle se regroupent), une colonne par activité à plusieurs salles.
     Vérifié au préalable sur les données réelles : résultat identique aux 6 colonnes. */
  const ptRowsDerived=useMemo(()=>{
    const cand=actes.filter(a=>!a.isSystem&&(acteRecapIn(a,"PLATEAU")||PT_FIXED_ROWS.some(r=>(r.ids||[]).includes(a.id))));
    const bySalle={},out=[];
    cand.forEach(a=>{
      const sl=a.salles||[];
      if(sl.length===1){
        const k="SALLE:"+sl[0];
        if(!bySalle[k]){bySalle[k]={key:k,label:sl[0],ids:[],color:a.color,salle:sl[0]};out.push(bySalle[k]);}
        bySalle[k].ids.push(a.id);
      } else if(sl.length>1){
        out.push({key:a.id,label:a.label,ids:[a.id],color:a.color,salle:null,hasSalleChoice:true,sallesDisp:sl});
      } else {
        out.push({key:a.id,label:a.label,ids:[a.id],color:a.color,salle:null});
      }
    });
    return out;
  },[actes]);
  /* PT_FIXED_ROWS ne sert plus qu'à retrouver le NOM, la COULEUR et la CLÉ d'ordre des
     six colonnes historiques : l'ordre enregistré (clés ROW_*) est ainsi conservé. */
  const ptRows=useMemo(()=>{
    const all=ptRowsDerived.map(r=>{
      const fx=PT_FIXED_ROWS.find(f=>(f.ids||[]).some(i=>(r.ids||[]).includes(i)));
      return fx?{...r,key:fx.key,label:fx.label,color:fx.color}:r;
    });
    const rank=k=>{const i=(ptOrder||[]).indexOf(k);return i<0?9999:i;};
    return all.map((r,i)=>({r,i})).sort((a,b)=>(rank(a.r.key)-rank(b.r.key))||(a.i-b.i)).map(x=>x.r);
  },[ptRowsDerived,ptOrder]);
  const movePtRow=(key,dir)=>{
    const cur=ptRows.map(r=>r.key);
    const i=cur.indexOf(key),j=i+dir;
    if(i<0||j<0||j>=cur.length)return;
    const nx=cur.slice();nx[i]=cur[j];nx[j]=cur[i];
    setPtOrder(nx);
  };
  useEffect(()=>{if(!isFirstLoad.current)saveToFirebase({astreinte:JSON.stringify(astreinte)});},[astreinte]);
  useEffect(()=>{if(!isFirstLoad.current)saveToFirebase({medPins:JSON.stringify(medPins)});},[medPins]);

  useEffect(()=>{ applyTheme(darkMode); },[darkMode]);
  /* v10.106 : sur iPhone, telecharger le fichier d'archive met la page en arriere-plan
     et iOS gele les minuteries — le message restait affiche jusqu'a quitter la session.
     Il s'efface donc aussi au retour au premier plan (et un clic le chasse). */
  useEffect(()=>{const f=()=>{if(!document.hidden)setNotif(null);};
    document.addEventListener("visibilitychange",f);
    return()=>document.removeEventListener("visibilitychange",f);},[]);
  /* v10.112 : UN SEUL minuteur d'effacement, réarmé à chaque message — deux toasts
     rapprochés se volaient l'effacement, et un minuteur gelé par iOS (leçon v10.106)
     laissait le message affiché sans fin. Le changement d'onglet le chasse aussi. */
  const notifTRef=useRef(0);
  const toast=(msg,type="ok")=>{ setNotif({msg,type}); clearTimeout(notifTRef.current); notifTRef.current=setTimeout(()=>setNotif(null),3500); };
  useEffect(()=>{setNotif(null);},[tab]);
  const acteById=useCallback(id=>actes.find(a=>a.id===id),[actes]);
  const isEdit=(accessMode==="edit"||(accessMode==="medecinEdit"&&(((medecins.find(m=>m.id===editMedId)||{}).niveau)||"basic")==="editeur"&&(((medecins.find(m=>m.id===editMedId)||{}).role)||"medecin")!=="attache"))&&!netOff;  /* v10.73 : jamais d'attache editeur */ // hors ligne : lecture seule
  /* v10.106 : borne du verrou (voir le bloc au-dessus de CardioPlanning). Calculee
     une fois : elle ne bouge qu'au changement de periode ou de calendrier scolaire. */
  const verrouDeb=useMemo(()=>verrouDebut(),[PCFG.len,PCFG.startM,vacs]);
  const estClos=useCallback((y2,m2,d2)=>dKey(y2,m2,d2)<verrouDeb,[verrouDeb]);
  /* la periode AFFICHEE est-elle close ? (son dernier jour precede la borne) */
  const perClose=useMemo(()=>{const p=perStart(year,month);const e=perEnd(p.sy,p.sm);
    return dKey(e.getFullYear(),e.getMonth(),e.getDate())<verrouDeb;},[year,month,verrouDeb]);
  /* v10.111 : la période affichée est-elle ARCHIVÉE ? Badge et messages dédiés —
     sa demande : distinguer à l'écran une période close d'une période archivée. */
  const perArchivee=useMemo(()=>{const p=perStart(year,month);return archivedList.indexOf(p.sy+"-"+p.sm)>=0;},[year,month,archivedList]);
  /* v10.108 : l'interrupteur de Parametres. Session seulement — aucun
     localStorage, aucun Firestore : le verrou se remet en place tout seul. */
  const [vUnlock,setVUnlock]=useState(false);
  const vRef=useRef({deb:verrouDeb,passe:false,ed:false});
  vRef.current={deb:verrouDeb,passe:isEdit&&vUnlock,ed:isEdit,arch:perArchivee};
  /* un seul message par geste : les operations de masse appellent l'ecriture en boucle */
  const vTRef=useRef(0);
  const vToast=useCallback((passe)=>{
    const n=Date.now();if(n-vTRef.current<1500)return;vTRef.current=n;
    setNotif({msg:passe?"⚠ Période close — modification enregistrée quand même":(vRef.current.arch?"🗄 Période archivée — modification impossible (désarchivage dans Paramètres)":vRef.current.ed?"🔒 Période close — modification impossible (déverrouillage dans Paramètres)":"🔒 Période close — modification impossible"),type:passe?"warn":"lock"});
    clearTimeout(notifTRef.current);notifTRef.current=setTimeout(()=>setNotif(null),3500);
  },[]);
  // ─── Undo/Redo history (edit mode) ───
  const histRef=useRef({stack:[],pas:[],idx:-1,restoring:0});
  /* v10.28 : un changement recu du SERVEUR n'est pas une action de cette personne.
     Sans ce drapeau, le travail d'un collegue entrait dans MA pile et mon retour
     arriere le defaisait. Il est leve par le gestionnaire de messages Firestore et
     rabaisse apres CHAQUE rendu (effet sans dependances, declare juste apres celui
     de l'historique) : meme un message qui ne change rien ne le laisse pas colle. */
  const fromServer=useRef(false);
  const [histVer,setHistVer]=useState(0);
  /* v10.27 : les trois donnees de l'onglet Reports entrent dans l'historique.
     Avant, poser un report ecrivait un commentaire (donc creait un cran) mais le
     report lui-meme restait hors photo : un retour arriere retirait le commentaire
     et laissait le report en place — les deux donnees se contredisaient. Cocher
     « rouvert » ou une semaine blanche ne creait, lui, aucun cran du tout. */
  const histSnapshot=()=>({plan,tourMed,astreinte,notes,planningType,csBlanches,csRep,csActsSel});
  /* v10.8 : sérialisation à CLÉS TRIÉES. Mon dédoublonnage de la v10.7 comparait deux
     textes bruts ; or l'écho du serveur renvoie les mêmes données dans un ORDRE DE CLÉS
     différent, donc le doublon passait quand même et le premier « retour » revenait sur
     un état identique. Avec un ordre stable, deux états de même contenu sont reconnus
     égaux — et le drapeau de restauration devient d'ailleurs superflu, l'état restauré
     étant par construction égal au cran visé. */
  const histStr=(o)=>JSON.stringify(o,(k,v)=>(v&&typeof v==="object"&&!Array.isArray(v))
    ?Object.keys(v).sort().reduce((a,x)=>{a[x]=v[x];return a;},{}):v);
  useEffect(()=>{
    const h=histRef.current;
    /* v10.6 : pendant le chargement on ne remplit pas la pile, mais on RETIENT l'état
       courant. Sans lui, la pile ne contenait après la première pose qu'un seul cran —
       celui d'APRÈS — et le premier clic sur « retour » reculait vers ce même état :
       rien ne bougeait à l'écran et il fallait cliquer deux fois. */
    if(isFirstLoad.current){h.depart=histStr(histSnapshot());return;}
    /* v10.5 : une annulation change CINQ états d'un coup (plan, tour, astreinte, notes,
       planning type). L'ancien drapeau était consommé par le premier signal reçu ; les
       quatre suivants étaient donc enregistrés comme de NOUVELLES actions, ce qui effaçait
       aussitôt la branche de rétablissement — d'où le bouton « avant » qui s'allumait puis
       se grisait. On compte désormais les cinq signaux avant de rendre la main. */
    if(h.restoring>0){h.restoring--;
      /* v10.77 : apres un retour, le sommet vaut l'etat REEL (le mien defait, celui
         des autres intact). Sans cela le pas suivant reprendrait leurs cases. */
      const sr=histStr(histSnapshot());
      if(h.idx>=0&&h.stack.length)h.stack[h.idx]=sr;else h.depart=sr;
      return;}
    /* v10.77 : un message du serveur ne cree pas de cran, mais il MET A JOUR le
       sommet de la pile. Sans cela, la modification du collegue entrait dans ma
       photo suivante, et mon retour arriere la supprimait (bug reproduit en 4
       gestes le 17/08/2026). Le sommet remis a jour, le prochain cran ne contient
       plus que MON geste. */
    if(fromServer.current){
      const sv=histStr(histSnapshot());
      if(h.idx>=0&&h.stack.length)h.stack[h.idx]=sv;else h.depart=sv;
      return;
    }
    if(h.stack.length===0&&h.depart){h.stack.push(h.depart);h.pas=[null];h.idx=0;}
    /* v10.7 : une seule pose déclenche DEUX fois cet effet — la modification, puis l'écho
       du serveur qui repose le même contenu dans un nouvel objet. Deux crans identiques
       étaient donc empilés, et le premier « retour » revenait sur un état identique :
       rien ne bougeait, d'où les deux clics nécessaires. Le « avant » n'était pas touché,
       puisqu'il avançait vers un cran réellement différent. On n'empile plus un état
       identique au sommet de la pile. */
    const snap=histStr(histSnapshot());
    if(h.stack[h.idx]===snap)return;
    // Truncate redo branch, push snapshot
    const pas=h.idx>=0?histPas(h.stack[h.idx],snap):null;   /* v10.77 : ce que CE geste a change */
    h.stack=h.stack.slice(0,h.idx+1);
    h.pas=(h.pas||[null]).slice(0,h.idx+1);
    h.stack.push(snap);h.pas.push(pas);
    if(h.stack.length>50){h.stack.shift();h.pas.shift();}
    h.idx=h.stack.length-1;
    setHistVer(v=>v+1);
  },[plan,tourMed,astreinte,notes,planningType,csBlanches,csRep,csActsSel]);
  /* Sans dependances : s'execute a chaque rendu, donc toujours APRES l'effet
     ci-dessus (les effets s'executent dans l'ordre de declaration). */
  useEffect(()=>{fromServer.current=false;});
  /* ── v10.28 : un retour arriere applique la DIFFERENCE entre le cran quitte et
     le cran vise, jamais la photo entiere. Une case modifiee entre-temps par
     quelqu'un d'autre n'apparait dans aucun des deux crans : elle est donc laissee
     telle quelle au lieu d'etre ecrasee par un etat perime. ── */
  const memeVal=(a,b)=>histStr(a===undefined?null:a)===histStr(b===undefined?null:b);
  /* un niveau de cles (notes, astreinte, tour, planning type, donnees de Reports) */
  const deltaObj=(av,ap,cur)=>{
    const A=av||{},B=ap||{},out={...(cur||{})};
    const cles={};Object.keys(A).forEach(k=>cles[k]=1);Object.keys(B).forEach(k=>cles[k]=1);
    Object.keys(cles).forEach(k=>{
      if(memeVal(A[k],B[k]))return;                 /* l'action n'a pas touche a cette cle */
      if(B[k]===undefined)delete out[k];else out[k]=B[k];
    });
    return out;
  };
  /* le planning a DEUX niveaux : demi-journee, puis medecin — deux personnes
     peuvent modifier la meme demi-journee sur des lignes differentes */
  const deltaPlan=(av,ap,cur)=>{
    const A=av||{},B=ap||{},out={...(cur||{})};
    const cles={};Object.keys(A).forEach(k=>cles[k]=1);Object.keys(B).forEach(k=>cles[k]=1);
    Object.keys(cles).forEach(k=>{
      const a2=A[k]||{},b2=B[k]||{};
      if(memeVal(a2,b2))return;
      const c2={...(out[k]||{})};const ids={};
      Object.keys(a2).forEach(x=>ids[x]=1);Object.keys(b2).forEach(x=>ids[x]=1);
      Object.keys(ids).forEach(x=>{
        if(cellKey(a2[x])===cellKey(b2[x]))return;
        if(b2[x]===undefined)delete c2[x];else c2[x]=b2[x];
      });
      if(Object.keys(c2).length===0)delete out[k];else out[k]=c2;
    });
    return out;
  };
  /* ── v10.77 : un cran retient la LISTE des cases qu'il a changees. Le retour
     arriere ne touche que celles-la : ce qu'un collegue a pose entre-temps n'est
     jamais dans la liste, donc jamais defait. ── */
  const delObj=(A,B)=>{
    const a=A||{},b=B||{},cles={},out={};
    Object.keys(a).forEach(k=>cles[k]=1);Object.keys(b).forEach(k=>cles[k]=1);
    Object.keys(cles).forEach(k=>{if(!memeVal(a[k],b[k]))out[k]=[a[k],b[k]];});
    return out;
  };
  const delPlan=(A,B)=>{
    const a=A||{},b=B||{},cles={},out={};
    Object.keys(a).forEach(k=>cles[k]=1);Object.keys(b).forEach(k=>cles[k]=1);
    Object.keys(cles).forEach(k=>{
      const a2=a[k]||{},b2=b[k]||{};
      if(memeVal(a2,b2))return;
      const ids={},d={};Object.keys(a2).forEach(x=>ids[x]=1);Object.keys(b2).forEach(x=>ids[x]=1);
      Object.keys(ids).forEach(x=>{if(cellKey(a2[x])!==cellKey(b2[x]))d[x]=[a2[x],b2[x]];});
      if(Object.keys(d).length)out[k]=d;
    });
    return out;
  };
  const HIST_CHAMPS=["tourMed","astreinte","notes","planningType","csBlanches","csRep","csActsSel"];
  const histPas=(snAv,snAp)=>{
    try{
      const A=JSON.parse(snAv),B=JSON.parse(snAp);
      const p={plan:delPlan(A.plan,B.plan)};
      HIST_CHAMPS.forEach(c=>{p[c]=delObj(A[c],B[c]);});
      return p;
    }catch(e){return null;}
  };
  /* pose des seules cases du pas ; null ou undefined = case vidée */
  const posePlan=(cur,d)=>{
    const out={...(cur||{})};
    Object.keys(d||{}).forEach(k=>{
      const c2={...(out[k]||{})};
      Object.keys(d[k]).forEach(x=>{const v=d[k][x];if(v===undefined||v===null)delete c2[x];else c2[x]=v;});
      if(Object.keys(c2).length===0)delete out[k];else out[k]=c2;
    });
    return out;
  };
  const poseObj=(cur,d)=>{
    const out={...(cur||{})};
    Object.keys(d||{}).forEach(k=>{const v=d[k];if(v===undefined||v===null)delete out[k];else out[k]=v;});
    return out;
  };
  const nbCases=(pas)=>pas?Object.keys(pas.plan||{}).reduce((n,k)=>n+Object.keys(pas.plan[k]).length,0):0;
  /* compte les cases du planning que le pas va reellement changer — garde-fou.
     v10.28 : compte le PAS (cran quitte -> cran vise), plus l'ecart avec l'etat
     courant, qui incluait a tort les modifications des autres. */
  const histDiff=(snAv,snAp)=>{
    try{
      const A=(JSON.parse(snAv).plan)||{},B=(JSON.parse(snAp).plan)||{};let n=0;
      const cles={};Object.keys(A).forEach(k=>cles[k]=1);Object.keys(B).forEach(k=>cles[k]=1);
      Object.keys(cles).forEach(k=>{
        const a2=A[k]||{},b2=B[k]||{};const ids={};
        Object.keys(a2).forEach(x=>ids[x]=1);Object.keys(b2).forEach(x=>ids[x]=1);
        Object.keys(ids).forEach(x=>{if(cellKey(a2[x])!==cellKey(b2[x]))n++;});
      });
      return n;
    }catch(e){return 0;}
  };
  /* v10.77 : on ne repose QUE les cases du pas, et seulement si elles valent encore
     ce qu'elles valaient. Une case reprise entre-temps par quelqu'un d'autre est
     laissée telle quelle — on le signale plutôt que de trancher à sa place. */
  const applyStep=(snAv,snAp,pas,sens)=>{
    const P=pas||histPas(snAv,snAp)||{plan:{}};
    const s=sens<0?1:0;                 /* retour : l'état attendu est l'APRÈS du geste */
    const att=v=>v[s], vis=v=>v[1-s];
    let nc=0;
    const cur={plan,tourMed,astreinte,notes,planningType,csBlanches,csRep,csActsSel};
    const dPlan={};
    Object.keys(P.plan||{}).forEach(k=>{
      const c2=(cur.plan||{})[k]||{},d={};
      Object.keys(P.plan[k]).forEach(x=>{
        const v=P.plan[k][x];
        if(cellKey(c2[x])!==cellKey(att(v))){nc++;return;}
        d[x]=vis(v);
      });
      if(Object.keys(d).length)dPlan[k]=d;
    });
    const dCh={};
    HIST_CHAMPS.forEach(c=>{
      const d={};
      Object.keys(P[c]||{}).forEach(k=>{
        const v=P[c][k];
        if(!memeVal((cur[c]||{})[k],att(v))){nc++;return;}
        d[k]=vis(v);
      });
      dCh[c]=d;
    });
    histRef.current.restoring=1;   /* React regroupe les huit changements en un seul rendu */
    setPlan(c=>posePlan(c,dPlan));
    setTourMed(c=>poseObj(c,dCh.tourMed));
    setAstreinte(c=>poseObj(c,dCh.astreinte));
    setNotes(c=>poseObj(c,dCh.notes));
    setPlanningType(c=>poseObj(c,dCh.planningType));
    setCsBlanches(c=>poseObj(c,dCh.csBlanches));
    setCsRep(c=>poseObj(c,dCh.csRep));
    setCsActsSel(c=>poseObj(c,dCh.csActsSel));
    if(nc>0)toast(nc>1?(nc+" cases ont été modifiées depuis par quelqu'un d'autre — laissées telles quelles"):"Une case a été modifiée depuis par quelqu'un d'autre — laissée telle quelle","warn");
  };
  const canUndo=histRef.current.idx>0;
  const canRedo=histRef.current.idx<histRef.current.stack.length-1;
  const HIST_SEUIL=5;   /* au-delà, on demande confirmation : une action de masse ne se défait pas par mégarde */
  const doUndo=()=>{
    const h=histRef.current;
    if(h.idx<=0)return;
    const n=nbCases(h.pas&&h.pas[h.idx])||histDiff(h.stack[h.idx],h.stack[h.idx-1]);
    if(n>HIST_SEUIL){setHistConf({sens:"undo",n});return;}
    applyStep(h.stack[h.idx],h.stack[h.idx-1],h.pas&&h.pas[h.idx],-1);h.idx--;setHistVer(v=>v+1);
  };
  const [histConf,setHistConf]=useState(null);
  const histGo=()=>{
    const h=histRef.current;
    if(histConf&&histConf.sens==="undo"){if(h.idx>0){applyStep(h.stack[h.idx],h.stack[h.idx-1],h.pas&&h.pas[h.idx],-1);h.idx--;setHistVer(v=>v+1);}}
    else{if(h.idx<h.stack.length-1){applyStep(h.stack[h.idx],h.stack[h.idx+1],h.pas&&h.pas[h.idx+1],1);h.idx++;setHistVer(v=>v+1);}}
    setHistConf(null);
  };
  const doRedo=()=>{
    const h=histRef.current;
    if(h.idx>=h.stack.length-1)return;
    const n=nbCases(h.pas&&h.pas[h.idx+1])||histDiff(h.stack[h.idx],h.stack[h.idx+1]);
    if(n>HIST_SEUIL){setHistConf({sens:"redo",n});return;}
    applyStep(h.stack[h.idx],h.stack[h.idx+1],h.pas&&h.pas[h.idx+1],1);h.idx++;setHistVer(v=>v+1);
  };
  /* ── v9.11 : niveaux de droits (basic | inter | editeur) portés par la fiche médecin ── */
  const medLvl=accessMode==="medecinEdit"?(((medecins.find(m=>m.id===editMedId)||{}).niveau)||"basic"):null;
  const isMedEdit=accessMode==="medecinEdit"&&medLvl!=="editeur"&&!netOff;
  const isInterEdit=accessMode==="medecinEdit"&&medLvl==="inter"&&!netOff;
  /* v10.73 : un ATTACHE connecte n'agit QUE dans l'onglet Attaches — sa ligne,
     plus les lignes d'attaches cochees dans sa fiche s'il est intermediaire. */
  const isAttEdit=accessMode==="medecinEdit"&&!netOff&&((((medecins.find(m=>m.id===editMedId)||{}).role)||"medecin")==="attache");
  const attPeutMod=(medId)=>{const me=medecins.find(m=>m.id===editMedId)||{};const t=medecins.find(m=>m.id===medId)||{};
    return (((t.role)||"medecin")==="attache")&&((me.attEdit)||[]).indexOf(t.init)>=0;};
  /* v9.15 : visibilité des onglets unifiée par rôle — un onglet inutile au rôle n'est pas affiché */
  const hideTabs=accessMode==="interneEdit"?["construire","tourmedical","garde","astreinte","reports","attache","plantype","equipe","activites","stats","partage"]
    :accessMode==="adminEdit"?["activites","equipe","partage","plantype","stats","astreinte","construire"]
    :isMedEdit?["activites","equipe","partage"].concat(isInterEdit&&!isAttEdit?[]:["construire"])
    :accessMode==="view"?["tourmedical","activites","equipe","reports","stats","partage","construire"]:[];
  const canAst=isEdit||(accessMode==="medecinEdit"&&!netOff&&((medecins.find(m=>m.id===editMedId)||{}).astreinte===true));
  const orderedTabs=tabOrder.map(id=>DEFAULT_TABS.find(t2=>t2[0]===id)).filter(Boolean)
    .filter(([tid])=>hideTabs.indexOf(tid)<0&&HIDDEN_TABS.indexOf(tid)<0&&(tid!=="internes"||intCfg.show===true));
  useEffect(()=>{if(hideTabs.indexOf(tab)>=0||HIDDEN_TABS.indexOf(tab)>=0||(tab==="internes"&&intCfg.show!==true))setTab(accessMode==="interneEdit"?"internes":"planning");},[accessMode,tab,isMedEdit,intCfg]);
  const isAdminEdit=accessMode==="adminEdit"&&!netOff;
  const isInterne=accessMode==="interneEdit"&&!netOff; /* v10.69 : interne connecte (hors ligne = lecture seule) */
  /* v10.100 : le bandeau de role du bas confirme sous quel acces on est entre,
     puis ne sert plus a rien et mange de la hauteur. Il s'efface au bout de
     6 secondes. doFit mesure les bandeaux a CHAQUE rendu : ce changement
     d'etat rend donc la place aux grilles tout seul. */
  const [botOn,setBotOn]=useState(true);
  useEffect(()=>{setBotOn(true);const t=setTimeout(()=>setBotOn(false),6000);return ()=>clearTimeout(t);},[accessMode]);
  const roleOkKey=isCadre?"cadreOk":"adminOk"; // v10.50 : la coche d'activité du rôle connecté
  // Returns true if current user can edit this specific medecin's data
  const canEdit=(medId)=>isAttEdit
    ?((isMedEdit&&editMedId===medId)||(isInterEdit&&attPeutMod(medId)))
    :(isEdit||isInterEdit||(isMedEdit&&editMedId===medId)||isAdminEdit);
  const isAnyEdit=isEdit||isMedEdit||isAdminEdit;
  /* v10.81 : voir les preferences de tour et de garde dans le Planning.
     Editeur et intermediaire voient tout le monde ; un medecin basique ne voit que
     sa ligne. Ni l'administratif ni l'interne ni l'attache n'y ont acces. */
  const canPref=(isEdit||isInterEdit||isMedEdit)&&!isAttEdit&&!isAdminEdit&&!isInterne;
  const prefScope=(isEdit||isInterEdit)?null:(isMedEdit?editMedId:null);
  const prefFor=(medId,y2,m2,d2)=>{
    if(prefScope&&medId!==prefScope)return null;
    const wkP=wKey(y2,m2,d2),dkP=dKey(y2,m2,d2),dwP=dow(y2,m2,d2);
    const tour=(dwP>=1&&dwP<=5)?(((tourWish[wkP]||{})[medId])?"wish":(((tourAvoid[wkP]||{})[medId])?"avoid":null)):null;
    const garde=((gardeWish[dkP]||{})[medId])?"wish":(((gardeAvoid[dkP]||{})[medId])?"avoid":null);
    return (tour||garde)?{tour,garde}:null;
  };
  const gardePrefFor=(medId,y2,m2,d2)=>{const dkP=dKey(y2,m2,d2);
    return ((gardeWish[dkP]||{})[medId])?"wish":(((gardeAvoid[dkP]||{})[medId])?"avoid":null);};
  useEffect(()=>{authorRef.current=accessMode==="medecinEdit"?(((medecins.find(m=>m.id===editMedId)||{}).init)||"?"):(isAdminEdit?((adminName||"?")+(isCadre?" (cadre)":" (secrétaire)")):(isInterne?((interneName||"?")+" (interne)"):(isEdit?"Éditeur":"?")));},[accessMode,isEdit,isMedEdit,isAdminEdit,isInterne,editMedId,adminName,interneName,medecins]);
  useEffect(()=>{ // purge du journal au-delà de 1200 entrées (éditeur uniquement, garde les 1000 plus récentes)
    if(!isEdit||!window.firebaseDB)return;
    (async()=>{try{
      const d3=await window.firebaseDB.collection("planning").doc("journal").get();
      const es=(d3.data()||{}).entries||{};const ks=Object.keys(es);
      if(ks.length>1200){
        const kept={};ks.map(k2=>[k2,es[k2]&&es[k2].t||0]).sort((a,b)=>b[1]-a[1]).slice(0,1000).forEach(([k2])=>{kept[k2]=es[k2];});
        await window.firebaseDB.collection("planning").doc("journal").set({entries:kept});
      }
    }catch(e){}})();
  },[isEdit]);
  const openCellHistory=useCallback((medId2,y2,m2,d2,sl2)=>{
    setHistModal({medId:medId2,y:y2,m:m2,d:d2,sl:sl2,loading:true,list:[]});
    (async()=>{try{
      const d3=await window.firebaseDB.collection("planning").doc("journal").get();
      const es=(d3.data()||{}).entries||{};
      const key3=sk(y2,m2,d2,sl2);
      const list=Object.values(es).filter(e=>e&&e.k===key3&&String(e.md)===String(medId2)).sort((a,b)=>(b.t||0)-(a.t||0)).slice(0,30);
      setHistModal(h=>h?{...h,loading:false,list}:h);
    }catch(e){setHistModal(h=>h?{...h,loading:false,list:[]}:h);}})();
  },[]);
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
    return perDaysList(sy,sm).map(o=>({y:o.y,m:o.m,d:o.d,label:MOIS[o.m].slice(0,3)}));
  },[year,month]);


  /* v10.35 : le corps est passe dans `expEntries` au niveau module, pour que
     l'export lise le planning EXACTEMENT comme l'ecran. tourDerog rejoint les
     dependances au passage — il manquait, une derogation ne rafraichissait pas. */
  /* v10.105 : le tour, les dérogations et les notes d'un mois archivé viennent du
     cache d'archives. L'ACTIF gagne toujours. Les écritures restent sur l'état brut. */
  const tourMedAff=useMemo(()=>Object.keys(archAnx.tourMed).length?{...archAnx.tourMed,...tourMed}:tourMed,[tourMed,archAnx]);
  const tourDerogAff=useMemo(()=>Object.keys(archAnx.tourDerog).length?{...archAnx.tourDerog,...tourDerog}:tourDerog,[tourDerog,archAnx]);
  const notesAff=useMemo(()=>Object.keys(archAnx.notes).length?{...archAnx.notes,...notes}:notes,[notes,archAnx]);
  /* v10.111 : la fusion plan+archives est calculée UNE fois par changement, plus à
     CHAQUE appel — getEntries est appelé des milliers de fois par rendu, et étaler
     un objet de plusieurs centaines de clés à chaque appel gelait toute l'application
     dès qu'une archive était chargée (son signalement du 25/08/2026). */
  const planAff=useMemo(()=>Object.keys(archPlan).length>0?{...archPlan,...plan}:plan,[plan,archPlan]);
  const getEntries=useCallback((medId,y2,m2,d2,slot)=>{
    return expEntries(planAff,tourMedAff,tourDerogAff,medId,y2,m2,d2,slot);
  },[planAff,tourMedAff,tourDerogAff]);

  const getEntry=useCallback((medId,y2,m2,d2,slot)=>getEntries(medId,y2,m2,d2,slot)[0]||null,[getEntries]);

  /* ── isMedAvailable ── */
  const isMedAvailable=useCallback((med,y2,m2,d2,slot)=>{
    const check=slot==="N"?["N","JOUR"]:slot==="JOUR"?["JOUR","M","AM"]:[slot,"JOUR"];
    const ids=[],cIds=[];
    check.forEach(sl=>getEntries(med.id,y2,m2,d2,sl).forEach(e=>{if((e&&e.acteId)&&!e._blocked)(e.cond?cIds:ids).push(e.acteId);}));
    if(ids.some(id=>["ABSENCE","FORMATION"].includes(id)))return "blocked";
    /* v10.63 : toute double activité se signale, tour médical compris — non bloquant */
    if(ids.length)return "warning";
    if(cIds.length)return "cond";
    return "free";
  },[getEntries]);

  /* ── setEntry / addEntry / removeEntry ── */
  const setEntry=useCallback((medId,y2,m2,d2,slot,entry)=>{
    if(vBloque(vRef,y2,m2,d2)){vToast(false);return;}   /* v10.106 */
    const key=sk(y2,m2,d2,slot);
    setPlan(p=>{const dm={...(p[key]||{})};if(entry)dm[medId]=entry;else delete dm[medId];return{...p,[key]:dm};});
    logCell(entry?"add":"del",medId,y2,m2,d2,slot,entry?entry.acteId:null);
    if(vAvertit(vRef,y2,m2,d2))vToast(true);
  },[]);

  /* v9.58 : poser une activité FERME sur une case qui porte un choix ouvert, c'est
     TRANCHER — quel que soit le chemin (salle d'un onglet, modale de case, BIP auto),
     et que l'activité posée soit l'une des branches ou non. Les branches disparaissent
     et l'entrée posée garde leur mémoire dans `wasCond`, ce qui permet de rétablir le
     choix si on la retire ensuite. */
  const addEntry=useCallback((medId,y2,m2,d2,slot,entry)=>{
    if(vBloque(vRef,y2,m2,d2)){vToast(false);return;}   /* v10.106 */
    const key=sk(y2,m2,d2,slot);
    let refusedBy=null;
    setPlan(p=>{
      const dm={...(p[key]||{})};const ex=dm[medId];
      const prev=ex?(Array.isArray(ex)?ex:[ex]):[];
      /* v9.64 : les activités exclusives ne cohabitent avec rien. En poser une
         remplace la case entière (mémoire des branches conservée) ; poser une
         activité normale sur une case qui en porte une est refusé. */
      if(entry&&!entry.cond){
        if(EXCL_IDS.includes(entry.acteId)){
          const drC=prev.filter(e=>e&&e.cond);
          dm[medId]=drC.length?{...entry,wasCond:drC.map(e=>e.acteId)}:entry;
          return{...p,[key]:dm};
        }
        const bl=prev.find(e=>e&&!e.cond&&EXCL_IDS.includes(e.acteId));
        if(bl){refusedBy=bl.acteId;return p;}
      }
      const dropped=(entry&&!entry.cond)?prev.filter(e=>e&&e.cond):[];
      let kept=dropped.length?prev.filter(e=>!(e&&e.cond)):prev;
      /* v9.63 : reposer une activité DÉJÀ ferme sur la case la remplace au lieu de la
         dupliquer — c'est ainsi qu'on lui attribue sa salle. La modale de case s'en
         gardait déjà, mais les modales de salles et le BIP automatique passent par ici
         sans ce contrôle, et pouvaient créer deux fois la même activité. */
      const dup=(entry&&!entry.cond)?kept.filter(e=>e&&e.acteId===entry.acteId&&!e.cond):[];
      if(dup.length)kept=kept.filter(e=>!(e&&e.acteId===entry.acteId&&!e.cond));
      let ent=entry;
      /* v9.61 : wasCond garde la liste COMPLÈTE des branches d'origine, sans en retirer
         celle qu'on garde. Rétablir devient « je remets exactement ce qu'il y avait »,
         règle valable que l'activité posée ait fait partie du choix ou non — l'ancienne
         version en rajoutait une quand elle venait d'ailleurs, et le compte était faux. */
      if(dropped.length)ent={...entry,wasCond:dropped.map(e=>e.acteId)};
      if(dup.length&&dup[0].wasCond&&!ent.wasCond)ent={...ent,wasCond:dup[0].wasCond};
      const nx=kept.concat([ent]);
      dm[medId]=nx.length===1?nx[0]:nx;
      return{...p,[key]:dm};
    });
    /* le refus se constate dans le réducteur ; le message part après son passage */
    setTimeout(()=>{
      if(refusedBy){toast("Ce créneau porte "+(EXCL_LABEL[refusedBy]||refusedBy)+" — retirez-la d'abord (×)","warn");return;}
      logCell("add",medId,y2,m2,d2,slot,entry.acteId);
      if(vAvertit(vRef,y2,m2,d2))vToast(true);
    },0);
  },[]);

  /* Trancher depuis la modale de case : la branche choisie devient ferme, les autres
     partent dans son wasCond. Indispensable pour la Scintigraphie, qui n'a pas de salle. */
  const settleCond=useCallback((medId,y2,m2,d2,slot,acteId)=>{
    const key=sk(y2,m2,d2,slot);
    setPlan(p=>{
      const dm={...(p[key]||{})};const ex=dm[medId];if(!ex)return p;
      const arr=Array.isArray(ex)?ex:[ex];
      const win=arr.find(e=>e&&e.cond&&e.acteId===acteId);if(!win)return p;
      const allBr=arr.filter(e=>e&&e.cond).map(e=>e.acteId);
      const ent={...win};delete ent.cond;if(allBr.length>1)ent.wasCond=allBr;
      const nx=arr.filter(e=>!(e&&e.cond)).concat([ent]);
      dm[medId]=nx.length===1?nx[0]:nx;
      return{...p,[key]:dm};
    });
    logCell("add",medId,y2,m2,d2,slot,acteId);
  },[]);

  /* v9.62 : retirer UNE branche (acteId fourni) ou TOUT le choix ouvert (acteId nul).
     Une branche unique reste volontairement conditionnelle : c'est la façon de dire
     « je prévois cette activité mais je n'ai pas encore de salle ». Elle n'occupe rien
     et reste dans la liste violette, là où une activité ferme sans salle irait, elle,
     dans la liste rouge des anomalies. Ce sont deux états différents. */
  const dropCond=useCallback((medId,y2,m2,d2,slot,acteId)=>{
    const key=sk(y2,m2,d2,slot);
    setPlan(p=>{
      const dm={...(p[key]||{})};const ex=dm[medId];if(!ex)return p;
      const arr=Array.isArray(ex)?ex:[ex];
      const nx=arr.filter(e=>!(e&&e.cond&&(!acteId||e.acteId===acteId)));
      if(nx.length===arr.length)return p;
      if(nx.length===0)delete dm[medId];else dm[medId]=nx.length===1?nx[0]:nx;
      return{...p,[key]:dm};
    });
    logCell("del",medId,y2,m2,d2,slot,acteId||null);
  },[]);

  /* Rétablir le choix ouvert à partir de la mémoire d'une entrée tranchée. */
  const restoreCond=useCallback((medId,y2,m2,d2,slot,acteId)=>{
    const key=sk(y2,m2,d2,slot);
    setPlan(p=>{
      const dm={...(p[key]||{})};const ex=dm[medId];if(!ex)return p;
      const arr=Array.isArray(ex)?ex:[ex];
      const src=arr.find(e=>e&&e.acteId===acteId&&e.wasCond&&e.wasCond.length);if(!src)return p;
      /* v9.63 : ne pas ressusciter une branche dont l'activité est déjà posée FERME sur
         la case — on recréerait le couple « branche + activité de même nom » qui était
         à l'origine du choix à 3 devenu 2. */
      const rest=arr.filter(e=>e!==src);
      const firmIds=rest.filter(e=>e&&!e.cond).map(e=>e.acteId);
      const brs=src.wasCond.filter(id=>firmIds.indexOf(id)<0).map(id=>({acteId:id,salle:null,cond:1}));
      const nx=rest.concat(brs);
      dm[medId]=nx.length===1?nx[0]:nx;
      return{...p,[key]:dm};
    });
    logCell("add",medId,y2,m2,d2,slot,acteId);
  },[]);

  const removeEntry=useCallback((medId,y2,m2,d2,slot,acteId)=>{
    if(vBloque(vRef,y2,m2,d2)){vToast(false);return;}   /* v10.106 */
    if(vAvertit(vRef,y2,m2,d2))vToast(true);
    const key=sk(y2,m2,d2,slot);
    setPlan(p=>{
      const dm={...(p[key]||{})};const ex=dm[medId];if(!ex)return p;
      const arr=Array.isArray(ex)?ex:[ex];
      /* v9.58 : si l'activité retirée était issue d'un choix ouvert, on ne vide pas la
         case — on remet les branches. Le choix redevient visible et à trancher. */
      const gone=arr.find(e=>e&&e.acteId===acteId&&!e.cond&&e.wasCond&&e.wasCond.length);
      /* v9.61 : ne retirer que l'entrée FERME. Filtrer sur le seul acteId emportait aussi
         la branche de même activité — c'est l'origine du « 3 choix devenus 2 » observé
         dès les premières versions, quand une activité posée coexistait avec sa branche. */
      const f=arr.filter(e=>!(e.acteId===acteId&&!e.cond));
      const firmIds=f.filter(e=>e&&!e.cond).map(e=>e.acteId);
      const back=gone?gone.wasCond.filter(id=>firmIds.indexOf(id)<0).map(id=>({acteId:id,salle:null,cond:1})):[];
      const nx=f.concat(back);
      if(nx.length===0)delete dm[medId];else dm[medId]=nx.length===1?nx[0]:nx;
      return{...p,[key]:dm};
    });
    logCell("del",medId,y2,m2,d2,slot,acteId);
  },[]);

  /* v9.37 : le départ différé appartient à l'ACTIVITÉ — on marque toutes ses entrées,
     quel que soit le nombre de médecins en salle (c'est l'effectif IDE qui conditionne le démarrage). */
  const patchActivity=useCallback((medId,y2,m2,d2,slot,acteId,salle,patch)=>{
    const key=sk(y2,m2,d2,slot);
    setPlan(p=>{
      const cell=p[key];if(!cell)return p;
      const dm={...cell};let done=false;
      Object.keys(dm).forEach(mid=>{
        const ex=dm[mid];if(!ex)return;
        const arr=Array.isArray(ex)?ex:[ex];let ch=false;
        const nx=arr.map(e=>{
          if(!e||e.acteId!==acteId)return e;
          if(salle!==undefined&&salle!==null&&(e.salle||null)!==salle)return e;
          ch=true;done=true;const q={...e,...patch};
          Object.keys(patch).forEach(k2=>{if(patch[k2]===null)delete q[k2];});
          return q;
        });
        if(ch)dm[mid]=nx.length===1?nx[0]:nx;
      });
      if(!done)return p;
      return{...p,[key]:dm};
    });
    logCell("add",medId,y2,m2,d2,slot,acteId);
  },[]);

  /* ── applyGarde (atomic) ── */
  /* ── v9.16 : répartition automatique du Bip (CHB) — dernière étape, après le planning type ── */
  const bipScan=()=>{
    const acteB=actes.find(a=>a.id==="BIP");
    const auth=(acteB&&acteB.medecinsAutorise)||[];
    const elig=medecins.filter(m=>m.role!=="ide"&&(auth.length===0||auth.indexOf(m.init)>=0));
    const chb={},bipN={},offN={},wkN={};
    elig.forEach(m=>{chb[m.id]=0;bipN[m.id]=0;offN[m.id]=0;});
    const jours=allDays4.filter(o=>{const dw=new Date(o.y,o.m,o.d).getDay();return dw>=1&&dw<=5&&!isFerie(o.y,o.m,o.d);});
    jours.forEach(o=>["M","AM"].forEach(sl=>{
      elig.forEach(m=>{
        /* v9.59 : une branche non tranchée ne compte ni comme demi-journée à Béthune
           (elle n'est pas décidée) ni comme bip posé — et laisse le créneau « libre ». */
        const es=(getEntries(m.id,o.y,o.m,o.d,sl)||[]).filter(e=>e&&!e.cond);
        if(es.length===0){offN[m.id]++;return;}
        let hasCHB=false;
        es.forEach(e=>{const a=acteById(e.acteId);if(a&&a.site==="CHB")hasCHB=true;if(e.acteId==="BIP"){bipN[m.id]++;const kw=m.id+"|"+wKey(o.y,o.m,o.d);wkN[kw]=(wkN[kw]||0)+1;}});
        if(hasCHB)chb[m.id]++;
      });
    }));
    return {acteB:acteB,elig:elig,chb:chb,bipN:bipN,offN:offN,wkN:wkN,jours:jours};
  };
  const bipStats=(S)=>S.elig.map(m=>({id:m.id,init:m.init,bip:S.bipN[m.id],chb:S.chb[m.id],off:S.offN[m.id]})).sort((a,b)=>b.chb-a.chb||b.bip-a.bip);
  const bipOpen=()=>{const S=bipScan();setBipModal({posed:null,fails:[],stats:bipStats(S)});};
  const bipRun=()=>{
    const S=bipScan();
    if(!S.acteB){toast("Activité BIP introuvable","warn");return;}
    const elig=S.elig,chb=S.chb,bipN=S.bipN,offN=S.offN,wkN=S.wkN,jours=S.jours,salles=S.acteB.salles||[];
    const BIP_MAX_SEM=2;
    const fails2=[];let posed=0,condN=0;
    jours.forEach(o=>{
      let deja=false;
      ["M","AM"].forEach(sl=>elig.forEach(m=>(getEntries(m.id,o.y,o.m,o.d,sl)||[]).forEach(e=>{if(e.acteId==="BIP"&&!e.cond)deja=true;})));
      if(deja)return;
      let done=false,capped=false;
      const wk=wKey(o.y,o.m,o.d);
      ["AM","M"].forEach(sl=>{
        if(done)return;
        /* v9.59 : est disponible celui qui n'a rien de ferme, ET dont l'éventuel choix
           ouvert contient BIP — l'algorithme ne décide donc jamais à la place de l'humain. */
        const dispo=elig.filter(m=>{
          if(offOn(m,o.y,o.m,o.d))return false;   /* v10.41 : désactivé ce jour-là */
          const es=getEntries(m.id,o.y,o.m,o.d,sl)||[];
          if(es.some(e=>e&&e.acteId&&!e.cond))return false;
          const cd=es.filter(e=>e&&e.cond);
          return cd.length===0||cd.some(e=>e.acteId==="BIP");
        });
        const libres=dispo.filter(m=>(wkN[m.id+"|"+wk]||0)<BIP_MAX_SEM);
        if(dispo.length>0&&libres.length===0)capped=true;
        if(libres.length===0)return;
        libres.sort((a,b)=>(chb[a.id]-chb[b.id])||(offN[b.id]-offN[a.id])||(bipN[a.id]-bipN[b.id])||String(a.init).localeCompare(String(b.init)));
        const m=libres[0];
        const occ={};elig.forEach(x=>(getEntries(x.id,o.y,o.m,o.d,sl)||[]).forEach(e=>{if(e.salle&&!e.cond)occ[e.salle]=true;}));
        const salle=salles.filter(s=>!occ[s])[0]||null;
        if((getEntries(m.id,o.y,o.m,o.d,sl)||[]).some(e=>e&&e.cond))condN++;
        addEntry(m.id,o.y,o.m,o.d,sl,{acteId:"BIP",salle:salle});
        chb[m.id]++;bipN[m.id]++;offN[m.id]--;wkN[m.id+"|"+wk]=(wkN[m.id+"|"+wk]||0)+1;posed++;done=true;
      });
      if(!done)fails2.push({y:o.y,m:o.m,d:o.d,cap:capped});
    });
    setBipModal({posed:posed,fails:fails2,stats:bipStats({elig:elig,chb:chb,bipN:bipN,offN:offN})});
    /* ⚑ dans la liste des jours non pourvus = plafond de 2 bips/semaine atteint par tous les disponibles */
    toast(posed+" bip"+(posed>1?"s":"")+" posé"+(posed>1?"s":"")+(condN?" · dont "+condN+" choix ouvert(s) tranché(s)":"")+(fails2.length?" · "+fails2.length+" jour(s) sans solution":""));
  };
  const bipClear=()=>{
    const S=bipScan();let n=0;
    S.jours.forEach(o=>["M","AM"].forEach(sl=>S.elig.forEach(m=>(getEntries(m.id,o.y,o.m,o.d,sl)||[]).forEach(e=>{if(e.acteId==="BIP"){removeEntry(m.id,o.y,o.m,o.d,sl,"BIP");n++;}}))));
    toast(n+" bip(s) retiré(s) sur la période");setBipModal(null);
  };
  const bipModalUI=()=>{
    const B=bipModal;const RE2=React.createElement;
    const th=(x,w)=>RE2("th",{key:x,style:{padding:"3px 6px",fontSize:9,color:"var(--txt3)",textAlign:w||"center",background:"var(--th)"}},x);
    return RE2("div",{onClick:()=>setBipModal(null),style:{position:"fixed",top:0,left:0,right:0,bottom:0,background:"rgba(0,0,0,.55)",zIndex:900,display:"flex",alignItems:"center",justifyContent:"center",padding:12}},
      RE2("div",{onClick:e=>e.stopPropagation(),style:{background:"var(--bg2)",border:"1px solid var(--border)",borderRadius:12,padding:14,width:"100%",maxWidth:480,maxHeight:"84vh",overflowY:"auto"}},
        RE2("div",{style:{display:"flex",alignItems:"center",gap:8,marginBottom:6}},
          RE2("div",{style:{fontWeight:800,fontSize:14,color:"var(--txt)"}},"📟 Répartition du Bip — CHB"),
          RE2("button",{onClick:()=>setBipModal(null),style:{marginLeft:"auto",background:"none",border:"none",color:"var(--txt2)",fontSize:20,cursor:"pointer",lineHeight:1}},"×")),
        RE2("div",{style:{fontSize:10,color:"var(--txt3)",marginBottom:9}},"Un bip par jour ouvré sur toute la période affichée, l'après-midi de préférence, avec un plafond de 2 bips par semaine et par médecin. Priorité au médecin qui a le moins de demi-journées à Béthune, puis à celui qui a le plus de demi-journées libres. Les bips déjà posés ne sont jamais déplacés."),
        B.posed!==null&&RE2("div",{style:{fontSize:12,fontWeight:800,color:B.fails.length?"#b45309":"#16a34a",marginBottom:6}},
          "✓ "+B.posed+" bip"+(B.posed>1?"s":"")+" posé"+(B.posed>1?"s":"")+(B.fails.length?" · "+B.fails.length+" jour(s) sans solution":" · aucun jour sans solution")),
        B.fails.length>0&&RE2("div",{style:{fontSize:10,color:"#ef4444",marginBottom:9,lineHeight:1.7}},
          RE2("b",null,"Jours non pourvus : "),
          B.fails.slice(0,40).map(o=>o.d+"/"+(o.m+1)+(o.cap?" ⚑":"")).join(" · ")+(B.fails.length>40?" …":""),
          RE2("div",{style:{color:"var(--txt3)",marginTop:2}},"⚑ = des médecins étaient libres mais avaient déjà 2 bips cette semaine-là")),
        RE2("div",{style:{fontSize:10,fontWeight:800,color:"var(--txt2)",textTransform:"uppercase",letterSpacing:.4,marginBottom:4}},"Équité sur la période"),
        RE2("div",{style:{overflowX:"auto",border:"1px solid var(--border)",borderRadius:8,marginBottom:10}},
          RE2("table",{style:{borderCollapse:"collapse",width:"100%"}},
            RE2("thead",null,RE2("tr",null,th("Médecin","left"),th("Bips"),th("½ j. CHB"),th("½ j. libres"))),
            RE2("tbody",null,B.stats.map(s=>RE2("tr",{key:s.id,style:{borderTop:"1px solid var(--border2)"}},
              RE2("td",{style:{padding:"3px 6px",fontSize:11,fontWeight:700,color:"var(--txt)"}},s.init),
              RE2("td",{style:{padding:"3px 6px",fontSize:11,textAlign:"center",color:"#46bdc6",fontWeight:800}},s.bip),
              RE2("td",{style:{padding:"3px 6px",fontSize:11,textAlign:"center",color:"var(--txt2)",fontWeight:700}},s.chb),
              RE2("td",{style:{padding:"3px 6px",fontSize:11,textAlign:"center",color:"var(--txt3)"}},s.off)))))),
        RE2("div",{style:{display:"flex",gap:6,flexWrap:"wrap"}},
          RE2("button",{onClick:bipRun,style:{fontSize:12,padding:"6px 13px",borderRadius:8,cursor:"pointer",fontWeight:800,border:"1.5px solid #46bdc6",background:"rgba(70,189,198,.12)",color:"#46bdc6"}},"▶ Répartir les bips manquants"),
          RE2("button",{onClick:bipClear,style:{fontSize:12,padding:"6px 13px",borderRadius:8,cursor:"pointer",fontWeight:800,border:"1.5px solid #dc2626",background:"rgba(220,38,38,.10)",color:"#dc2626"}},"🗑 Effacer les bips de la période"))));
  };
  const removeGardeDay=(y3,m3,d3)=>{
    setPlan(p=>{
      let next={...p};const gIds=[];
      ["N","JOUR"].forEach(sl=>{const k=sk(y3,m3,d3,sl);const dm={...(next[k]||{})};let ch=false;
        Object.keys(dm).forEach(mid=>{if(cellHasAny(dm[mid],["GARDE"])){gIds.push(mid);const r=cellDrop(dm[mid],["GARDE"]);if(r)dm[mid]=r;else delete dm[mid];ch=true;}});
        if(ch)next={...next,[k]:dm};});
      const dt=new Date(y3,m3,d3+1);const ny=dt.getFullYear(),nm=dt.getMonth(),nd=dt.getDate();
      ["JOUR","M","AM"].forEach(sl=>{const k=sk(ny,nm,nd,sl);const dm={...(next[k]||{})};let ch=false;
        /* v9.82 : le repos n'est retiré que s'il est présent, où qu'il soit dans la case,
           et sans emporter ce qui l'accompagnerait (même règle que v9.73). */
        gIds.forEach(mid=>{if(cellHasAny(dm[mid],["REPOS_GARDE"])){const r=cellDrop(dm[mid],["REPOS_GARDE"]);if(r)dm[mid]=r;else delete dm[mid];ch=true;}});
        if(ch)next={...next,[k]:dm};});
      return next;
    });
    toast("Garde et repos retir\u00e9s","info");
  };

  const applyGarde=useCallback((medId,y2,m2,d2)=>{
    if(accessMode==="adminEdit")return;
    logCell("add",medId,y2,m2,d2,"N","GARDE");
    /* v9.65 : la garde la veille d'une absence ou d'une FMC reste PERMISE (décision
       utilisateur), mais elle est signalée — le repos ne sera pas posé, la v9.64
       interdisant au repos d'écraser une exclusive. La répartition automatique, elle,
       ÉVITE ces gardes depuis toujours (canTake teste le lendemain). */
    let nxWarn=false;
    const dw=dow(y2,m2,d2);
    const gardeSlot=(dw===6||dw===0)?"JOUR":"N";
    const dt=new Date(y2,m2,d2+1);
    const ny=dt.getFullYear(),nm=dt.getMonth(),nd2=dt.getDate();
    setPlan(p=>{
      let next={...p};
      const gk=sk(y2,m2,d2,gardeSlot);
      const gdm={...(next[gk]||{})};
      Object.keys(gdm).forEach(mid=>{
        if(cellHasAny(gdm[mid],["GARDE"])){
          const prevId=parseInt(mid);
          const rSlots=isWE(ny,nm,nd2)?["JOUR"]:["M","AM"];
          rSlots.forEach(sl=>{const rk=sk(ny,nm,nd2,sl);const rdm={...(next[rk]||{})};if(cellHasAny(rdm[prevId],["REPOS_GARDE"])){const rr=cellDrop(rdm[prevId],["REPOS_GARDE"]);if(rr)rdm[prevId]=rr;else delete rdm[prevId];next={...next,[rk]:rdm};}});
          const rg=cellDrop(gdm[mid],["GARDE"]);if(rg)gdm[mid]=rg;else delete gdm[mid];
        }
      });
      next={...next,[gk]:gdm};
      next[gk]={...next[gk],[medId]:{acteId:"GARDE",salle:null}};
      if(isWE(ny,nm,nd2)){
        const k=sk(ny,nm,nd2,"JOUR"),dm={...(next[k]||{})};
        if(!cellHasAny(dm[medId],EXCL_IDS))dm[medId]={acteId:"REPOS_GARDE",salle:null};
        else if(cellHasAny(dm[medId],ABS_IDS))nxWarn=true;
        next={...next,[k]:dm};
      } else {
        /* v9.65.1 : une absence ou FMC « journée entière » vit dans la case JOUR du
           lendemain, pas dans M/AM — le contrôle ne la voyait pas : l'alerte ne partait
           jamais et deux repos fantômes se posaient dessous. On lit donc aussi JOUR,
           et si la journée est bloquée, aucun repos n'est posé. */
        const jC=(next[sk(ny,nm,nd2,"JOUR")]||{})[medId];
        const jBlk=cellHasAny(jC,EXCL_IDS);
        if(cellHasAny(jC,ABS_IDS))nxWarn=true;
        ["M","AM"].forEach(sl=>{const k=sk(ny,nm,nd2,sl),dm={...(next[k]||{})};if(!jBlk&&!cellHasAny(dm[medId],EXCL_IDS))dm[medId]={acteId:"REPOS_GARDE",salle:null};else if(cellHasAny(dm[medId],ABS_IDS))nxWarn=true;next={...next,[k]:dm};});
      }
      return next;
    });
    setTimeout(()=>{
      if(nxWarn)toast("⚠ Absence ou FMC le lendemain — garde posée SANS repos","warn");
      else toast("Garde + repos automatique","info");
    },0);
  },[]);

  /* ── applyAbsence ── */
  const applyAbsence=useCallback(({medId,dateFrom,dateTo,slots,absType="ABSENCE",slotsParJour=null})=>{
    const [fy,fm,fd]=parseDate(dateFrom);
    const fromT=new Date(fy,fm,fd).getTime(),toT=new Date(...parseDate(dateTo)).getTime();
    let vSkip=false,vWarn=false;
    setPlan(p=>{
      let next={...p};
      let cy=fy,cm=fm;
      while(new Date(cy,cm,1).getTime()<=new Date(...parseDate(dateTo)).getTime()){
        for(let d=1;d<=dIM(cy,cm);d++){
          const t=new Date(cy,cm,d).getTime();
          if(t<fromT||t>toT)continue;
          /* v10.106 : jour clos — saute pour tout le monde sauf l'editeur, averti */
          if(vBloque(vRef,cy,cm,d)){vSkip=true;continue;}
          if(vAvertit(vRef,cy,cm,d))vWarn=true;
          (isWE(cy,cm,d)?["JOUR"]:(slotsParJour?slotsParJour(cy,cm,d):slots)).forEach(sl=>{const k=sk(cy,cm,d,sl);const dm={...(next[k]||{})};dm[medId]={acteId:absType||"ABSENCE",salle:null};next={...next,[k]:dm};});
        }
        if(cm===11){cy++;cm=0;}else cm++;
      }
      return next;
    });
    if(vSkip||vWarn)vToast(!vSkip);else toast(absType==="FORMATION"?"Formation appliquée":"Absence appliquée");
  },[]);

  const removeAbsence=useCallback(({medId,dateFrom,dateTo,slotsParJour=null})=>{
    const [fy,fm,fd]=parseDate(dateFrom);
    const fromT=new Date(fy,fm,fd).getTime(),toT=new Date(...parseDate(dateTo)).getTime();
    let vSkip=false,vWarn=false;
    setPlan(p=>{
      let next={...p};
      let cy=fy,cm=fm;
      while(new Date(cy,cm,1).getTime()<=new Date(...parseDate(dateTo)).getTime()){
        for(let d=1;d<=dIM(cy,cm);d++){
          const t=new Date(cy,cm,d).getTime();
          if(t<fromT||t>toT)continue;
          /* v10.106 : jour clos — saute pour tout le monde sauf l'editeur, averti */
          if(vBloque(vRef,cy,cm,d)){vSkip=true;continue;}
          if(vAvertit(vRef,cy,cm,d))vWarn=true;
          (isWE(cy,cm,d)?["JOUR"]:(slotsParJour?slotsParJour(cy,cm,d):["M","AM"]).concat(["JOUR"])).forEach(sl=>{
            const k=sk(cy,cm,d,sl);
            if(!next[k]||!next[k][medId])return;
            if(cellHasAny(next[k][medId],["ABSENCE","FORMATION"])){
              const r=cellDrop(next[k][medId],["ABSENCE","FORMATION"]);
              const dm={...next[k]};if(r)dm[medId]=r;else delete dm[medId];next={...next,[k]:dm};
            }
          });
        }
        if(cm===11){cy++;cm=0;}else cm++;
      }
      return next;
    });
    if(vSkip||vWarn)vToast(!vSkip);else toast("Absence retirée");
  },[]);

  /* ── applyPlanningType ── */
  const [plIssOpen,setPlIssOpen]=useState(false);
  /* v9.50 : le relevé porte désormais sur la liste de médecins qu'on lui donne,
     pour que chaque onglet compte les siens. */
  const issuesFor=useCallback((medList)=>{
    const IGN=["GARDE","REPOS_GARDE","TOUR_HC","TOUR_USIC","ABSENCE","FORMATION","TP"];
    const ABSL=["ABSENCE","FORMATION","REPOS_GARDE"];
    const JRS=["Dim","Lun","Mar","Mer","Jeu","Ven","Sam"];
    const map={},list=[],condList=[],counts={salle:0,double:0,abs:0,hop:0,cond:0};
    const sh=e=>{const a=acteById(e.acteId);return a?a.short:e.acteId;};
    (allDays4||[]).forEach(dd=>{(medList||[]).forEach(med=>{["M","AM"].forEach(sl=>{
      const all=[];[sl,"JOUR"].forEach(s2=>getEntries(med.id,dd.y,dd.m,dd.d,s2).forEach(e=>{if(e&&e.acteId&&!e._blocked)all.push(e);}));
      if(!all.length)return;
      /* v9.59 : un choix ouvert n'est pas une anomalie mais une décision en attente —
         il a son propre décompte et ne gonfle plus « sans salle » ni « double activité ». */
      const allC=all.filter(e=>e&&e.cond),allF=all.filter(e=>!(e&&e.cond));
      if(allC.length){
        counts.cond++;
        condList.push({y:dd.y,m:dd.m,d:dd.d,sl,med,cond:true,label:"choix ouvert : "+allC.map(sh).join(" ou "),dw:JRS[new Date(dd.y,dd.m,dd.d).getDay()]});
      }
      if(!allF.length)return;
      const msgs=[];
      allF.forEach(e=>{const a=acteById(e.acteId);if(a&&a.hasSalle&&!e.salle){msgs.push((a.short||e.acteId)+" sans salle");counts.salle++;}});
      const met=allF.filter(e=>IGN.indexOf(e.acteId)<0);
      if(met.length>=2){msgs.push("double activité : "+met.map(sh).join(" + "));counts.double++;}
      const ab=allF.filter(e=>ABSL.indexOf(e.acteId)>=0);
      if(met.length>=1&&ab.length>=1){const a0=acteById(ab[0].acteId);msgs.push("activité sur "+(a0?a0.label:ab[0].acteId));counts.abs++;}
      /* deux salles DÉDIÉES dans deux hôpitaux sur la même demi-journée : les sites sont
         proches et on passe de l'un à l'autre, mais pas quand les deux lieux sont fixés. */
      /* v9.80 : le lieu vient désormais de la SALLE POSÉE, plus du site de l'activité.
         Une Coro en Angio-2 est à Lens même si l'activité est cochée « tous », et une
         salle déplacée d'un hôpital à l'autre est suivie sans rien changer ici. */
      const sts=uniqArr(allF.filter(e=>e.salle).map(e=>{
        const rg=(salleReg||[]).find(x=>x&&x.n===e.salle);
        if(rg)return salleSite(rg);
        const a=acteById(e.acteId);return a&&a.site;
      }).filter(x=>x==="CHL"||x==="CHB"));
      if(sts.length>=2){msgs.push("deux hôpitaux : "+sts.map(x=>x==="CHL"?"Lens":"Béthune").join(" + "));counts.hop++;}
      if(msgs.length){map[med.id+"|"+dd.y+"|"+dd.m+"|"+dd.d+"|"+sl]="⚠ "+msgs.join(" · ");list.push({y:dd.y,m:dd.m,d:dd.d,sl,med,label:msgs.join(" · "),dw:JRS[new Date(dd.y,dd.m,dd.d).getDay()]});}
    });});});
    return {map,list,condList,counts};
  },[getEntries,acteById,allDays4,actes,salleReg]);
  /* ── Application flexible du planning type (multi-mois, départ configurable) ── */
  const applyPTFlex=useCallback((medId,monthsList,fromToday,bornes)=>{
    const tod=new Date();tod.setHours(0,0,0,0);
    const targets=medId?medecins.filter(m=>m.id===medId):medecins;
    let nApplied=0;
    setPlan(p=>{
      let next={...p};
      monthsList.forEach(({y:ay,m:am})=>{
        const dim=new Date(ay,am+1,0).getDate();
        for(let d=1;d<=dim;d++){
          /* v10.109 : hors des bornes reelles de la periode — les premiers jours du
             1er mois appartiennent a la periode PRECEDENTE, souvent close. */
          const _dk=dKey(ay,am,d);
          if(bornes&&(_dk<bornes.deb||_dk>bornes.fin))continue;
          if(isWE(ay,am,d))continue;
          if(fromToday&&new Date(ay,am,d)<tod)continue;
          const dw=dow(ay,am,d);
          const wk=wKey(ay,am,d),wm=tourMed[wk]||{HC:[],USIC:[]};
          const allTm=[...(wm.HC||[]),...(wm.USIC||[])];
          targets.forEach(med=>{
            if(allTm.includes(med.id))return;
            if(offOn(med,ay,am,d))return;   /* v10.40 : désactivé ce jour-là — sauté */
            if(med.partTime&&(med.workDays||{})[String(dw)]===false){
              ["M","AM"].forEach(sl=>{
                const k=sk(ay,am,d,sl),ex=(next[k]||{})[med.id];
                if(cellHasAny(ex,PROT_TOUR))return;
                if(!next[k])next[k]={};
                next[k]={...next[k],[med.id]:{acteId:"TP",salle:null}};
                nApplied++;
              });
              return;
            }
            const pt=planningType[med.id];if(!pt||!pt[dw])return;
            ["M","AM"].forEach(sl=>{
              const k=sk(ay,am,d,sl),ex=(next[k]||{})[med.id];
              if(cellHasAny(ex,PROT_TOUR))return;
              const [acteId,salle,a2x=null,s2x=null,a3x=null,s3x=null,c1x=null]=(pt[dw][sl])||[null,null];if(!acteId)return;
              if(!next[k])next[k]={};
              next[k]={...next[k],[med.id]:ptCell(acteId,salle,a2x,s2x,a3x,s3x,c1x)};
              nApplied++;
            });
          });
        }
      });
      return next;
    });
    const medLbl=medId?(medecins.find(m=>m.id===medId)||{}).init||"":"tous";
    toast("Planning type appliqué ("+medLbl+", "+(bornes?bornes.n:monthsList.length)+" mois"+(fromToday?", à partir d'aujourd'hui":"")+")","info");
  },[medecins,planningType,tourMed]);

  /* v10.40 : désactivation — état et écriture. Le champ `off` voyage avec la
     fiche : la synchro de l'équipe l'emporte, aucun document nouveau. */
  const [deactMed,setDeactMed]=React.useState(null);
  const saveOff=useCallback((medId,ranges)=>{
    setMedecins(list=>list.map(m=>m.id===medId?{...m,off:ranges}:m));
  },[]);

  /* ── Modale d'application du PT ── */
  const [ptModal,setPtModal]=React.useState(null); // null | {medId:null|number}
  const [ptMonths,setPtMonths]=React.useState([]); // indices cochés
  const [ptFromToday,setPtFromToday]=React.useState(false);
  const ptPeriodMonths=React.useMemo(()=>{
    /* v10.30 : depuis Construire, la fenetre porte sur la periode de CET onglet,
       pas sur le mois global — sinon on appliquerait le planning type a cote. */
    const p=(ptModal&&ptModal.per)?ptModal.per:perStart(year,month);const arr=[];
    for(let i=0;i<PCFG.len;i++){const mm=(p.sm+i)%12,yy=p.sm+i>11?p.sy+1:p.sy;arr.push({y:yy,m:mm});}
    return arr;
  },[ptModal,year,month,PCFG.len,PCFG.startM]);
  const removePTFlex=useCallback((medId,monthsList,fromToday,bornes)=>{
    const tod=new Date();tod.setHours(0,0,0,0);
    const KEEP=["GARDE","REPOS_GARDE","TOUR_HC","TOUR_USIC","ABSENCE","FORM","FORMATION"];
    const targetIds=medId?[medId]:medecins.map(m=>m.id);
    setPlan(p=>{
      let next={...p};
      monthsList.forEach(({y:ay,m:am})=>{
        const dim=new Date(ay,am+1,0).getDate();
        for(let d=1;d<=dim;d++){
          /* v10.109 : hors des bornes reelles de la periode — les premiers jours du
             1er mois appartiennent a la periode PRECEDENTE, souvent close. */
          const _dk=dKey(ay,am,d);
          if(bornes&&(_dk<bornes.deb||_dk>bornes.fin))continue;
          if(fromToday&&new Date(ay,am,d)<tod)continue;
          ["M","AM","JOUR","N"].forEach(sl=>{
            const k=sk(ay,am,d,sl);
            if(!next[k])return;
            const dm={...next[k]};let changed=false;
            targetIds.forEach(mid=>{
              const e=dm[mid];if(!e)return;
              if(!cellHasAny(e,KEEP)){delete dm[mid];changed=true;}
            });
            if(changed)next[k]=dm;
          });
        }
      });
      return next;
    });
    toast("Affectations retirées ("+(bornes?bornes.n:monthsList.length)+" mois"+(fromToday?", à partir d'aujourd'hui":"")+"). Gardes, absences, formations et tour conservés.","info");
  },[medecins]);
  const openPtModal=(medId,mode,per)=>{
    setPtMonths(ptPeriodMonths.map((_,i)=>i)); // tous cochés par défaut
    setPtFromToday(false); // nominal : depuis le début de la période
    setPtModal({medId:medId||null,mode:mode||"apply",per:per||null});
  };
  const runPtModal=()=>{
    const list=ptPeriodMonths.filter((_,i)=>ptMonths.includes(i));
    if(list.length===0){toast("Sélectionnez au moins un mois","warn");return;}
    /* v10.109 : les mois coches deviennent des SEGMENTS DE PERIODE. Cocher le PREMIER
       mois demarre a la vraie borne de debut (le 6 juillet 2026, pas le 1er : les cinq
       premiers jours appartiennent a la periode precedente, close). Cocher le DERNIER
       va jusqu'a la fin reelle, debordement compris — le 1er novembre 2026 appartient
       a la periode juillet-octobre, il suit donc le dernier mois et non le suivant. */
    const _per=(ptModal&&ptModal.per)?ptModal.per:perStart(year,month);
    const _jrs=perDaysList(_per.sy,_per.sm);
    const _j1=_jrs[0],_j2=_jrs[_jrs.length-1];
    const _prem=ptMonths.includes(0),_dern=ptMonths.includes(PCFG.len-1);
    const bornes={deb:_prem?dKey(_j1.y,_j1.m,_j1.d):"0000-00-00",
                  fin:_dern?dKey(_j2.y,_j2.m,_j2.d):"9999-99-99",n:list.length};
    /* les jours de debordement vivent dans le mois SUIVANT : il faut le parcourir,
       le filtre des bornes se chargeant de n'en garder que ces jours-la. */
    const _liste=list.slice();
    if(_dern){
      const _last=ptPeriodMonths[PCFG.len-1];
      for(let _r=_last.y*12+_last.m+1;_r<=_j2.y*12+_j2.m;_r++)_liste.push({y:Math.floor(_r/12),m:_r%12});
    }
    if(ptModal.mode==="remove"){
      if(!window.confirm("Retirer toutes les affectations d'activités sur les mois sélectionnés ?"))return;
      removePTFlex(ptModal.medId,_liste,ptFromToday,bornes);
    }else{
      applyPTFlex(ptModal.medId,_liste,ptFromToday,bornes);
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
            if(cellHasAny(ex,PROT_TOUR))return;
            const [acteId,salle,a2x=null,s2x=null,a3x=null,s3x=null,c1x=null]=(pt[dw][sl])||[null,null];if(!acteId)return;
            if(!next[k])next[k]={};
            next[k]={...next[k],[med.id]:ptCell(acteId,salle,a2x,s2x,a3x,s3x,c1x)};
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
          if(cellHasAny(ex,PROT_TOUR))return;
          const [acteId,salle,a2x=null,s2x=null,a3x=null,s3x=null,c1x=null]=(pt[dw][sl])||[null,null];if(!acteId)return;
          if(!next[k])next[k]={};
          next[k]={...next[k],[medId]:ptCell(acteId,salle,a2x,s2x,a3x,s3x,c1x)};
        });
      });
      return next;
    });
    toast(`PT appliqué pour ${med.nom}`,"info");
  },[allDays,year,month,medecins,planningType,tourMed]);

  /* ── clearPlanningType (global or individual) ── */
  /* v9.92 : traduit « du 10 matin au 14 après-midi » en la liste des demi-journées à
     traiter jour par jour. Les jours du milieu sont toujours entiers ; seules les deux
     extrémités peuvent être partielles. Les week-ends n'ont qu'une case JOUR : les
     fonctions appelées s'en chargent déjà, on leur passe les deux demi-journées. */
  const perSlots=(p)=>{
    const out={...p};
    out.slotsParJour=(y3,m3,d3)=>{
      const j=`${y3}-${m3}-${d3}`;
      const a=p.dateFrom.split("-").map(Number), b=p.dateTo.split("-").map(Number);
      const estDeb=(y3===a[0]&&m3===a[1]-1&&d3===a[2]);
      const estFin=(y3===b[0]&&m3===b[1]-1&&d3===b[2]);
      if(estDeb&&estFin)return p.slotDebut===p.slotFin?[p.slotDebut]:["M","AM"];
      if(estDeb)return p.slotDebut==="AM"?["AM"]:["M","AM"];
      if(estFin)return p.slotFin==="M"?["M"]:["M","AM"];
      return ["M","AM"];
    };
    return out;
  };

  /* v9.92 : l'effacement d'activités sur une période, extrait de l'ancien écran pour être
     partagé. Conserve la même liste qu'avant, et remplace aussi « Effacer mois » : le mois
     entier n'est qu'une période comme une autre. */
  /* v9.94 : compte, sans rien modifier, ce que l'effacement retirerait. Même parcours et
     mêmes règles que clearPeriodActs — une seule logique, deux usages. */
  const countPeriodActs=useCallback(({medId,dateFrom,dateTo,keepAbs=true,keepGardes=true,slotDebut="M",slotFin="AM"})=>{
    /* v10.10 : `keepGardes` à false retire aussi gardes, repos et tour. Une garde et son
       repos partent TOUJOURS ensemble — jamais l'un sans l'autre, sinon on laisserait
       quelqu'un de garde sans repos le lendemain, incohérence que l'application signale. */
    const KEEP=(keepGardes?["GARDE","REPOS_GARDE","TOUR_HC","TOUR_USIC"]:[]).concat(keepAbs?["ABSENCE","FORM","FORMATION"]:[]);
    const sp=perSlots({medId,dateFrom,dateTo,slotDebut,slotFin}).slotsParJour;
    const [fy,fm,fd]=parseDate(dateFrom);
    const fromT=new Date(fy,fm,fd).getTime(),toT=new Date(...parseDate(dateTo)).getTime();
    let n=0,cy=fy,cm=fm;const par={};
    while(new Date(cy,cm,1).getTime()<=toT){
      for(let d=1;d<=dIM(cy,cm);d++){
        const t=new Date(cy,cm,d).getTime();
        if(t<fromT||t>toT)continue;
        (isWE(cy,cm,d)?["JOUR"]:sp(cy,cm,d).concat(["JOUR"])).concat(keepGardes?[]:["N"]).forEach(sl=>{
          const c=(plan[sk(cy,cm,d,sl)]||{})[medId];
          cellEs(c).forEach(e=>{if(e&&e.acteId&&KEEP.indexOf(e.acteId)<0){n++;par[e.acteId]=(par[e.acteId]||0)+1;}});
        });
      }
      if(cm===11){cy++;cm=0;}else cm++;
    }
    /* v9.95 : le détail par activité, du plus fréquent au plus rare — « 12 CS-L, 4 Coro »
       est plus parlant qu'un total, et permet de repérer une erreur de période. */
    const det=Object.keys(par).map(id=>{const a=acteById(id);return {lab:(a&&(a.short||a.label))||id,n:par[id]};})
      .sort((x,y)=>y.n-x.n||String(x.lab).localeCompare(String(y.lab)));
    return {n,det};
  },[plan,acteById]);

  /* v10.2 : le BILAN avant restauration. Restaurer n'est pas qu'ajouter — cela supprime
     aussi ce qui a été posé depuis la sauvegarde. On compte donc trois choses : ce qui
     sera remis, ce qui sera supprimé, ce qui ne bouge pas. Trois zéros = mauvaise
     sauvegarde, autant le savoir avant de cliquer. */
  /* v10.3 : deux bugs corrigés d'un coup, révélés par ses tests.
     (a) COMPARAISON. Une case vaut soit un objet, soit un tableau — `{acteId:"ABSENCE"}`
         et `[{acteId:"ABSENCE"}]` décrivent la même chose mais ne se sérialisent pas
         pareil. Le bilan comptait donc « 7 remises ET 7 supprimées » sur des cases
         pourtant identiques. On compare désormais la forme normalisée.
     (b) ÉCRITURE. `setPlan(p=>{…})` n'exécute PAS sa fonction tout de suite : le tableau
         des modifications était encore vide quand on l'envoyait à Firestore, donc rien
         n'était enregistré et l'écran revenait à l'état précédent. Les changements sont
         maintenant calculés AVANT, sur l'état courant. */
  const cellKey=(c)=>JSON.stringify(cellEs(c)
    .filter(e=>e&&e.acteId)
    .map(e=>({a:e.acteId,s:e.salle||null,c:e.cond?1:0}))
    .sort((x,y)=>String(x.a+x.s).localeCompare(String(y.a+y.s))));

  const diffMedPeriod=useCallback(async(id,medId,dateFrom,dateTo)=>{
    try{
      const d=await window.firebaseDB.collection("backups").doc(id).get();
      const data=d.data();
      if(!data)return null;
      const old=data.planV2?data.planV2:(data.plan?JSON.parse(data.plan):null);
      if(!old)return null;
      const [fy,fm,fd]=parseDate(dateFrom);
      const fromT=new Date(fy,fm,fd).getTime(),toT=new Date(...parseDate(dateTo)).getTime();
      const cles={};
      Object.keys(old).forEach(k=>cles[k]=1);
      Object.keys(plan).forEach(k=>cles[k]=1);
      let nAdd=0,nDel=0,nSame=0;const parA={},parD={};
      Object.keys(cles).forEach(k=>{
        const parts=k.split("|");if(parts.length<2)return;
        /* v10.4 : la clé s'écrit « 2026-08-10 » — mois EN CLAIR, donc 1-based. Je le
           relisais comme un mois technique (0-based), ce qui décalait tout d'un mois :
           aucune clé ne tombait dans la fenêtre demandée, d'où « rien à restaurer ». */
        const [yy,mm,dd]=parts[0].split("-").map(Number);
        const t=new Date(yy,mm-1,dd).getTime();
        if(t<fromT||t>toT)return;
        const av=(old[k]||{})[medId], mt=(plan[k]||{})[medId];
        if(cellKey(av)===cellKey(mt)){if(mt!==undefined)nSame++;return;}
        cellEs(av).forEach(e=>{if(e&&e.acteId){nAdd++;parA[e.acteId]=(parA[e.acteId]||0)+1;}});
        cellEs(mt).forEach(e=>{if(e&&e.acteId){nDel++;parD[e.acteId]=(parD[e.acteId]||0)+1;}});
      });
      const det=o=>Object.keys(o).map(x=>{const a=acteById(x);return{lab:(a&&(a.short||a.label))||x,n:o[x]};})
        .sort((x,y)=>y.n-x.n||String(x.lab).localeCompare(String(y.lab)));
      return {nAdd,nDel,nSame,detA:det(parA),detD:det(parD)};
    }catch(e){console.log("diff:",e);return null;}
  },[plan,acteById]);

  /* v10.13 : retire les semaines de tour d'un médecin sur une période. */
  const removeTourPeriod=useCallback((medId,dateFrom,dateTo)=>{
    const [fy,fm,fd]=parseDate(dateFrom);
    const fromT=new Date(fy,fm,fd).getTime(),toT=new Date(...parseDate(dateTo)).getTime();
    setTourMed(tm=>{
      const next={...tm};let n=0;
      Object.keys(next).forEach(wk=>{
        const p=wk.split("-").map(Number);
        const t=new Date(p[0],p[1],p[2]).getTime();
        if(isNaN(t))return;
        const fin=t+6*86400000;
        if(fin<fromT||t>toT)return;
        const w={...(next[wk]||{})};
        ["HC","USIC"].forEach(r=>{
          if((w[r]||[]).includes(medId)){w[r]=(w[r]||[]).filter(x=>x!==medId);n++;}
        });
        next[wk]=w;
      });
      return n?next:tm;
    });
  },[]);

  const clearPeriodActs=useCallback(({medId,dateFrom,dateTo,keepAbs=true,keepGardes=true,slotsParJour=null})=>{
    /* v10.10 : `keepGardes` à false retire aussi gardes, repos et tour. Une garde et son
       repos partent TOUJOURS ensemble — jamais l'un sans l'autre, sinon on laisserait
       quelqu'un de garde sans repos le lendemain, incohérence que l'application signale. */
    const KEEP=(keepGardes?["GARDE","REPOS_GARDE","TOUR_HC","TOUR_USIC"]:[]).concat(keepAbs?["ABSENCE","FORM","FORMATION"]:[]);
    const [fy,fm,fd]=parseDate(dateFrom);
    const fromT=new Date(fy,fm,fd).getTime(),toT=new Date(...parseDate(dateTo)).getTime();
    setPlan(p=>{
      let next={...p};
      let cy=fy,cm=fm;
      while(new Date(cy,cm,1).getTime()<=toT){
        for(let d=1;d<=dIM(cy,cm);d++){
          const t=new Date(cy,cm,d).getTime();
          if(t<fromT||t>toT)continue;
          /* v10.13 : la GARDE est enregistrée dans le créneau « N », qui n'était jamais
             parcouru — d'où le repos retiré mais la garde conservée. On l'ajoute quand on
             ne conserve pas les gardes. Le TOUR, lui, ne vit pas dans le planning mais
             dans une liste de semaines ; il est traité séparément par l'appelant. */
          const sls=(isWE(cy,cm,d)?["JOUR"]:(slotsParJour?slotsParJour(cy,cm,d):["M","AM"]).concat(["JOUR"])).concat(keepGardes?[]:["N"]);
          sls.forEach(sl=>{
            const k=sk(cy,cm,d,sl);
            if(!next[k]||!next[k][medId])return;
            const dm={...next[k]};
            const gardes=cellEs(dm[medId]).filter(e=>e&&KEEP.includes(e.acteId));
            if(gardes.length===0)delete dm[medId];
            else dm[medId]=gardes.length===1?gardes[0]:gardes;
            next={...next,[k]:dm};
          });
        }
        if(cm===11){cy++;cm=0;}else cm++;
      }
      return next;
    });
    toast("Activités effacées sur la période","info");
  },[]);

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
            if(!cellHasAny(ex,["ABSENCE","FORM","FORMATION","GARDE","REPOS_GARDE","TOUR_HC","TOUR_USIC"])) delete newSlot[medId];
          } else {
            // Clear all meds (except ABSENCE/GARDE/REPOS)
            Object.keys(newSlot).forEach(mid=>{
              const ex=newSlot[mid];
              if(!cellHasAny(ex,["ABSENCE","FORM","FORMATION","GARDE","REPOS_GARDE","TOUR_HC","TOUR_USIC"])) delete newSlot[mid];
            });
          }
          next={...next,[k]:newSlot};
        });
      });
      return next;
    });
    toast(medId?`Planning effacé pour ${(medecins.find(m=>m.id===medId)||{nom:"?"}).nom}`:`Planning effacé pour ${MOIS[month]}`,"info");
  },[allDays,year,month,medecins]);

  /* v10.42 : garde-fou de la désactivation. Le compte lit par getEntries — il
     voit donc AUSSI le tour synthétisé et les gardes ; le nettoyage appelle
     clearPeriodActs ET removeTourPeriod, car le tour ne vit pas dans le planning. */
  const offCount=useCallback((medId,du,au)=>{
    const a=String(du).split("-").map(Number),b=String(au).split("-").map(Number);
    const fin=new Date(b[0],b[1]-1,b[2]);
    let n=0;
    for(const c=new Date(a[0],a[1]-1,a[2]);c<=fin;c.setDate(c.getDate()+1)){
      const y2=c.getFullYear(),m2=c.getMonth(),d2=c.getDate();
      ["M","AM","JOUR","N"].forEach(sl=>{n+=getEntries(medId,y2,m2,d2,sl).filter(e=>e&&e.acteId&&!e._blocked).length;});
    }
    return n;
  },[getEntries]);
  const offClear=useCallback((medId,du,au)=>{
    clearPeriodActs({medId:medId,dateFrom:du,dateTo:au,keepAbs:false,keepGardes:false});
    removeTourPeriod(medId,du,au);
  },[clearPeriodActs,removeTourPeriod]);

  /* ── salleOcc ── */
  const salleOcc=useCallback((acteId,y2,m2,d2,slot)=>{
    const res={};
    medecins.forEach(med=>{
      getEntries(med.id,y2,m2,d2,slot).forEach(e=>{
        if((e&&e.acteId)===acteId&&e.salle&&!e.cond){if(!res[e.salle])res[e.salle]=[];if(!res[e.salle].find(x=>x.id===med.id))res[e.salle].push(djAff(med,dKey(y2,m2,d2)));}
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
    return[0,1,2,3,4].some(i=>{const dt=new Date(wy,wm2,wd+i);return["M","AM","JOUR"].some(sl=>cellHasAny((plan[sk(dt.getFullYear(),dt.getMonth(),dt.getDate(),sl)]||{})[medId],ABS_IDS));});
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
  /* v10.108 : plus personne n'ouvre une case close, editeur compris — sauf si
     l'interrupteur de Parametres est leve, et alors la confirmation reste. */
  const vOuvre=(y2,m2,d2)=>{
    if(!estClos(y2,m2,d2))return true;
    if(!(isEdit&&vUnlock)){vToast(false);return false;}
    return window.confirm("🔒 Période close — elle précède la période en cours.\n\nLe verrou est levé pour cette session : vous pouvez modifier, et chaque modification vous sera signalée.\n\nOuvrir cette case ?");
  };
  const openCell=(medId,y2,m2,d2,slot)=>{
    if(!canEdit(medId))return;
    if(!vOuvre(y2,m2,d2))return;
    setMData({medId,y:y2,m:m2,d:d2,slot});setModal("cell");
  };

  /* ═══ v10.90 — LOT 2 des juniors ═══
     Date de référence de l'identité affichée : AUJOURD'HUI s'il tombe dans la
     période affichée, sinon le premier jour de cette période (sa règle du 19/08).
     `medsAff` sert à TOUT l'affichage ; `medecins` (brut) reste la liste de
     l'onglet Équipe, de la fiche, de l'export et de la sauvegarde Firestore. */
  const djTodayIso=intISO(new Date());
  const djA0=(allDays4&&allDays4.length)?dKey(allDays4[0].y,allDays4[0].m,allDays4[0].d):djTodayIso;
  const djZ=(allDays4&&allDays4.length)?allDays4[allDays4.length-1]:null;
  const djA1=djZ?dKey(djZ.y,djZ.m,djZ.d):djTodayIso;
  const djRefIso=(djTodayIso>=djA0&&djTodayIso<=djA1)?djTodayIso:djA0;
  djSetSems(intCfg,djA1);
  const medsAff=djSubst(medecins,intCfg,djRefIso);
  const medPlan=medsAff.filter(m=>m.role==="medecin");
  const medAttache=medsAff.filter(m=>m.role==="attache");
  // ── Ordre d'affichage : déplace un médecin dans son groupe de rôle (ordre du tableau = ordre partout) ──
  const moveMed=(id,dir)=>{
    setMedecins(prev=>{
      const idx=prev.findIndex(m=>String(m.id)===String(id));
      if(idx<0)return prev;
      const role=prev[idx].role||"medecin";
      let j=idx+dir;
      while(j>=0&&j<prev.length&&(prev[j].role||"medecin")!==role)j+=dir;
      if(j<0||j>=prev.length)return prev;
      const next=[...prev];const t=next[idx];next[idx]=next[j];next[j]=t;
      return next;
    });
  };
  const filteredMeds=medPlan.filter(m=>planFilter.length===0||planFilter.includes(m.id));
  /* v9.50 : un relevé par onglet, et le clic mène à la case */
  const medAttacheAll=useMemo(()=>[...medAttache,...medsAff.filter(m=>m.role==="ide")],[medsAff]);
  const planIssues=useMemo(()=>issuesFor(medPlan),[issuesFor,medecins]);
  const attIssues=useMemo(()=>issuesFor(medAttacheAll),[issuesFor,medAttacheAll]);
  /* v10.74 : une seule carte pour les 4 onglets salles — un attache en consultation
     doit etre signale la aussi, et les deux calculs existent deja. */
  const issAllMap=useMemo(()=>({...planIssues.map,...attIssues.map}),[planIssues,attIssues]);
  const goIssue=(it)=>{setMData({medId:it.med.id,y:it.y,m:it.m,d:it.d,slot:it.sl});setModal("cell");};

  /* v10.37 : repli des encarts de Paramètres. `psetItems` est LU dans la page
     après chaque affichage — c'est ce qui rend le mécanisme insensible à l'ajout
     d'un encart, et au fait que les deux fichiers ne les rangent pas pareil. */
  const psetRef=useRef(null);
  const [psetItems,setPsetItems]=useState([]);
  const [psetFold,setPsetFold]=useState([]);
  const psetInit=useRef(false);
  useEffect(()=>{
    if(tab!=="partage"){psetInit.current=false;if(psetItems.length)setPsetItems([]);return;}
    const l=setScan(psetRef.current);
    const a=l.map(x=>x.i+x.titre).join("|"),b=psetItems.map(x=>x.i+x.titre).join("|");
    if(a!==b)setPsetItems(l);
    /* v10.39 : à l'arrivée dans l'onglet, TOUT est replié — sa demande. Une seule
       fois par visite : sinon un encart qui apparaît replierait ce qu'il vient d'ouvrir. */
    if(!psetInit.current&&l.length){psetInit.current=true;setPsetFold(l.map(x=>x.i));}
  });
  const psetClick=useCallback((e)=>{
    let n=e.target,box=null;
    const root=psetRef.current;if(!root)return;
    while(n&&n!==root){if(n.parentNode===root){box=n;break;}n=n.parentNode;}
    if(!box||box.getAttribute("data-fold")!=="1")return;
    /* on ne replie qu'au clic sur la PREMIÈRE ligne de l'encart (son titre) */
    let t=e.target,dansTitre=false;
    while(t&&t!==box){if(t===box.children[0]){dansTitre=true;break;}t=t.parentNode;}
    if(e.target===box.children[0])dansTitre=true;
    if(!dansTitre)return;
    const idx=Array.prototype.indexOf.call(root.children,box)+1;
    setPsetFold(p=>p.indexOf(idx)>=0?p.filter(x=>x!==idx):p.concat([idx]));
  },[]);
  const psetTout=useCallback(()=>{
    setPsetFold(p=>p.length>=psetItems.length?[]:psetItems.map(x=>x.i));
  },[psetItems]);

  /* v10.35.1 : DÉCLARÉE ICI, et pas plus bas — l'écran de connexion sort par
     un `return` anticipé, et un hook placé après ne s'exécute pas à tous les
     rendus (erreur React #310 à l'ouverture). Tous les hooks doivent rester
     au-dessus de ce point. */
  const doExport=useCallback(async(kind)=>{
    setExpBusy(true);
    try{
      let src;
      if(expSrc==="now")src={plan:plan,notes:notes,tourMed:tourMed,tourDerog:tourDerog,medecins:medecins,actes:actes,salleReg:salleReg,planningType:planningType};
      else{
        const dd=(await window.firebaseDB.collection("backups").doc(expSrc).get()).data()||{};
        const pj=(x,def)=>{try{return typeof x==="string"?JSON.parse(x):(x||def);}catch(e){return def;}};
        /* v10.102 : l'équipe et les activités d'une sauvegarde sont en V2 (map + ordre)
           depuis la v9.7 — l'ancien champ, purgé, sortait une liste vide ou périmée. */
        const rdV2=(mp,ordRaw,leg)=>{
          if(!mp)return pj(leg,[]);
          const vals={};Object.keys(mp).forEach(k=>{const v=mp[k];vals[k]=typeof v==="string"?JSON.parse(v):v;});
          const ord=pj(ordRaw,null);
          const ids=Array.isArray(ord)?ord.map(String).filter(id=>vals[id]!==undefined):[];
          const rest=Object.keys(vals).filter(id=>ids.indexOf(id)<0);
          return ids.concat(rest).map(id=>vals[id]);
        };
        src={plan:dd.planV2||{},notes:pj(dd.notes,{}),tourMed:pj(dd.tourMed,{}),tourDerog:pj(dd.tourDerog,{}),
             medecins:rdV2(dd.medecinsV2,dd.medecinsV2Order,dd.medecins),actes:rdV2(dd.actesV2,dd.actesV2Order,dd.actes),salleReg:pj(dd.salleReg,[]),
             planningType:(dd.planningTypeV2!==undefined?pj(dd.planningTypeV2,{}):pj(dd.planningType,{}))};
      }
      src.exportDate=new Date().toISOString();src.version="v7";   /* v10.102 : relisible par 📂 Importer */
      const nom="planning-"+expPer.sy+"-"+String(expPer.sm+1).padStart(2,"0");
      if(kind==="tableau")expTelecharge(nom+".xls",expTable(expPer,src));
      else expTelecharge(nom+"-donnees.json",JSON.stringify(src),"application/json;charset=utf-8");
      const t=Date.now();setExpLast(t);setExpN(0);setExpSnooze(false);
      try{localStorage.setItem("cp6_expLast",String(t));localStorage.setItem("cp6_expN","0");}catch(e){}
      toast("Sauvegarde téléchargée","info");
    }catch(e){console.log("export:",e);toast("Échec de la sauvegarde","warn");}
    setExpBusy(false);
  },[expSrc,expPer,plan,notes,tourMed,tourDerog,medecins,actes,salleReg,planningType]);

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
        <button style={{width:"100%",padding:"11px",borderRadius:9,border:"1px solid var(--border)",background:"var(--bg2)",color:"var(--txt)",cursor:"pointer",fontSize:14,marginBottom:14,fontWeight:600}} onClick={()=>setAccessMode("view")}>👁 Consulter</button>
        <div style={{color:"var(--txt3)",fontSize:12,marginBottom:12,display:"flex",alignItems:"center",justifyContent:"center",gap:6}}>
          — édition —
          {fbStatus==="connecting"&&<span style={{fontSize:10,color:"#f59e0b"}}>⏳ Chargement...</span>}
          {fbStatus==="ok"&&Object.keys(medPins).length>0&&<span style={{fontSize:10,color:"#4ade80"}}>✓ {Object.keys(medPins).length} PIN(s) médecin</span>}
        </div>
        <input value={pinInput} onChange={e=>setPinInput(e.target.value)} onKeyDown={e=>{if(e.key==="Enter"){
    if(pinInput===editPin){setAccessMode("edit");setPinError(false);return;}
    const medEntry=Object.entries(medPins).find(([id,pin])=>pin===pinInput&&pin.length>=3);
    if(medEntry){setEditMedId(parseInt(medEntry[0]));setAccessMode("medecinEdit");setPinError(false);
      /* v10.72 : un ATTACHE ouvre directement sur l'onglet Attaches — son planning
         n'est pas dans l'onglet Planning, qui ne montre que les medecins. */
      const _mA=medecins.find(m=>m.id===parseInt(medEntry[0]));if(_mA&&_mA.role==="attache")setTab("attache");}
    else if(adminEnabled&&(()=>{const okA=adminPin&&adminPin.length>=3&&pinInput===adminPin;const okC=cadrePin&&cadrePin.length>=3&&pinInput===cadrePin;if(okA||okC)setIsCadre(!!okC&&!okA);return okA||okC;})()){setAdminAsk(true);setPinError(false);}
    else if(intCfg.show===true&&intCfg.pin&&intCfg.pin.length>=3&&pinInput===intCfg.pin){setInterneAsk(true);setPinError(false);}
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
              setAccessMode("medecinEdit");
              setPinError(false);
              const _mA=medecins.find(m=>m.id===parseInt(medEntry[0]));   /* v10.72 : attache -> onglet Attaches */
              if(_mA&&_mA.role==="attache")setTab("attache");
            } else if(adminEnabled&&(()=>{const okA=adminPin&&adminPin.length>=3&&pinInput===adminPin;const okC=cadrePin&&cadrePin.length>=3&&pinInput===cadrePin;if(okA||okC)setIsCadre(!!okC&&!okA);return okA||okC;})()){
              setAdminAsk(true);setPinError(false);
            } else if(intCfg.show===true&&intCfg.pin&&intCfg.pin.length>=3&&pinInput===intCfg.pin){
              setInterneAsk(true);setPinError(false);
            } else {
              setPinError(true);
            }
          }}>✏️ Édition</button>
        {adminAsk&&<div style={{marginTop:10,padding:10,borderRadius:9,border:"1.5px solid #7c3aed",background:"rgba(124,58,237,.08)"}}>
          <div style={{fontSize:11,color:"#7c3aed",fontWeight:800,marginBottom:6}}>{"🗝 Accès "+(isCadre?"cadre":"secrétaire")+" — votre prénom :"}</div>
          <input value={adminNameInput} onChange={e=>setAdminNameInput(e.target.value)} placeholder="Prénom" style={{...S.fi,width:"100%",textAlign:"center",marginBottom:8}}/>
          <button style={{width:"100%",padding:"9px",borderRadius:9,border:"none",background:"#7c3aed",color:"#fff",cursor:"pointer",fontSize:13,fontWeight:800}}
            onClick={()=>{const n=(adminNameInput||"").trim();if(!n)return;setAdminName(n);try{localStorage.setItem("cp6_adminName",n);}catch(e){}setAccessMode("adminEdit");setAdminAsk(false);}}>{"Entrer ("+(isCadre?"cadre":"secrétaire")+")"}</button>
        </div>}
        {interneAsk&&<div style={{marginTop:10,padding:10,borderRadius:9,border:"1.5px solid #0e9f9f",background:"rgba(14,159,159,.08)"}}>
          <div style={{fontSize:11,color:"#0e9f9f",fontWeight:800,marginBottom:6}}>🎓 Accès interne — votre prénom :</div>
          <input value={interneNameInput} onChange={e=>setInterneNameInput(e.target.value)} placeholder="Prénom" style={{...S.fi,width:"100%",textAlign:"center",marginBottom:8}}/>
          <button style={{width:"100%",padding:"9px",borderRadius:9,border:"none",background:"#0e9f9f",color:"#fff",cursor:"pointer",fontSize:13,fontWeight:800}}
            onClick={()=>{const n=(interneNameInput||"").trim();if(!n)return;setInterneName(n);try{localStorage.setItem("cp6_interneName",n);}catch(e){}setAccessMode("interneEdit");setInterneAsk(false);setTab("internes");}}>Entrer (interne)</button>
        </div>}
        <div style={{marginTop:14,fontSize:10,color:"var(--txt3)",textAlign:"center"}}>{APP_VERSION}</div>
      </div>
    </div>
  );

  const _per=getPeriodRange(year,month);
  const _pem=(_per.sm+PCFG.len-1)%12,_pey=_per.sm+PCFG.len-1>11?_per.sy+1:_per.sy;
  const _titlePeriod=MOIS[_per.sm]+" — "+MOIS[_pem]+" "+(_per.sy!==_pey?_per.sy+"/"+_pey:_pey);
  /* v10.29 : un SEUL jeu de props par ecran, utilise par l'onglet d'origine ET par la
     tuile de Construire (qui n'y change que l'annee, le mois et noNav). */
  const tourProps={medecins:medsAff,specColors,tourMins,tourMinsHard,tourAvoid,tourWish,applyTPForWeek,cleanTPForWeek,clearWeekActivities,reapplyPTWeek,purgeTourExtras,plan,tourDerog,lastReport:tourReport,setLastReport:setTourReport,tourCfg,setTourCfg,year:tourYear,month:tourMonth,setYear:setTourYear,setMonth:setTourMonth,tourMed,setTourMed,getEntries,isEdit:isEdit||(isInterEdit&&!isAttEdit),darkMode,setDarkMode,planningType,setPlan,allDays,toast};
  const gardeProps={onRemoveGarde:removeGardeDay,printWk,onPrint:()=>setModal("print"),year,month,prevM,nextM,medecins:medsAff,getEntry,allDays,isEdit,applyGarde,isMedAvailable,plan,setPlan,darkMode,setDarkMode,showFull,setShowFull,viewPeriod,allDays4,setViewPeriod,tourMed,gardeAvoid,gardeWish,toast};
  return(
    <div style={S.app}>
      <style>{setFoldCSS()+`@import url('https://fonts.googleapis.com/css2?family=Sora:wght@400;600;700;800&family=JetBrains+Mono:wght@500;700&display=swap');
*{box-sizing:border-box;margin:0;padding:0}
::-webkit-scrollbar{width:5px;height:5px}
::-webkit-scrollbar-track{background:var(--bg)}
::-webkit-scrollbar-thumb{background:var(--border);border-radius:3px}
td{background:var(--bg2)}

nav{scrollbar-width:none;-ms-overflow-style:none}
nav::-webkit-scrollbar { display: none; }
/* v10.52 : sur ordinateur (pointeur souris), la barre reapparait — le navigateur
   ne la dessine que si les onglets debordent, elle reste invisible sinon */
@media (pointer:fine){
  nav{scrollbar-width:thin}
  nav::-webkit-scrollbar{display:block;height:5px}
}
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

      {/* v10.107 : la couleur SUIT le type — le style ignorait notif.type, un
          avertissement s'affichait donc en vert comme une confirmation. */}
      {notif&&<div onClick={()=>setNotif(null)} title="Cliquer pour fermer" style={{...S.notif,background:"var(--bg-td)",cursor:"pointer",
        borderColor:notif.type==="warn"?"#f59e0b":notif.type==="lock"?"#a78bfa":"#4ade80",
        borderWidth:notif.type==="ok"?1.5:2.5,
        color:notif.type==="warn"?"#b45309":notif.type==="lock"?"#6d28d9":"var(--txt)"}}>{notif.msg}</div>}
      {netOff&&<div data-botbar="1" style={{position:"fixed",bottom:0,left:0,right:0,background:"#64748b",color:"#fff",textAlign:"center",fontSize:12,padding:"6px",zIndex:502,fontWeight:600}}>
        📴 Hors ligne — dernier planning reçu · lecture seule
      </div>}
      {isMedEdit&&botOn&&<div data-botbar="1" style={{position:"fixed",bottom:0,left:0,right:0,background:"#1d4ed8",color:"#fff",textAlign:"center",fontSize:12,padding:"6px",zIndex:500,fontWeight:600}}>
        ✏️ {isInterEdit?"Édition étendue":"Mode édition restreinte"} — Dr. {(medecins.find(m=>m.id===editMedId)||{nom:""}).nom}
      </div>}
      {isInterne&&botOn&&<div data-botbar="1" style={{position:"fixed",bottom:0,left:0,right:0,background:"#0e9f9f",color:"#fff",textAlign:"center",fontSize:12,padding:"6px",zIndex:500,fontWeight:600}}>
        🎓 Accès interne — {interneName||"?"}
      </div>}
      {isAdminEdit&&botOn&&<div data-botbar="1" style={{position:"fixed",bottom:0,left:0,right:0,background:"#7c3aed",color:"#fff",textAlign:"center",fontSize:12,padding:"6px",zIndex:500,fontWeight:600}}>
        🗝 {isCadre?"Édition cadre":"Édition secrétaire"} — {adminName||"?"}
      </div>}

      {/* HEADER */}
      <header style={S.hdr}>
        <div style={{display:"flex",alignItems:"center",gap:7,flexShrink:0}}>
          <span onClick={()=>{setPinInput("");setPinError(false);setIsCadre(false);setAccessMode("ask");}} title="Retour à l'accueil" style={{fontSize:20,color:"#f85149",cursor:"pointer"}}>♥</span>
          {/* v10.27 : l'administratif y a droit aussi — c'est lui qui remplit le plus
              souvent les semaines blanches et les reports. */}
          {(isEdit||isMedEdit||isAdminEdit)&&<div style={{display:"flex",gap:3}}>
            <button onClick={doUndo} disabled={!canUndo} title="Annuler (retour arrière)"
              style={{width:26,height:26,borderRadius:6,border:"1px solid rgba(255,255,255,.25)",background:canUndo?"rgba(255,255,255,.1)":"transparent",color:canUndo?"#f0f6fc":"#484f58",cursor:canUndo?"pointer":"default",fontSize:13,display:"flex",alignItems:"center",justifyContent:"center"}}>↶</button>
            <button onClick={doRedo} disabled={!canRedo} title="Rétablir (retour avant)"
              style={{width:26,height:26,borderRadius:6,border:"1px solid rgba(255,255,255,.25)",background:canRedo?"rgba(255,255,255,.1)":"transparent",color:canRedo?"#f0f6fc":"#484f58",cursor:canRedo?"pointer":"default",fontSize:13,display:"flex",alignItems:"center",justifyContent:"center"}}>↷</button>
          </div>}
          <div>
            <div style={{fontWeight:800,fontSize:14,color:"#f0f6fc"}}>CardioPlanning</div>
            <div style={{fontSize:8,color:"#484f58",display:"flex",alignItems:"center",gap:4}}>
              CHL & CHB{!isEdit&&<span style={{color:"#e3b341",marginLeft:5}}>👁</span>}
              {/* v10.106 : l'indicateur vit dans le BLOC DE TITRE, pas dans la rangée de
                  l'en-tête — celle-ci est un flex de hauteur fixe où tout ajout vole sa
                  largeur au <nav>, ce qui rendait les onglets inatteignables sur téléphone. */}
              {perClose&&<span title={perArchivee?"Période archivée : retirée des données actives et relue ici en consultation. Désarchivez-la depuis Paramètres pour la modifier.":"Période close : elle précède la période en cours. Les modifications y sont bloquées pour tout le monde. L'éditeur peut lever le verrou depuis Paramètres, le temps d'une session."} style={{background:perArchivee?"#0e7490":"#7c3aed",color:"#fff",fontWeight:800,fontSize:9,marginLeft:4,padding:"2px 6px",borderRadius:9,whiteSpace:"nowrap",letterSpacing:.2}}>{perArchivee?"🗄 PÉRIODE ARCHIVÉE":"🔒 PÉRIODE CLOSE"}</span>}
              <span style={{marginLeft:4,width:6,height:6,borderRadius:"50%",display:"inline-block",
                background:netOff?"#94a3b8":fbStatus==="ok"?"#4ade80":fbStatus==="error"?"#ef4444":fbStatus==="offline"?"#94a3b8":"#f59e0b"}}
                title={netOff?"Hors ligne — lecture seule":fbStatus==="ok"?"Firebase connecté":fbStatus==="error"?"Erreur Firebase":fbStatus==="offline"?"Mode local (CodeSandbox)":"Connexion..."}/>
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
              onClick={()=>goTab(v)}
              style={{...S.nb,...(tab===v?S.nba:{}),cursor:"grab",userSelect:"none"}}>{l}</button>
          ))}
        </nav>
      </header>

      <main style={{...S.main,paddingBottom:GRID_FIT.indexOf(tab)>=0?12:110}}>

      {/* MON PLANNING */}
      

      {/* v9.48 : le filtre « depuis aujourd'hui » peut ne laisser aucun jour quand on
          remonte à une période révolue — le tableau se vidait alors sans un mot. */}
      {(()=>{
        if(showFull||!allDays4||allDays4.length===0)return null;
        const tod=new Date();tod.setHours(0,0,0,0);
        if(allDays4.some(o=>new Date(o.y,o.m,o.d)>=tod))return null;
        return(
          <div style={{display:"flex",alignItems:"center",gap:10,flexWrap:"wrap",background:"rgba(245,158,11,.12)",border:"1px solid #f59e0b66",borderRadius:9,padding:"10px 13px",marginBottom:10}}>
            <span style={{fontSize:16}}>🗓️</span>
            <span style={{fontSize:12,color:"var(--txt)",flex:1,minWidth:180}}>{"Cette période est entièrement passée. L'affichage « depuis aujourd'hui » ne laisse donc aucun jour."}</span>
            <button onClick={()=>setShowFull(true)} style={{fontSize:11,fontWeight:800,padding:"5px 12px",borderRadius:6,border:"1.5px solid #f59e0b",background:"rgba(245,158,11,.15)",color:"#b45309",cursor:"pointer"}}>📅 Afficher la période complète</button>
          </div>
        );
      })()}

      {/* PLANNING */}
      {tab==="planning"&&(
        <div>
          {isEdit&&!expSnooze&&<ExportRappel nModifs={expN} seuil={expSeuil} dernier={expLast}
            onAller={()=>goTab("partage")} onPlusTard={()=>setExpSnooze(true)}/>}
          {/* v10.32 : rappel des demandes ouvertes. Il apparait quelle que soit la
              periode affichee — la demande porte sur la periode suivante, mais
              personne n'y va spontanement (sa remarque du 12/08). */}
          <BuildAsk build={build} medecins={medsAff} editMedId={accessMode==="medecinEdit"?editMedId:null}
            onRepondre={(k,champ)=>setBuild(p=>{const B0=(p||{})[k]||{};const c={...(B0[champ]||{})};c[editMedId]=1;return {...(p||{}),[k]:{...B0,[champ]:c}};})}
            onGoPer={(k)=>{const a=String(k).split("_");setYM({year:+a[0],month:+a[1]});}}/>
          {/* v10.18 : alerte si la période affichée n'est pas couverte par les vacances saisies.
              Placée dans le Planning — l'onglet toujours ouvert — et réservée à l'éditeur.
              Pas de blocage de l'écriture : changer une borne ne déplace ni n'efface aucune
              activité, cela ne change que ce qui est AFFICHÉ. Bloquer gênerait sans protéger. */}
          {/* v10.22 : alerte de fin de liste d'astreinte, sur le modèle de celle des
              vacances — Planning seulement, éditeur seulement, seuil à 6 semaines. */}
          {isEdit&&(()=>{
            const auj=new Date();auj.setHours(0,0,0,0);
            const lim=new Date(auj);lim.setDate(lim.getDate()+42);
            let fin=null;
            Object.keys(astreinte||{}).forEach(k=>{
              const v=astreinte[k];if(v===undefined||v===null||v==="")return;
              const p=String(k).split("-").map(Number);
              if(p.length<3||isNaN(p[0]))return;
              const d0=new Date(p[0],p[1],p[2]);if(isNaN(d0))return;
              const d1=new Date(d0);d1.setDate(d1.getDate()+6);   // une clé de semaine couvre 7 jours
              if(!fin||d1>fin)fin=d1;
            });
            if(fin&&fin>=lim)return null;
            const reste=fin?Math.max(0,Math.round((fin-auj)/86400000)):0;
            return <div style={{background:"#fffbeb",border:"1px solid #fcd34d",borderRadius:9,padding:"9px 12px",
              fontSize:12.5,color:"#78350f",marginBottom:8,display:"flex",gap:9,alignItems:"center",flexWrap:"wrap"}}>
              <span>⚠</span>
              <span>{fin?<><b>Astreinte remplie jusqu'au {fmtLongD(fin)}</b> — soit {reste} jour{reste>1?"s":""}. Pensez à compléter la suite.</>
                        :<><b>Astreinte non renseignée.</b> Aucune semaine n'est remplie.</>}</span>
              <button onClick={()=>goTab("astreinte")} style={{...S.icnBtn,width:"auto",padding:"3px 10px",fontSize:11,fontWeight:800,marginLeft:"auto"}}>Compléter</button>
            </div>;
          })()}
          {isEdit&&(()=>{
            const p0=perStart(year,month);const a=new Date(p0.sy,p0.sm,1),b=perEnd(p0.sy,p0.sm);
            const couvert=vacs.some(v=>v.d1&&v.d2&&new Date(v.d2+"T00:00:00")>=a&&new Date(v.d1+"T00:00:00")<=b);
            if(couvert)return null;
            return <div style={{background:"#fffbeb",border:"1px solid #fcd34d",borderRadius:9,padding:"9px 12px",
              fontSize:12.5,color:"#78350f",marginBottom:8,display:"flex",gap:9,alignItems:"center",flexWrap:"wrap"}}>
              <span>⚠</span>
              <span><b>Vacances scolaires non renseignées</b> pour cette période — les bornes affichées sont provisoires.</span>
              <button onClick={()=>goTab("partage")} style={{...S.icnBtn,width:"auto",padding:"3px 10px",fontSize:11,fontWeight:800,marginLeft:"auto"}}>Les saisir</button>
            </div>;
          })()}
          {isEdit&&<IssuePanel iss={planIssues} open={plIssOpen} setOpen={setPlIssOpen} onGo={goIssue}/>}
          <div style={S.bar}>
            <div style={{display:"flex",alignItems:"center",gap:8}}>
              <button onClick={prevM} style={S.arr}>‹</button>
              <h2 style={S.mTit}>{"📅 "+_titlePeriod}</h2>
              <button onClick={nextM} style={S.arr}>›</button>
            </div>
            <div style={{display:"flex",gap:4,alignItems:"center",marginLeft:"auto"}}>
              <button onClick={()=>setModal("print")} title="Imprimer" style={{...S.arr,fontSize:13,width:30}}>🖨️</button>
              <button onClick={()=>setDarkMode(d=>!d)} style={{...S.arr,fontSize:13,width:30}}>{darkMode?"☀️":"🌓"}</button>
              <button onClick={()=>setShowFull(f=>!f)} title={showFull?"Depuis aujourd'hui":"Mois complet"} style={{...S.arr,fontSize:16,width:32,color:showFull?"var(--today-c)":"var(--txt2)",border:`1px solid ${showFull?"var(--today-c)":"var(--border)"}`}}>{showFull?"📅":"🗓️"}</button>
              {canPref&&<button onClick={()=>setPrefOn(v=>!v)} title="Afficher les préférences de tour et de garde" style={{...S.arr,fontSize:14,width:30,color:prefOn?"var(--today-c)":"var(--txt2)",border:`1px solid ${prefOn?"var(--today-c)":"var(--border)"}`}}>⭐</button>}
            </div>
          </div>
          {prefOn&&<div style={{display:"flex",flexWrap:"wrap",gap:"4px 10px",alignItems:"center",marginBottom:8,fontSize:10,color:"var(--txt3)"}}>
            <span style={{fontWeight:700,textTransform:"uppercase"}}>Préférences :</span>
            <span style={{display:"flex",alignItems:"center",gap:4}}><span style={{width:12,height:12,borderRadius:3,background:"rgba(56,139,253,.20)",border:"1px solid #388bfd"}}></span>souhaite tourner</span>
            <span style={{display:"flex",alignItems:"center",gap:4}}><span style={{width:12,height:12,borderRadius:3,background:"rgba(248,81,73,.18)",border:"1px solid #f85149"}}></span>préfère ne pas tourner</span>
            <span>⭐ souhaite la garde</span>
            <span>🚫 préfère éviter la garde</span>
          </div>}
          {(isEdit||isMedEdit)&&<div style={{display:"flex",gap:6,alignItems:"center",marginBottom:8}}>
            <button style={{fontSize:11,padding:"3px 12px",borderRadius:6,border:"1.5px solid #388bfd",background:"rgba(56,139,253,.10)",color:"#388bfd",fontWeight:800,cursor:"pointer"}} onClick={()=>openPtModal(null)}>📋 Planning type</button>
          </div>}
          <div style={{display:"flex",flexWrap:"wrap",gap:4,marginBottom:8,alignItems:"center"}}>
            <span style={{fontSize:10,color:"var(--txt3)",fontWeight:700,textTransform:"uppercase",marginRight:4}}>Filtre:</span>
            <button onClick={()=>setPlanFilter([])} style={{padding:"2px 8px",borderRadius:10,border:"1px solid var(--border)",background:planFilter.length===0?"#1d4ed8":"var(--bg2)",color:planFilter.length===0?"#fff":"var(--txt2)",fontSize:11,cursor:"pointer",fontWeight:600}}>Tous</button>
            {medPlan.map(m=>{const on=planFilter.includes(m.id);return <button key={m.id} onClick={()=>setPlanFilter(p=>on?p.filter(x=>x!==m.id):[...p,m.id])} style={{padding:"2px 7px",borderRadius:10,border:`1px solid ${on?m.color:"var(--border)"}`,background:on?m.color:"var(--bg2)",color:on?"#fff":"var(--txt2)",fontSize:11,cursor:"pointer",fontWeight:on?700:400}}>{m.init}</button>;})}
            {intCfg.show===true&&(intCfg.sems||[]).length>0&&<button onClick={()=>setIntGardeOn(v=>!v)} title="Afficher la colonne de garde des internes (lecture seule)" style={{padding:"2px 8px",borderRadius:10,border:`1px solid ${intGardeOn?"#1d4ed8":"var(--border)"}`,background:intGardeOn?"#1d4ed8":"var(--bg2)",color:intGardeOn?"#fff":"var(--txt2)",fontSize:11,cursor:"pointer",fontWeight:intGardeOn?700:400}}>🎓 Garde int.</button>}
          </div>
          {<GridV onRemoveGarde={removeGardeDay} planIssues={planIssues.map} intGarde={intGardeOn?((y2,m2,d2)=>intGardeDuJour(getEntries,intCfg,y2,m2,d2)):null} printWk={printWk} allDays4={allDays4} allDays={allDays} year={year} month={month} meds={filteredMeds} getEntries={getEntries} acteById={acteById} onCell={openCell} isEdit={isAnyEdit} notes={notesAff} isVac={isVac} applyGarde={applyGarde} allMeds={medsAff} viewPeriod={viewPeriod} allDays4={allDays4} showFull={showFull} gardeLocked={isAdminEdit||isAttEdit} onCellHistory={isAnyEdit?openCellHistory:null} prefFor={prefOn?prefFor:null} gardePref={gardePrefFor} getAstreinteForDay={prefOn?null:getAstreinteForDay}/>}
        </div>
      )}

      {/* TOUR MÉDICAL */}
      {tab==="tourmedical"&&<TourTab {...tourProps}/>}

      {/* v10.29 : CONSTRUIRE — pas a pas, memes ecrans, une seule periode */}
      {tab==="construire"&&<BuildTab build={build} setBuild={setBuild} medecins={medsAff} getEntries={getEntries} tourMed={tourMed} isEdit={(isEdit||isInterEdit)&&!isAttEdit} darkMode={darkMode} setDarkMode={setDarkMode} author={authorRef.current} goTab={goTab} onOpenBip={bipOpen} onApplyPT={(per)=>openPtModal(null,"apply",per)} onRemovePT={(per)=>openPtModal(null,"remove",per)} tourProps={tourProps} gardeProps={gardeProps}/>}

      {tab==="chl"&&<SiteView issMap={issAllMap} printWk={printWk} onPrint={()=>setModal("print")} colOrder={colOrder["CHL"]||null} onOrder={(cols)=>{setColModal({site:"CHL",cols});setModal("colOrder");}} site="CHL" intCfg={intCfg} salleReg={salleReg} year={year} month={month} prevM={prevM} nextM={nextM} actes={actes} medecins={medsAff} getEntries={getEntries} salleOcc={salleOcc} allDays={allDays} isEdit={isEdit||isAdminEdit||(isMedEdit&&!isAttEdit)} notes={notesAff}
        onPickSite={({salle,siteActes,d,sl,y,m})=>{if(!vOuvre(y,m,d))return;setMData({salle,siteActes,d,sl,y,m});setModal("pickMedSite");}}
        darkMode={darkMode} setDarkMode={setDarkMode} showFull={showFull} setShowFull={setShowFull} viewPeriod={viewPeriod} allDays4={allDays4} setViewPeriod={setViewPeriod}/>}

      {tab==="chb"&&<div>
        <SiteView issMap={issAllMap} printWk={printWk} onPrint={()=>setModal("print")} colOrder={colOrder["CHB"]||null} onOrder={(cols)=>{setColModal({site:"CHB",cols});setModal("colOrder");}} site="CHB" intCfg={intCfg} darkMode={darkMode} setDarkMode={setDarkMode} salleReg={salleReg} year={year} month={month} prevM={prevM} nextM={nextM} actes={actes} medecins={medsAff} getEntries={getEntries} salleOcc={salleOcc} allDays={allDays} isEdit={isEdit||isAdminEdit||(isMedEdit&&!isAttEdit)} showFull={showFull} setShowFull={setShowFull} notes={notesAff}
        onPickSite={({salle,siteActes,d,sl,y,m})=>{if(!vOuvre(y,m,d))return;
          const bip=actes.find(a=>a.id==="BIP");
          /* v9.86 : les salles du BIP viennent de l'activité elle-même, plus d'une liste
             figée. Une salle ajoutée à Béthune et autorisée pour le BIP est reconnue sans
             modification du code — dernier endroit où un nom de salle était comparé à une
             liste écrite en dur. */
          const full=bip&&(bip.salles||[]).includes(salle)?[...siteActes.filter(a=>a.id!=="BIP"),bip]:siteActes;
          setMData({salle,siteActes:full,d,sl,y,m});setModal("pickMedSite");}} viewPeriod={viewPeriod} allDays4={allDays4} setViewPeriod={setViewPeriod}/></div>}

      {tab==="plateau"&&<ActTabView issMap={issAllMap} title="❤️ PT Cardio" titleColor="#e3b341" intCfg={intCfg}
        rows={ptRows} orderCtl={isEdit} onOrder={()=>setModal("ptOrder")}
        year={year} month={month} prevM={prevM} nextM={nextM} medecins={medsAff} actes={actes}
        getEntries={getEntries} allDays={allDays} notes={notesAff} ideFeature={true} ideOn={ideOn} setIdeOn={setIdeOn} ideCfg={ideCfg} setIdeCfg={setIdeCfg} canIde={isEdit||(isAdminEdit&&isCadre)} printWk={printWk} onPrint={()=>setModal("print")} isEdit={isEdit||isAdminEdit||(isMedEdit&&!isAttEdit)} showFull={showFull} setShowFull={setShowFull} darkMode={darkMode} setDarkMode={setDarkMode} showFull={showFull} setShowFull={setShowFull} viewPeriod={viewPeriod} allDays4={allDays4} setViewPeriod={setViewPeriod}
        onPickAct={({row,d,sl,y,m})=>{if(!vOuvre(y,m,d))return;setMData({row,d,sl,y,m});setModal("pickMedAct");}}/>}

      {tab==="angio"&&<SiteView issMap={issAllMap} printWk={printWk} onPrint={()=>setModal("print")} colOrder={colOrder["ANGIO"]||null} onOrder={(cols)=>{setColModal({site:"ANGIO",cols});setModal("colOrder");}} site="ANGIO" intCfg={intCfg} salleReg={salleReg} year={year} month={month} prevM={prevM} nextM={nextM}
        actes={actes} medecins={medsAff} getEntries={getEntries} salleOcc={salleOcc}
        allDays={allDays} isEdit={isEdit||isAdminEdit||(isMedEdit&&!isAttEdit)} notes={notesAff}
        onPickSite={({salle,siteActes,d,sl,y,m})=>{if(!vOuvre(y,m,d))return;setMData({salle,siteActes,d,sl,y,m});setModal("pickMedSite");}}
        darkMode={darkMode} setDarkMode={setDarkMode} showFull={showFull} setShowFull={setShowFull} viewPeriod={viewPeriod} allDays4={allDays4} setViewPeriod={setViewPeriod}/>}
      {false&&null&&<ActTabView title="🔬 PT Angio" titleColor="#c084fc"
        rows={[
          {label:"Coronarographie",ids:["CORO"],color:"#c084fc",salle:null},
          {label:"TAVI",ids:["TAVI"],color:"#fb7185",salle:null},
          {label:"FOP / FAG",ids:["FOP"],color:"#34d399",salle:null},
        ]}
        year={year} month={month} prevM={prevM} nextM={nextM} medecins={medsAff} actes={actes}
        getEntries={getEntries} allDays={allDays} isEdit={isEdit} darkMode={darkMode} setDarkMode={setDarkMode} showFull={showFull} setShowFull={setShowFull} viewPeriod={viewPeriod} allDays4={allDays4} setViewPeriod={setViewPeriod}
        onPickAct={({row,d,sl,y,m})=>{if(!vOuvre(y,m,d))return;setMData({row,d,sl,y,m});setModal("pickMedAct");}}/>}

      {tab==="garde"&&<GardeView {...gardeProps}/>}


      {tab==="plantype"&&(
        <div>
          <div style={{...S.bar,position:"sticky",top:HDR_H,zIndex:40,background:"var(--bg)",paddingTop:6,paddingBottom:6}}>
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
          <PlanTypeGrid medecins={[...medPlan,...medAttache,...medecins.filter(m=>m.role==="ide")]} actes={actes} planningType={planningType} setPlanningType={setPlanningType} isEdit={(isEdit||isInterEdit)&&!isAttEdit} acteById={acteById} setMData={setMData} setModal={setModal} perDays={allDays4} onMedClick={isEdit?((med)=>setDeactMed(med.id)):null}/>
          {deactMed&&<DeactModal med={medecins.find(m=>m.id===deactMed)} perDays={allDays4} perLbl={perLibelle(perStart(year,month).sy,perStart(year,month).sm)} onSave={(rgs)=>saveOff(deactMed,rgs)} onClose={()=>setDeactMed(null)} countActs={(du,au)=>offCount(deactMed,du,au)} onClear={(du,au)=>offClear(deactMed,du,au)}/>}
          <PTOccRooms medecins={medsAff} planningType={planningType} actes={actes} acteById={acteById} salleReg={salleReg} darkMode={darkMode} perDays={allDays4}/>
        </div>
      )}

      {tab==="attache"&&(
        <div>
          {isEdit&&<IssuePanel iss={attIssues} open={plIssOpen} setOpen={setPlIssOpen} onGo={goIssue}/>}
          <div style={S.bar}>
            <div style={{display:"flex",alignItems:"center",gap:8}}><button onClick={prevM} style={S.arr}>‹</button><h2 style={S.mTit}>{"👔 Attachés — "+(MOIS[perStart(year,month).sm]+" — "+MOIS[(perStart(year,month).sm+PCFG.len-1)%12]+" "+perStart(year,month).sy)}</h2><button onClick={nextM} style={S.arr}>›</button></div>
            <div style={{display:"flex",gap:4,alignItems:"center",marginLeft:"auto"}}><button onClick={()=>setModal("print")} title="Imprimer" style={{...S.arr,fontSize:13,width:30}}>🖨️</button><button onClick={()=>setDarkMode(d=>!d)} style={{...S.arr,fontSize:13,width:30}}>{darkMode?"☀️":"🌓"}</button><button onClick={()=>setShowFull(f=>!f)} title={showFull?"Depuis aujourd'hui":"Mois complet"} style={{...S.arr,fontSize:16,width:32,color:showFull?"var(--today-c)":"var(--txt2)",border:`1px solid ${showFull?"var(--today-c)":"var(--border)"}`}}>{showFull?"📅":"🗓️"}</button></div>
          </div>
           {isEdit&&<div style={{display:"flex",gap:6,alignItems:"center",marginBottom:8}}>
             <button style={{fontSize:11,padding:"3px 12px",borderRadius:6,border:"1.5px solid #388bfd",background:"rgba(56,139,253,.10)",color:"#388bfd",fontWeight:800,cursor:"pointer"}} onClick={()=>openPtModal(null)}>📋 Planning type</button>
           </div>}
          {<GridV onRemoveGarde={removeGardeDay} planIssues={attIssues.map} printWk={printWk} allDays4={allDays4} allDays={allDays} year={year} month={month} meds={[...medAttache,...medecins.filter(m=>m.role==="ide")]} getEntries={getEntries} acteById={acteById} onCell={openCell} isEdit={isAnyEdit} notes={notesAff} isVac={isVac} applyGarde={applyGarde} allMeds={medsAff} viewPeriod={viewPeriod} allDays4={allDays4} showFull={showFull} showGarde={false} gardeLocked={isAdminEdit||isAttEdit} onCellHistory={isAnyEdit?openCellHistory:null} getAstreinteForDay={getAstreinteForDay}/>}
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
                      {a.id==="TP"&&<div style={{fontSize:9,color:"var(--txt3)"}}>{medecins.filter(m3=>m3.partTime===true).map(m3=>m3.init).join(", ")||"aucun médecin en temps partiel"}</div>}
                      {a.id!=="TP"&&(a.medecinsAutorise&&a.medecinsAutorise.length)>0&&<div style={{fontSize:9,color:"var(--txt3)"}}>{(a.medecinsAutorise.includes("__AUCUN__")?"🚫 Aucun médecin":a.medecinsAutorise.join(", "))}</div>}
                      {(a.ideN>0)&&<div style={{fontSize:9,color:"#3fb950",fontWeight:700}}>{"🩺 "+a.ideN+" IDE nécessaire"+(a.ideN>1?"s":"")}</div>}
                {(a.id==="GARDE"||a.id==="REPOS_GARDE")&&<div style={{fontSize:9,color:"#16a34a",fontWeight:700}}>⚙ Synchronisé avec la coche « Garde » de l'onglet Équipe</div>}
                      {a.id==="TP"&&<div style={{fontSize:9,color:"#16a34a",fontWeight:700}}>⚙ Synchronisé avec la coche « Temps partiel » des fiches médecins</div>}
                      {a.csReport&&<div style={{fontSize:9,color:"#7c3aed",fontWeight:700}}>📥 Proposée dans l'onglet Reports</div>}
                      {a.adminOk&&<div style={{fontSize:9,color:"#7c3aed",fontWeight:700}}>✏️ Secrétaires</div>}
                      {a.cadreOk&&<div style={{fontSize:9,color:"#7c3aed",fontWeight:700}}>✏️ Cadres</div>}
                      {a.interneOk&&<div style={{fontSize:9,color:"#0e9f9f",fontWeight:700}}>{"🎓 Internes"+(a.interneSelf?" (posable par eux)":"")}</div>}
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

      {tab==="equipe"&&accessMode!=="adminEdit"&&!isMedEdit&&(
        <div>
          <div style={S.bar}><h2 style={S.mTit}>👥 Équipe</h2><div style={{display:"flex",gap:4,alignItems:"center",marginLeft:"auto"}}><button onClick={()=>setDarkMode(d=>!d)} style={{...S.arr,fontSize:13,width:30}}>{darkMode?"☀️":"🌓"}</button></div></div>
      {isEdit&&<div style={{display:"flex",gap:6,alignItems:"center",marginBottom:10}}>
        <button style={{fontSize:11,padding:"3px 12px",borderRadius:6,border:"1.5px solid #16a34a",background:"rgba(22,163,74,.10)",color:"#16a34a",fontWeight:800,cursor:"pointer"}} onClick={()=>{setMData({_new:true,id:Date.now(),nom:"",prenom:"",init:"",color:"#3b82f6",garde:true,tourMed:true,role:"medecin"});setModal("editMed");}}>+ Ajouter</button>
        <span style={{fontSize:10,color:"var(--txt3)"}}>▲▼ sur une fiche : ordre d'affichage dans tous les plannings</span>
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
                      {djRole(m)&&<div style={{fontSize:10,color:"var(--txt3)"}}>{djTuileTxt(m,intCfg)}</div>}
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
                      {isEdit&&<button style={{...S.icnBtn,fontSize:11,textAlign:"center"}} onClick={()=>{setMData({...m,_pinMode:true});setModal("editMedPin");}}>🔑</button>}
                      {isEdit&&<div style={{display:"flex",gap:3}}>
                        <button title="Avancer dans l'ordre" style={{...S.icnBtn,fontSize:11,fontWeight:800}} onClick={()=>moveMed(m.id,-1)}>▲</button>
                        <button title="Reculer dans l'ordre" style={{...S.icnBtn,fontSize:11,fontWeight:800}} onClick={()=>moveMed(m.id,1)}>▼</button>
                      </div>}
                    </div>
                  </div>
                ))}
              </div>
            </div>
          ))}
          <InternesEquipe intCfg={intCfg} setIntCfg={setIntCfg} isEdit={isEdit}/>
        </div>
      )}

      {tab==="reports"&&<div><div style={{display:"flex",justifyContent:"flex-end",marginBottom:6}}><button onClick={()=>setDarkMode(d=>!d)} style={{...S.arr,fontSize:13,width:30}}>{darkMode?"☀️":"🌓"}</button></div><ReportsView salleReg={salleReg} medecins={medsAff} actes={actes} getEntries={getEntries} tourMed={tourMed} planningType={planningType} isVac={isVac} isEdit={isEdit} editMedId={editMedId} accessMode={accessMode} csBlanches={csBlanches} setCsBlanches={setCsBlanches} csRep={csRep} setCsRep={setCsRep} csActsSel={csActsSel} setCsActsSel={setCsActsSel} addEntry={addEntry} setNotes={setNotes} csActsGlobal={csActsGlobal} adminOkKey={roleOkKey} adminReports={isAdminEdit&&adminCanReports} adminName={adminName} removeEntry={removeEntry} year={year} month={month} toast={toast}/></div>}
      {tab==="internes"&&<InternesView intCfg={intCfg} setIntCfg={setIntCfg} actes={actes} acteById={acteById} getEntries={getEntries} setEntry={setEntry} isVac={isVac} year={year} month={month} allDays={allDays} viewPeriod={viewPeriod} showFull={showFull} setShowFull={setShowFull} canEdit={isEdit||(isInterEdit&&!isAttEdit)||isAdminEdit||isInterne} canSalle={isEdit||(isInterEdit&&!isAttEdit)||(isAdminEdit&&isCadre)} intSelf={isInterne} salleReg={salleReg} prevM={prevM} nextM={nextM} darkMode={darkMode} setDarkMode={setDarkMode}/>}
      {tab==="aide"&&<div><div style={{display:"flex",justifyContent:"flex-end",marginBottom:6}}><button onClick={()=>setDarkMode(d=>!d)} style={{...S.arr,fontSize:13,width:30}}>{darkMode?"☀️":"🌓"}</button></div><HelpView/></div>}
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
        /* v9.49 : liste d'affichage seule — les statistiques et le retrait de période
           continuent de porter sur toute la période, quelle que soit l'impression. */
        const astPrintDays=printWk?allDays4M.filter(o=>inPrintRange(printWk,o.y,o.m,o.d)):allDays4M;
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
            const sun=new Date(mn);sun.setDate(sun.getDate()+6);
            if(sun>end)break; // semaine incomplète (ex. lundi férié isolé) → attribuée par la période suivante
            list.push({y:mn.getFullYear(),m:mn.getMonth(),d:mn.getDate()});
          }
          return list;
        })();
        const astWeekDays=(mon)=>[0,1,2,3,4,5,6].map(i=>{const dt=new Date(mon.y,mon.m,mon.d+i);return{y:dt.getFullYear(),m:dt.getMonth(),d:dt.getDate()};});
        const astAbsPart=(mid,days)=>days.some(({y,m,d})=>{
          const sls=isWE(y,m,d)?["JOUR"]:["M","AM"];
          return sls.some(sl=>getEntries(mid,y,m,d,sl).some(e=>ABS_IDS.includes(e.acteId)));
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
            <div style={{display:"flex",alignItems:"center",gap:6,marginBottom:12,flexWrap:"wrap",position:"sticky",top:HDR_H,zIndex:40,background:"var(--bg)",paddingTop:6,paddingBottom:6}}>
              <button onClick={prevP} style={S.arr}>‹</button>
              <h2 style={{...S.mTit,margin:0}}><span style={{color:"#7c3aed"}}>📞</span> {pLabel}</h2>
              <button onClick={nextP} style={S.arr}>›</button>
                <button onClick={()=>setModal("print")} title="Imprimer" style={{...S.arr,fontSize:13,width:30,marginLeft:"auto"}}>🖨️</button>
                <button onClick={()=>setDarkMode(d=>!d)} style={{...S.arr,fontSize:13,width:30}}>{darkMode?"☀️":"🌓"}</button>
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
            <div style={{maxWidth:620,marginBottom:14,padding:12,borderRadius:10,border:"1px solid var(--border)",background:"var(--bg2)"}}>
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
                        <span style={{display:"inline-flex",width:22,height:22,borderRadius:"50%",background:m.color,color:"#fff",fontSize:8,fontWeight:800,alignItems:"center",justifyContent:"center",marginRight:5,verticalAlign:"middle"}}>{m.init}</span>
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
            <TableScroll memId="astreinte">
              {/* v10.22 : UNE TUILE PAR SEMAINE. L'astreinte est déjà enregistrée par
                  SEMAINE, un jour ne l'écrasant qu'en cas d'exception — l'ancien tableau
                  développait donc artificiellement sept lignes identiques. Les semaines à
                  exception sont bordées de violet et s'ouvrent d'elles-mêmes. Rien ne change
                  à l'enregistrement, à l'export ni à l'impression : affichage seul. */}
              {(()=>{
                const sems=[];let cur=null;
                astPrintDays.forEach(({y,m,d})=>{
                  const wk=monKey2(y,m,d);
                  if(!cur||cur.wk!==wk){cur={wk,jours:[]};sems.push(cur);}
                  cur.jours.push({y,m,d});
                });
                const fmtJ=(o)=>o.d+" "+MOIS[o.m].slice(0,4).toLowerCase()+".";
                /* v10.23 : les tuiles s'alignent sur le cadre recapitulatif du dessus
                   (meme maxWidth 560) — pleine largeur, elles etaient peu pratiques. */
                return <div style={{padding:"4px 0",maxWidth:620}}>
                  {sems.map(sem=>{
                    const j0=sem.jours[0],j9=sem.jours[sem.jours.length-1];
                    const exc=sem.jours.filter(o=>{const dk=o.y+"-"+o.m+"-"+o.d;return dk!==sem.wk&&typeof astreinte[dk]==="string";});
                    /* v10.26 : les semaines a exception ne s'ouvrent plus d'elles-memes —
                       la bande des jours (a droite) dit deja qui remplace qui et quand. */
                    const ouvert=astSemOuv[sem.wk]===true;
                    const midS=astreinte[sem.wk];
                    const medS=midS?medecins.find(x=>String(x.id)===String(midS)):null;
                    const auj=sem.jours.some(o=>o.d===astToday.getDate()&&o.m===astToday.getMonth()&&o.y===astToday.getFullYear());
                    return <div key={sem.wk} style={{border:"1px solid "+(exc.length?"#7c3aed":"var(--border)"),
                      borderLeftWidth:exc.length?4:1,borderRadius:9,marginBottom:6,overflow:"hidden",
                      background:auj?"var(--bg-td)":"var(--card)",borderStyle:medS?"solid":"dashed"}}>
                      <div style={{display:"flex",alignItems:"center",gap:10,padding:"9px 11px",flexWrap:"wrap",
                        cursor:"pointer"}} onClick={()=>setAstSemOuv(o=>({...o,[sem.wk]:!ouvert}))}>
                        <span style={{color:"var(--txt3)",fontSize:11,width:10}}>{ouvert?"▾":"▸"}</span>
                        <span style={{fontSize:12,fontWeight:700,minWidth:130}}>{fmtJ(j0)} → {fmtJ(j9)}</span>
                        <span onClick={e=>{if(!canAst)return;e.stopPropagation();
                          setAstPickModal({dayKey:sem.wk,wKey:sem.wk,isWeek:true,label:"semaine du "+fmtJ(j0)});}}
                          style={{cursor:canAst?"pointer":"default",display:"flex",alignItems:"center",gap:6}}>
                          {medS?<>
                            <span style={{width:22,height:22,borderRadius:"50%",background:medS.color,display:"flex",
                              alignItems:"center",justifyContent:"center",color:"#fff",fontSize:9,fontWeight:800}}>{medS.init}</span>
                            <span style={{fontSize:12.5,fontWeight:700}}>{medS.prenom} {medS.nom}</span>
                          </>:<span style={{color:"var(--txt3)",fontSize:12.5}}>— non renseignée</span>}
                        </span>
                        {/* v10.26 : BANDE DES JOURS DE LA SEMAINE, a la place du compte
                            textuel « n exceptions ». Une case par jour reellement affiche
                            (les semaines de bord de periode en comptent moins de sept) :
                            initiale du jour si l'astreinte est celle de la semaine, initiales
                            du praticien sur sa couleur si le jour porte une exception. La
                            largeur ne depend donc plus du nombre d'exceptions. L'export CSV
                            et l'impression restent jour par jour, inchanges. */}
                        <span style={{marginLeft:"auto",display:"flex",alignItems:"center",gap:6}}>
                          {exc.length>0&&<span style={{display:"flex",gap:2,alignItems:"center"}}>
                            {sem.jours.map(({y,m,d})=>{
                              const dkB=y+"-"+m+"-"+d;
                              const isE=dkB!==sem.wk&&typeof astreinte[dkB]==="string";
                              const eMed=isE?medecins.find(x=>String(x.id)===String(astreinte[dkB])):null;
                              const dwB=new Date(y,m,d).getDay();
                              return <span key={dkB} title={["Dim","Lun","Mar","Mer","Jeu","Ven","Sam"][dwB]+" "+d+" "+MOIS[m]+(eMed?" — "+eMed.prenom+" "+eMed.nom:(isE?" — personne":""))}
                                style={{width:21,height:21,borderRadius:5,display:"flex",alignItems:"center",
                                  justifyContent:"center",fontSize:8.5,fontWeight:800,flexShrink:0,
                                  background:eMed?eMed.color:"var(--bg)",
                                  color:eMed?"#fff":(isE?"#7c3aed":"var(--txt3)"),
                                  border:"1px solid "+(eMed?"transparent":(isE?"#7c3aed":"var(--border2)"))}}>
                                {eMed?eMed.init:["D","L","M","M","J","V","S"][dwB]}</span>;
                            })}
                          </span>}
                          {!medS&&<span style={{fontSize:10,fontWeight:800,borderRadius:11,padding:"2px 9px",
                            background:"rgba(220,38,38,.10)",border:"1px solid #fca5a5",color:"#991b1b"}}>à remplir</span>}
                        </span>
                      </div>
                      {ouvert&&<div style={{borderTop:"1px solid var(--border)",background:"var(--bg)"}}>
                        {sem.jours.map(({y,m,d})=>{
                          const dk=y+"-"+m+"-"+d;
                          const hasExc=dk!==sem.wk&&typeof astreinte[dk]==="string";
                          const mid=astForDay2(y,m,d);
                          const med=mid?medecins.find(x=>String(x.id)===String(mid)):null;
                          const isAbsMed=med?(getEntries(med.id,y,m,d,"M").some(e=>ABS_IDS.includes(e.acteId))||getEntries(med.id,y,m,d,"JOUR").some(e=>ABS_IDS.includes(e.acteId))):false;
                          const dw2=new Date(y,m,d).getDay();
                          return <div key={dk} onClick={canAst?()=>setAstPickModal({dayKey:dk,wKey:sem.wk,isWeek:false,
                            label:["Dim","Lun","Mar","Mer","Jeu","Ven","Sam"][dw2]+" "+d+" "+MOIS[m]}):undefined}
                            style={{display:"flex",alignItems:"center",gap:10,padding:"5px 11px 5px 32px",fontSize:12,
                              borderBottom:"1px solid var(--border)",cursor:canAst?"pointer":"default",
                              background:hasExc?"rgba(124,58,237,.06)":"transparent",fontWeight:hasExc?700:400}}>
                            <span style={{width:112,color:"var(--txt2)"}}>{["Dim","Lun","Mar","Mer","Jeu","Ven","Sam"][dw2]} {d} {MOIS[m].slice(0,4).toLowerCase()}.</span>
                            {med?<>
                              <span style={{width:20,height:20,borderRadius:"50%",background:med.color,display:"flex",
                                alignItems:"center",justifyContent:"center",color:"#fff",fontSize:8.5,fontWeight:800}}>{med.init}</span>
                              <span style={{color:isAbsMed?"#ef4444":"var(--txt)"}}>{med.prenom} {med.nom}</span>
                              {isAbsMed&&<span style={{fontSize:9,color:"#ef4444",fontWeight:700}}>⚠ abs</span>}
                            </>:<span style={{color:"var(--txt3)"}}>—</span>}
                            {hasExc&&<span style={{marginLeft:"auto",fontSize:9.5,fontWeight:800,borderRadius:9,
                              padding:"1px 7px",background:"rgba(124,58,237,.14)",color:"#5b21b6"}}>exception</span>}
                          </div>;
                        })}
                      </div>}
                    </div>;
                  })}
                </div>;
              })()}
            </TableScroll>
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
                        /* v10.13 : ces deux fonds clairs étaient figés — illisibles en mode
                           sombre, où le texte reste clair. On teinte la couleur du thème,
                           comme le fait déjà la modale des gardes. */
                        background:on?"rgba(124,58,237,.16)":hasAbs?"rgba(239,68,68,.10)":"var(--bg2)",
                        cursor:(!isWeek&&absent)?"not-allowed":"pointer"}}>
                      <div style={{width:28,height:28,borderRadius:"50%",background:m.color,display:"flex",alignItems:"center",justifyContent:"center",color:"#fff",fontSize:10,fontWeight:800}}>{m.init}</div>
                      <div style={{flex:1}}>
                        <div style={{fontSize:12,fontWeight:600,color:"var(--txt)"}}>{m.prenom} {m.nom}</div>
                        {isWeek&&absDays.length>0&&<div style={{fontSize:9,color:"#ef4444",marginTop:1}}>Absent: {absDays.join(", ")}</div>}
                        {!isWeek&&absent&&<div style={{fontSize:9,color:"#ef4444",marginTop:1}}>Absent ce jour</div>}
                      </div>
                      {on&&<span style={{color:"#7c3aed",fontSize:11,flexShrink:0}}>✓</span>}
                    </button>
                  );
                })}
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

      {tab==="stats"&&(isEdit||isInterEdit)&&<StatsTab medecins={medsAff} actes={actes} plan={plan} year={year} month={month} darkMode={darkMode} setDarkMode={setDarkMode} tourMed={tourMed}/>}
      {tab==="partage"&&accessMode!=="adminEdit"&&!isMedEdit&&(
        <div style={{maxWidth:500}} className={"pset "+psetFold.map(i=>"pf"+i).join(" ")} ref={psetRef} onClick={psetClick}>
          <div data-noskip="1" style={{display:"flex",justifyContent:"flex-end",marginBottom:6}}><button onClick={()=>setDarkMode(d=>!d)} style={{...S.arr,fontSize:13,width:30}}>{darkMode?"☀️":"🌓"}</button></div>
          <div data-noskip="1"><SetQuick items={psetItems} replies={psetFold} onTout={psetTout}/></div>
          <h2 style={{...S.mTit,marginBottom:16}}>⚙️ Paramètres <span style={{fontSize:10,color:"var(--txt3)",fontWeight:400,marginLeft:8}}>{APP_VERSION}</span></h2>

          <div style={{...S.card,marginBottom:10}}>
            <div style={{fontWeight:700,color:"#3fb950",fontSize:13,marginBottom:6}}>👁 Lecture seule<div style={{display:"flex",gap:4,alignItems:"center",marginLeft:"auto"}}><button onClick={()=>setDarkMode(d=>!d)} style={{...S.arr,fontSize:13,width:30}}>{darkMode?"☀️":"🌓"}</button></div></div>
            <div style={{fontSize:11,color:"var(--txt3)"}}>Partagez l'URL directement. Sans PIN, le planning est consultable mais non modifiable.</div>
          </div>

                    {isEdit&&<div style={{...S.card,marginBottom:10}}>
            <div style={{fontWeight:700,color:"#388bfd",fontSize:13,marginBottom:6}}>🔐 Code PIN éditeur</div>
            <div style={{display:"flex",flexDirection:"column",gap:6}}>
              <input type="password" id="pinOld" placeholder="Ancien PIN" style={{...S.fi,textAlign:"center",letterSpacing:4}}/>
              <input type="password" id="pinN1" placeholder="Nouveau PIN (min 4 car.)" style={{...S.fi,textAlign:"center",letterSpacing:4}}/>
              <input type="password" id="pinN2" placeholder="Confirmer le nouveau PIN" style={{...S.fi,textAlign:"center",letterSpacing:4}}/>
              <button style={S.btnP} onClick={()=>{const o=document.getElementById("pinOld").value;const a=document.getElementById("pinN1").value;const b=document.getElementById("pinN2").value;if(o!==editPin){toast("Ancien PIN incorrect","warn");}else if(a.length<4){toast("Min 4 car.","warn");}else if(a!==b){toast("Les deux nouveaux PIN ne correspondent pas","warn");}else{setEditPin(a);["pinOld","pinN1","pinN2"].forEach(x=>{document.getElementById(x).value="";});toast("PIN mis à jour");}}}>Changer le PIN</button>
            </div>
          </div>}

          {isEdit&&<div style={{...S.card,marginBottom:10}}>
            <div style={{fontWeight:700,color:"#7c3aed",fontSize:13,marginBottom:6}}>🗝 Rôles secrétaires et cadres</div>
            <div style={{fontSize:11,color:"var(--txt3)",marginBottom:8}}>PIN secrétaires (partagé) : à la connexion, chaque personne saisit son prénom (mémorisé sur son appareil). Le rôle peut poser, modifier et retirer les activités cochées « ✏️ secrétaires » sur la ligne de n'importe quel médecin.</div>
            <div style={{display:"flex",gap:8,marginBottom:8}}>
              <input type="password" id="nap" placeholder={adminPin?"PIN défini — nouveau PIN":"Définir le PIN"} style={{...S.fi,flex:1,textAlign:"center",letterSpacing:4}}/>
              <button style={S.btnP} onClick={()=>{const v=document.getElementById("nap").value;if(v.length>=4){setAdminPin(v);toast("PIN administratif mis à jour");}else toast("Min 4 car.","warn");}}>OK</button>
            </div>
            <div style={{fontSize:10,color:"var(--txt3)",margin:"2px 0 4px"}}>PIN cadre : suit sa propre coche « ✏️ cadres » sur chaque activité, plus la gestion du planning IDE (PT cardio) et les départs différés.</div>
            <div style={{display:"flex",gap:8,marginBottom:8}}>
              <input type="password" id="ncp" placeholder={cadrePin?"PIN cadre défini — nouveau PIN":"Définir le PIN cadre"} style={{...S.fi,flex:1,textAlign:"center",letterSpacing:4}}/>
              <button style={S.btnP} onClick={()=>{const v=document.getElementById("ncp").value;if(v.length>=4){if(v===adminPin||v===editPin){toast("Ce PIN est déjà utilisé par un autre rôle","warn");return;}setCadrePin(v);toast("PIN cadre mis à jour");}else toast("Min 4 car.","warn");}}>OK</button>
            </div>
            <div style={{display:"flex",flexDirection:"column",gap:5,marginBottom:8}}>
              <label style={{display:"flex",gap:8,alignItems:"center",fontSize:12,color:"var(--txt2)",cursor:"pointer"}}><input type="checkbox" checked={adminEnabled} onChange={e=>setAdminEnabled(e.target.checked)} style={{width:14,height:14}}/>Rôle activé (décocher suspend l'accès sans changer le PIN)</label>
              <label style={{display:"flex",gap:8,alignItems:"center",fontSize:12,color:"var(--txt2)",cursor:"pointer"}}><input type="checkbox" checked={adminCanReports} onChange={e=>setAdminCanReports(e.target.checked)} style={{width:14,height:14}}/>Peut remplir les semaines blanches (onglet Reports)</label>
              <label style={{display:"flex",gap:8,alignItems:"center",fontSize:12,color:"var(--txt2)",cursor:"pointer"}}><input type="checkbox" checked={adminCanNotes} onChange={e=>setAdminCanNotes(e.target.checked)} style={{width:14,height:14}}/>Peut ajouter des notes 📝 sur les cases</label>
            </div>
            {[["Activités ouvertes aux secrétaires","adminOk","secrétaires"],["Activités ouvertes aux cadres","cadreOk","cadres"]].map(([tit,key,rl])=>(
              <React.Fragment key={key}>
                <div style={{fontSize:10,fontWeight:800,color:"var(--txt3)",textTransform:"uppercase",letterSpacing:.4,marginBottom:4}}>{tit}</div>
                <div style={{display:"flex",flexWrap:"wrap",gap:4,marginBottom:4}}>
                  {actes.filter(a=>a[key]===true).map(a=><span key={a.id} style={{padding:"1px 7px",borderRadius:5,fontSize:9,fontWeight:800,fontFamily:"'JetBrains Mono',monospace",background:a.color,color:"#111"}}>{a.short}</span>)}
                  {actes.filter(a=>a[key]===true).length===0&&<span style={{fontSize:11,color:"#b45309",fontWeight:700}}>aucune — cochez « ✏️ {rl} » sur les activités concernées</span>}
                </div>
              </React.Fragment>
            ))}
            <div style={{fontSize:9,color:"var(--txt3)"}}>⚙ Se gère dans l'onglet Activités (cases « ✏️ secrétaires » et « ✏️ cadres » de chaque activité).</div>
          </div>}

          {isEdit&&<div style={{...S.card,marginBottom:10}}>
            <div style={{fontWeight:700,color:"#e3b341",fontSize:13,marginBottom:6}}>🔐 Niveaux de droits des médecins</div>
            <div style={{fontSize:11,color:"var(--txt3)",marginBottom:8}}>Se règle dans chaque fiche ✏️ de l'onglet Équipe. Le niveau s'applique quand la personne se connecte avec son PIN personnel.<br/><b>Intermédiaire</b> : planning de tous les médecins, gardes et échanges, semaines de tour, planning type, attachés — sans Paramètres, Équipe ni Activités.</div>
            {["editeur","inter","basic"].map(lv=>{
              const list=medecins.filter(m=>((m.niveau)||"basic")===lv);
              if(list.length===0)return null;
              const lab=lv==="editeur"?"Éditeur":lv==="inter"?"Intermédiaire":"Basique";
              const col=lv==="editeur"?"#dc2626":lv==="inter"?"#b45309":"var(--txt3)";
              return <div key={lv} style={{marginBottom:5}}>
                <div style={{fontSize:9,fontWeight:800,color:col,textTransform:"uppercase",letterSpacing:.4,marginBottom:2}}>{lab}</div>
                <div style={{display:"flex",flexWrap:"wrap",gap:4}}>
                  {list.map(m=><span key={m.id} style={{padding:"1px 7px",borderRadius:5,fontSize:10,fontWeight:800,fontFamily:"'JetBrains Mono',monospace",background:"var(--bg2)",border:"1px solid var(--border)",color:"var(--txt2)"}}>{m.init}{(medPins[String(m.id)]||"").length>=3?"":" ⚠"}</span>)}
                </div>
              </div>;
            })}
            <div style={{fontSize:9,color:"var(--txt3)",marginTop:4}}>⚠ = pas encore de PIN personnel : le niveau ne s'appliquera qu'une fois le code défini.</div>
          </div>}

          {isEdit&&<div style={{...S.card,marginBottom:10}}>
            <div style={{fontWeight:700,color:"#e3b341",fontSize:13,marginBottom:6}}>👁 Récupération des codes PIN</div>
            {!showPins
              ?(!pinsAsk
                ?<button style={S.btnP} onClick={()=>{setPinsTry("");setPinsAsk(true);}}>Afficher tous les codes</button>
                :<div style={{display:"flex",gap:6,alignItems:"center",flexWrap:"wrap"}}>
                  <input autoFocus type="password" value={pinsTry} onChange={e=>setPinsTry(e.target.value)} onKeyDown={e=>{if(e.key==="Enter")validatePins();}} placeholder="PIN éditeur" style={{...S.fi,width:140,textAlign:"center",letterSpacing:4}}/>
                  <button style={S.btnP} onClick={()=>validatePins()}>Valider</button>
                  <button style={{fontSize:11,padding:"4px 10px",borderRadius:6,border:"1px solid var(--border)",background:"var(--bg2)",color:"var(--txt2)",cursor:"pointer"}} onClick={()=>{setPinsAsk(false);setPinsTry("");}}>Annuler</button>
                </div>)
              :<div>
                <div style={{fontSize:12,color:"var(--txt)",lineHeight:1.9}}>
                  <div><b>Éditeur :</b> <span style={{fontFamily:"'JetBrains Mono',monospace"}}>{editPin}</span></div>
                  <div><b>Administratif :</b> <span style={{fontFamily:"'JetBrains Mono',monospace"}}>{adminPin||"— non défini —"}</span></div>
                  {Object.entries(medPins).filter(([,p2])=>p2&&p2.length>=3).map(([mid2,p2])=>{const m2=medecins.find(x=>String(x.id)===String(mid2));return <div key={mid2}><b>{m2?m2.init:mid2} :</b> <span style={{fontFamily:"'JetBrains Mono',monospace"}}>{p2}</span></div>;})}
                  {Object.entries(medPins).filter(([,p2])=>p2&&p2.length>=3).length===0&&<div style={{color:"var(--txt3)"}}>Aucun PIN médecin défini.</div>}
                </div>
                <button style={{...S.qBtn,marginTop:8}} onClick={()=>setShowPins(false)}>Masquer</button>
              </div>}
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
            {/* v9.84 : couleurs des surspécialités, réglables ici */}
            <div style={{marginTop:12,paddingTop:10,borderTop:"1px solid var(--border)"}}>
              <div style={{fontSize:11,color:"var(--txt2)",fontWeight:700,marginBottom:6}}>🎨 Couleurs des surspécialités</div>
              <div style={{display:"flex",flexWrap:"wrap",gap:10,alignItems:"center"}}>
                {SPEC_LIST.map(([k2,lb2])=>{
                  const cur=(specColors&&specColors[k2])||SPEC_COLORS_DEF[k2];
                  return(
                    <div key={k2} style={{display:"flex",alignItems:"center",gap:5}}>
                      <input type="color" value={cur} onChange={e=>{const v=e.target.value;setSpecColors(p=>({...p,[k2]:v}));}}
                        style={{width:30,height:26,padding:0,border:"1px solid var(--border)",borderRadius:5,background:"transparent",cursor:"pointer"}}/>
                      <span style={{fontSize:12,fontWeight:800,color:cur}}>{lb2}</span>
                    </div>);
                })}
              </div>
              <div style={{fontSize:9,color:"var(--txt3)",marginTop:5}}>Utilisées dans la distribution du tour (tuile 2 de Construire) pour la surspécialité de chaque praticien et le décompte des disponibles.</div>
            </div>
          </div>}

          <InternesTile intCfg={intCfg} setIntCfg={setIntCfg} actes={actes} pins={[editPin,adminPin,cadrePin]}/>
          <div style={{...S.card,marginBottom:10}}>
            {/* Vacances scolaires */}
            <div style={{...S.card,marginBottom:10}}>
              <div style={{fontWeight:700,fontSize:13,color:"var(--txt)",marginBottom:8}}>🏖 Vacances scolaires</div>
              <div style={{fontSize:12,color:"var(--txt2)",marginBottom:10}}>
                Saisies ici, elles grisent les jours concernés dans tous les onglets. Elles ne sont plus téléchargées :
                une donnée qui arrive après l'affichage rendrait les bornes de période changeantes.
              </div>
              {(()=>{
                const der=vacs.filter(v=>v.d2).map(v=>v.d2).sort().slice(-1)[0]||null;
                const proche=der?((new Date(der+"T00:00:00")-new Date())/86400000)<183:true;
                if(!proche)return null;
                return <div style={{background:"#fffbeb",border:"1px solid #fcd34d",borderRadius:8,padding:"9px 11px",fontSize:12,color:"#78350f",marginBottom:10}}>
                  {der?<>Vos dates couvrent jusqu'au <b>{fmtLong(der)}</b>. Au-delà, l'application ne connaît plus les vacances — pensez à saisir l'année suivante.</>
                     :<>Aucune date saisie. La règle d'extension et le grisé des vacances sont sans effet tant que la liste est vide.</>}
                </div>;
              })()}
              <label style={{display:"flex",alignItems:"center",gap:9,fontSize:12.5,fontWeight:700,marginBottom:10,cursor:"pointer"}}>
                <input type="checkbox" checked={vacRule} onChange={e=>setVacRule(e.target.checked)} style={{width:15,height:15}}/>
                Étendre la période jusqu'à la fin des vacances
              </label>
              <div style={{fontSize:11.5,color:"var(--txt2)",marginBottom:10,lineHeight:1.5}}>
                Quand la fin d'une période tombe au milieu de vacances, elle est repoussée à leur dernier jour et la
                période suivante démarre le lendemain. Limité à 3 semaines, pour que les grandes vacances n'absorbent pas août.
              </div>
              {(()=>{
                const p0=perStart(year,month);const out=[];let cy=p0.sy,cm=p0.sm;
                for(let i=0;i<3;i++){
                  const pv=perPrev(cy,cm);const a=new Date(perEnd(pv.sy,pv.sm));a.setDate(a.getDate()+1);
                  const b=perEnd(cy,cm);
                  out.push(<div key={i} style={{marginBottom:5}}>
                    <b>{MOIS[cm]} {cy}</b> — du {fmtLongD(a)} au {fmtLongD(b)}
                  </div>);
                  const nx=perNext(cy,cm);cy=nx.sy;cm=nx.sm;
                }
                return <div style={{background:"var(--bg2)",border:"1px solid var(--border)",borderRadius:8,padding:"9px 11px",fontSize:11.5,marginBottom:12}}>
                  <div style={{fontSize:10,fontWeight:800,color:"var(--txt3)",textTransform:"uppercase",marginBottom:5}}>Aperçu</div>
                  {out}
                </div>;
              })()}
              {isEdit&&<>
                <div style={{display:"flex",gap:6,flexWrap:"wrap",marginBottom:10}}>
                  <button onClick={()=>setModal("vacColler")} style={{...S.icnBtn,width:"auto",padding:"6px 11px",fontSize:11.5,fontWeight:800}}>📋 Coller un calendrier</button>
                  <a href="https://www.education.gouv.fr/calendrier-scolaire" target="_blank" rel="noopener"
                    style={{...S.icnBtn,width:"auto",padding:"6px 11px",fontSize:11.5,fontWeight:800,textDecoration:"none",display:"inline-flex",alignItems:"center"}}>🔗 Calendrier officiel</a>
                  <button onClick={()=>{
                    const an=vacAnSuivante(vacs);
                    setVacs(v=>v.concat(VAC_NOMS.map(n2=>({an,nom:n2,d1:"",d2:""}))));
                  }} style={{...S.icnBtn,width:"auto",padding:"6px 11px",fontSize:11.5,fontWeight:800}}>+ Année {vacAnSuivante(vacs)}</button>
                </div>
              </>}
              {isEdit&&vacGroupes(vacs).some(([an])=>vacTerminee(an))&&
                <button onClick={()=>{
                  const fin=vacGroupes(vacs).filter(([an])=>vacTerminee(an)).map(([an])=>an);
                  if(window.confirm("Supprimer "+fin.length+" année(s) scolaire(s) terminée(s) ?\n\n"+fin.join(", ")+"\n\nLes activités du planning ne sont pas touchées ; seules les bornes des périodes déjà écoulées peuvent se décaler de quelques jours."))
                    setVacs(l=>l.filter(v=>!vacTerminee(v.an)));
                }} style={{...S.icnBtn,width:"auto",padding:"5px 10px",fontSize:11,fontWeight:800,marginBottom:10}}>
                  🗑 Supprimer les années terminées
                </button>}
              {vacGroupes(vacs).map(([an,lignes])=>(
                <div key={an} style={{marginBottom:12}}>
                  {/* v10.20 : une année terminée est repliée — la liste reste courte au fil des
                      ans sans que rien ne soit supprimé à votre insu. */}
                  <div onClick={()=>setVacOuv(o=>({...o,[an]:!vacOuvert(o,an)}))}
                    style={{fontSize:11,fontWeight:800,color:"var(--txt2)",marginBottom:4,cursor:"pointer",userSelect:"none"}}>
                    {vacOuvert(vacOuv,an)?"▾":"▸"} Année scolaire {an}
                    {vacTerminee(an)&&<span style={{fontWeight:600,color:"var(--txt3)"}}> — terminée</span>}
                  </div>
                  {vacOuvert(vacOuv,an)&&
                  /* v10.23 : cadre complet a coins arrondis, comme l'encart Apercu.
                     Les td ont un fond blanc (regle globale) : sans ce cadre, les lignes
                     paraissaient ouvertes a droite et a gauche. */
                  <div style={{border:"1px solid var(--border)",borderRadius:8,overflow:"hidden"}}>
                  <table style={{width:"100%",borderCollapse:"collapse",fontSize:12}}>
                    <tbody>
                    {lignes.map(({v,idx},i9)=>(
                      <tr key={idx}>
                        <td style={{padding:"3px 6px",borderBottom:i9===lignes.length-1?"none":"1px solid var(--border)",width:88,fontWeight:700}}>{v.nom}</td>
                        <td style={{padding:"3px 6px",borderBottom:i9===lignes.length-1?"none":"1px solid var(--border)"}}>
                          <input type="date" value={v.d1||""} disabled={!isEdit}
                            onChange={e=>setVacs(l=>l.map((x,i)=>i===idx?{...x,d1:e.target.value}:x))}
                            style={{...S.fi,fontSize:11.5,padding:"3px 6px",width:"100%",maxWidth:150}}/>
                        </td>
                        <td style={{padding:"3px 6px",borderBottom:i9===lignes.length-1?"none":"1px solid var(--border)"}}>
                          <input type="date" value={v.d2||""} disabled={!isEdit}
                            onChange={e=>setVacs(l=>l.map((x,i)=>i===idx?{...x,d2:e.target.value}:x))}
                            style={{...S.fi,fontSize:11.5,padding:"3px 6px",width:"100%",maxWidth:150}}/>
                        </td>
                        {isEdit&&<td style={{padding:"3px 6px",borderBottom:i9===lignes.length-1?"none":"1px solid var(--border)",width:22}}>
                          <span title={"Supprimer la ligne "+v.nom+" — à ne faire que pour corriger une saisie : les vacances passées servent à calculer les bornes des périodes passées"} onClick={()=>{if(window.confirm("Supprimer « "+v.nom+" "+v.an+" » ?\n\nLes vacances passées servent à calculer les bornes des périodes déjà écoulées."))setVacs(l=>l.filter((x,i)=>i!==idx));}} style={{color:"#dc2626",cursor:"pointer",fontWeight:800}}>✕</span>
                        </td>}
                      </tr>
                    ))}
                    </tbody>
                  </table></div>}
                </div>
              ))}
              {vacs.length===0&&<div style={{fontSize:11.5,color:"var(--txt3)"}}>Aucune vacance saisie.</div>}
            </div>

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
                <button onClick={()=>{try{localStorage.removeItem("cp6_theme");}catch(e){};const mm=window.matchMedia&&window.matchMedia("(prefers-color-scheme: dark)");setDarkModeRaw(!!(mm&&mm.matches));}}
                  style={{fontSize:11,padding:"4px 12px",borderRadius:6,border:"1.5px solid #7c3aed",background:"rgba(124,58,237,.10)",color:"#7c3aed",fontWeight:800,cursor:"pointer"}}>📱 Auto (téléphone)</button>
                <button onClick={()=>setDarkMode(false)} style={{fontSize:11,padding:"4px 12px",borderRadius:6,border:"1px solid var(--border)",background:!darkMode?"var(--nav-act)":"var(--bg2)",color:!darkMode?"var(--nav-act-c)":"var(--txt2)",fontWeight:700,cursor:"pointer"}}>☀️ Jour</button>
                <button onClick={()=>setDarkMode(true)} style={{fontSize:11,padding:"4px 12px",borderRadius:6,border:"1px solid var(--border)",background:darkMode?"var(--nav-act)":"var(--bg2)",color:darkMode?"var(--nav-act-c)":"var(--txt2)",fontWeight:700,cursor:"pointer"}}>🌓 Nuit</button>
              </div>
              <div style={{fontSize:10,color:"var(--txt3)",marginTop:4}}>Auto : suit le réglage clair/sombre du téléphone, en direct (y compris s'il bascule au coucher du soleil). Jour/Nuit : choix mémorisé sur cet appareil (le bouton 🌓 des onglets fait pareil).</div>
            </div>

            <div style={{fontWeight:700,color:"#e3b341",fontSize:13,marginBottom:6}}>💾 Sauvegarde & archivage</div>
            <div style={{fontSize:11,color:"var(--txt3)",marginBottom:12}}>
              Tout ce qui protège vos données, regroupé ici : leur poids, la sauvegarde quotidienne, la copie sur votre ordinateur et l'archivage des anciens mois.
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
                {docDet&&(()=>{ /* v10.101 : le détail du poids, par famille de données */
                  const EQ="Équipe & internes",AC="Activités & salles",TO="Tour médical",SO="Souhaits ⭐🚫",AS="Astreinte",RE="Reports";
                  const FAMN={planV2:"Cases du planning",plan:"Cases (ancien format)",planningTypeV2:"Planning type",planningType:"Planning type",medecinsV2:EQ,medecinsV2Order:EQ,medecins:EQ,intCfg:EQ,medPins:EQ,actesV2:AC,actesV2Order:AC,actes:AC,salleReg:AC,tourMed:TO,tourDerog:TO,tourMins:TO,tourMinsHard:TO,tourCfg:TO,tourReport:TO,tourWish:SO,tourAvoid:SO,gardeWish:SO,gardeAvoid:SO,astreinte:AS,astReport:AS,notes:"Notes",build:"Construire",csRep:RE,csBlanches:RE,csActsSel:RE,csActsGlobal:RE,journal:"Journal"};
                  const g={};Object.keys(docDet).forEach(k=>{const f=FAMN[k]||"Réglages divers";g[f]=(g[f]||0)+docDet[k];});
                  const rows=Object.keys(g).map(f=>({f,b:g[f]})).sort((a,b)=>b.b-a.b);
                  return <div style={{marginTop:6,display:"flex",flexWrap:"wrap",gap:4}}>
                    {rows.map(r=><span key={r.f} style={{fontSize:9,fontWeight:700,padding:"1px 6px",borderRadius:9,border:"1px solid var(--border)",background:"var(--bg)",color:"var(--txt2)"}}>{r.f} {r.b<1024?"<1":(r.b/1024).toFixed(r.b<10240?1:0)} Ko</span>)}
                  </div>;
                })()}
                <div style={{fontSize:10,color:"var(--txt3)",marginTop:4}}>Limite Firebase : 1 Mo par document. {pct<60?"Large marge.":pct<85?"À surveiller — un archivage des anciens mois sera à prévoir.":"⚠ Proche de la limite : archivez les anciens mois rapidement."}</div>
              </div>);
            })()}
            <div style={{marginBottom:14,padding:10,borderRadius:8,border:"1px solid var(--border)",background:"var(--bg2)"}}>
              <div style={{fontSize:11,fontWeight:700,color:"var(--txt2)",marginBottom:4}}>🕐 Sauvegardes automatiques (une par jour, 45 conservées)</div>
              <div style={{fontSize:10,color:"var(--txt3)",marginBottom:8}}>Restaurer écrase les données actuelles par celles de la sauvegarde choisie.</div>
              <div style={{display:"flex",flexDirection:"column",gap:4,marginBottom:8}}>
                {backupList.length===0&&<span style={{fontSize:11,color:"var(--txt3)"}}>Aucune sauvegarde pour l'instant.</span>}
                {/* v10.0 : avec 45 sauvegardes, une liste à plat devient illisible. On la
                    replie sur les 5 plus récentes, le reste derrière un menu déroulant. */}
                {backupList.length>5&&<select value="" onChange={e=>{if(e.target.value)setBkOpen(e.target.value);}}
                  style={{...S.fi,width:"100%",marginBottom:6,fontSize:11}}>
                  <option value="">📜 {backupList.length-5} sauvegardes plus anciennes…</option>
                  {backupList.slice(5).map(b=>(
                    <option key={b.id} value={b.id}>{new Date(b.ts).toLocaleString("fr-FR",{weekday:"short",day:"2-digit",month:"short",hour:"2-digit",minute:"2-digit"})}</option>))}
                </select>}
                {backupList.filter(b=>backupList.indexOf(b)<5||b.id===bkOpen).map(b=>(
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
            {isEdit&&<ExportCard per={expPer} setPer={setExpPer} source={expSrc} setSource={setExpSrc}
              backups={backupList} seuil={expSeuil} setSeuil={setExpSeuil} dernier={expLast} onExport={doExport} occupe={expBusy}/>}
            <div style={{marginBottom:14,padding:10,borderRadius:8,border:"1px solid var(--border)",background:"var(--bg2)"}}>
            <div style={{fontSize:11,fontWeight:700,color:"var(--txt2)",marginBottom:6}}>📂 Importer</div>
            <div style={{fontSize:10,color:"var(--txt3)",marginBottom:6}}>📂 Importer relit un fichier de données (.json) et remet tout en place.</div>
            <div style={{display:"flex",gap:8,flexWrap:"wrap"}}>
              
              {isEdit&&<button style={{...S.btnP,background:"#7c3aed"}} onClick={()=>{
                /* v10.103 : champ ATTACHÉ au document (sinon Safari iOS peut le jeter avant
                   son onchange) et confirmation rendue DANS la page (confirm() peut être
                   muet en mode écran d'accueil : il répond non sans s'afficher). */
                const input=document.createElement("input");
                input.type="file";input.accept=".json";
                input.style.position="fixed";input.style.left="-9999px";input.style.top="0";
                document.body.appendChild(input);
                const fini=()=>{try{document.body.removeChild(input);}catch(e2){}};
                input.onchange=e=>{
                  const file=e.target.files[0];if(!file){fini();return;}
                  const reader=new FileReader();
                  reader.onload=ev=>{
                    fini();
                    try{
                      const data=JSON.parse(ev.target.result);
                      if(!data.version)throw new Error("Fichier invalide");
                      const d=new Date(data.exportDate).toLocaleDateString("fr-FR");
                      setImpWait({data:data,ds:d});
                    }catch(err){setImpWait(null);toast("Fichier invalide","warn");}
                  };
                  reader.readAsText(file);
                };
                input.click();
              }}>📂 Importer</button>}
            </div>
            {impWait&&<div style={{marginTop:8,padding:10,borderRadius:8,border:"1px solid #f87171",background:"var(--bg2)"}}>
              <div style={{fontSize:11,fontWeight:700,marginBottom:6}}>Restaurer la sauvegarde du {impWait.ds} ?</div>
              <div style={{fontSize:10,color:"var(--txt3)",marginBottom:8}}>Toutes les données actuelles seront remplacées par celles du fichier.</div>
              <div style={{display:"flex",gap:8}}>
                <button style={{...S.btnP,background:"#dc2626"}} onClick={()=>{
                  const data=impWait.data;
                  if(data.plan)setPlan(data.plan);
                  if(data.tourMed)setTourMed(data.tourMed);
                  if(data.planningType)setPlanningType(data.planningType);
                  if(data.notes)setNotes(data.notes);
                  if(data.medecins)setMedecins(data.medecins);
                  if(data.actes)setActes(data.actes);
                  if(data.tourDerog)setTourDerog(data.tourDerog);
                  if(data.salleReg)setSalleReg(data.salleReg);
                  setImpWait(null);toast("Sauvegarde restaurée");
                }}>↩ Restaurer</button>
                <button style={{...S.btnP,background:"var(--bg3)",color:"var(--txt2)"}} onClick={()=>setImpWait(null)}>✕ Annuler</button>
              </div>
            </div>}
            </div>
            {isEdit&&<div style={{marginBottom:14,padding:10,borderRadius:8,border:"1px solid var(--border)",background:"var(--bg2)"}}>
                <div style={{fontSize:11,fontWeight:700,color:"var(--txt2)",marginBottom:6}}>🔓 Périodes closes</div>
                <div style={{fontSize:10,color:"var(--txt2)",marginBottom:6}}>Tout ce qui précède le premier jour de la période en cours est en <b>lecture seule, pour tout le monde</b> — vous compris. Vous pouvez lever le verrou le temps d'une correction : il se remet en place tout seul au prochain chargement de l'application, et rien n'est enregistré.</div>
                <label style={{display:"flex",alignItems:"center",gap:7,fontSize:11,fontWeight:700,color:vUnlock?"#b45309":"var(--txt2)",cursor:"pointer"}}>
                  <input type="checkbox" checked={vUnlock} onChange={e=>{const v=e.target.checked;setVUnlock(v);toast(v?"⚠ Périodes closes déverrouillées jusqu'au rechargement":"🔒 Périodes closes de nouveau verrouillées",v?"warn":"info");}}/>
                  Autoriser la modification des périodes closes
                </label>
                {vUnlock&&<div style={{marginTop:6,fontSize:10,color:"#b45309",padding:"4px 7px",borderRadius:6,border:"1px solid #f59e0b",background:"rgba(245,158,11,.10)"}}>⚠ Verrou levé sur cet appareil et pour cette session seulement. Chaque modification faite sur une période close vous sera signalée.</div>}
              </div>}
            {isEdit&&(()=>{
              const vDeb=verrouDebut();
              /* « archivable » = période ENTIÈREMENT CLOSE — la même borne que le verrou,
                 quelle que soit la période affichée (durcissement v10.110). */
              const perCmp=(a,b)=>{const x=a.split("-"),y2=b.split("-");return (+x[0]-+y2[0])||(+x[1]-+y2[1]);};
              const perLib=(pid)=>{const a=pid.split("-");return perLibelle(+a[0],+a[1]);};
              const perSet={};
              Object.keys(plan).forEach(k=>{const pid=arPerClair(k);if(pid)perSet[pid]=1;});
              const persInPlan=Object.keys(perSet).filter(pid=>{
                const a=pid.split("-");const l=perDaysList(+a[0],+a[1]);
                return l.length>0&&dKey(l[l.length-1].y,l[l.length-1].m,l[l.length-1].d)<vDeb;
              }).sort(perCmp);
              const anx=arDecoupe({tourMed,tourDerog,notes,tourWish,tourAvoid,gardeWish,gardeAvoid,build,csRep,csBlanches},persInPlan);
              /* v10.111 : archivage période par période (sa demande) — la même mécanique,
                 paramétrée par la liste. Le découpage est recalculé AU CLIC pour être
                 annoncé dans la confirmation avant le moindre retrait. */
              const archiverPers=async(list)=>{
                const libs=list.map(perLib);
                const anxL=arDecoupe({tourMed,tourDerog,notes,tourWish,tourAvoid,gardeWish,gardeAvoid,build,csRep,csBlanches},list);
                if(!window.confirm("Archiver "+(list.length>1?"les "+list.length+" périodes closes":"la période close")+" ("+libs.join(", ")+") ?"
                  +(anxL.n>0?"\n\nPartent aussi : "+anxL.lib+".":"")
                  +"\n\nLes semestres entièrement archivés seront aussi retirés de l'onglet Équipe : internes et noms de Docteurs Juniors de ces semestres."))return;
                const okB=await makeBackup(true);
                if(!okB&&!window.confirm("⚠ La sauvegarde de sécurité a échoué. Continuer quand même ?"))return;
                const byPer={};
                Object.keys(plan).forEach(k=>{const pid=arPerClair(k);if(pid&&list.indexOf(pid)>=0){(byPer[pid]=byPer[pid]||{})[k]=plan[k];}});
                try{
                  for(const pid of list){
                    const ref=window.firebaseDB.collection("archives").doc("per-"+pid);
                    const prev=(await ref.get()).data()||{};
                    const merged=Object.assign({},prev.plan?JSON.parse(prev.plan):{},byPer[pid]||{});
                    /* les annexes de la période rejoignent le document d'archive, FUSIONNÉES
                       avec ce qui s'y trouvait déjà (une période corrigée après déverrouillage
                       peut être archivée en deux fois). */
                    const pAnx=prev.annex?JSON.parse(prev.annex):{};
                    const nAnx=anxL.parts[pid]||{};
                    const mAnx=Object.assign({},pAnx);
                    Object.keys(nAnx).forEach(ch=>{mAnx[ch]=arFusion(ch,nAnx[ch],pAnx[ch]||{});});
                    await ref.set({plan:JSON.stringify(merged),annex:JSON.stringify(mAnx),_ts:Date.now()});
                  }
                }catch(e){toast("Échec de la copie en archive — RIEN n'a été retiré","warn");return;}
                /* v10.112 : LES RETRAITS D'ABORD, LE TÉLÉCHARGEMENT EN DERNIER. Sur iPhone,
                   le téléchargement met la page en arrière-plan et iOS gèle réseau et
                   minuteries (leçon v10.106) : en v10.110/111 les suppressions, envoyées
                   par la synchronisation APRÈS le clic, ne partaient jamais — les cases
                   ressuscitaient au rechargement et la liste des périodes archivées restait
                   vide. Les retraits sont donc écrits et CONFIRMÉS ici, avant tout
                   téléchargement ; la synchronisation ne fera ensuite que les reconstater
                   (supprimer un champ déjà absent est sans effet). */
                const delPairs=[];
                Object.keys(byPer).forEach(pid=>Object.keys(byPer[pid]).forEach(k=>delPairs.push([["planV2",k],"__DELETE__"])));
                try{
                  if(PLANNING_DOC&&updatePaths)for(let i2=0;i2<delPairs.length;i2+=200)await updatePaths(PLANNING_DOC,delPairs.slice(i2,i2+200));
                }catch(e){toast("Échec du retrait des cases — les archives sont écrites, les données actives n'ont pas bougé. Réessayez.","warn");return;}
                setPlan(p=>{const n2={};Object.keys(p).forEach(k=>{const pid=arPerClair(k);if(!pid||list.indexOf(pid)<0)n2[k]=p[k];});return n2;});
                /* retrait des annexes. Toujours par UPDATER et par période, jamais en
                   reposant la valeur calculée au rendu — le serveur a pu livrer des
                   modifications entre l'affichage et le clic (leçon v10.3). */
                const okP=(pid)=>!!pid&&list.indexOf(pid)>=0;
                setTourMed(o=>arPurge(o,arPerTechSem,okP));
                setTourDerog(o=>arPurge(o,arPerClair,okP));
                setNotes(o=>arPurge(o,arPerNote,okP));
                setTourWish(o=>arPurge(o,arPerTechSem,okP));
                setTourAvoid(o=>arPurge(o,arPerTechSem,okP));
                setGardeWish(o=>arPurge(o,arPerClair,okP));
                setGardeAvoid(o=>arPurge(o,arPerClair,okP));
                setBuild(o=>arPurge(o,arPerPeriode,okP));
                setCsBlanches(o=>arPurgeMed(o,null,okP));
                setCsRep(o=>arPurgeMed(o,["done","to"],okP));
                list.forEach(pid=>{archFetched.current[pid]=true;});
                /* v10.88, sa consigne : « je ne peux pas rester avec une liste qui
                   continue ». Un semestre dont la FIN est dans les périodes archivées
                   disparaît, avec ses internes et les noms de juniors qui y sont
                   rattachés. Le dernier mois de la dernière période donne la borne. */
                const lpd=perDaysList(+list[list.length-1].split("-")[0],+list[list.length-1].split("-")[1]);
                const lastMk=arPad(lpd[lpd.length-1].y,lpd[lpd.length-1].m);
                setMedecins(l2=>l2.map(m2=>{const g=djPurgeMed(m2,intCfg,lastMk);return g?{...m2,dj:g}:m2;}));
                setIntCfg(p3=>({...p3,sems:(((p3&&p3.sems)||[]).filter(s3=>String(s3.fin||"").slice(0,7)>lastMk))}));
                setArchPlan(p2=>{const add={};Object.keys(byPer).forEach(pid=>Object.assign(add,byPer[pid]));return {...p2,...add};});
                /* les annexes RELUES rejoignent le cache de consultation tout de suite,
                   sinon le tour et les notes de la période disparaîtraient jusqu'au rechargement */
                setArchAnx(p2=>{const o={...p2};
                  Object.keys(anxL.parts).forEach(pid=>{const A=anxL.parts[pid];
                    AR_LU.forEach(ch=>{if(A[ch])o[ch]=arFusion(ch,A[ch],o[ch]||{});});});
                  return o;});
                await refreshArchList();   /* v10.112 : pastilles et badge à jour AVANT le téléchargement */
                toast("Archivage terminé : "+(list.length>1?list.length+" périodes copiées puis retirées":"1 période copiée puis retirée")+" des données actives","info");
                /* le fichier part en dernier, une fois les écritures critiques confirmées ;
                   le court délai laisse aussi partir l'enregistrement des annexes */
                const blob=new Blob([JSON.stringify({version:"arch-per-1",plan:byPer,annexes:anxL.parts},null,1)],{type:"application/json"});
                const a2=document.createElement("a");a2.href=URL.createObjectURL(blob);a2.download="archive-cardio-"+list[0]+"_"+list[list.length-1]+".json";
                setTimeout(()=>{a2.click();},800);
              };
              return(
              <div style={{marginBottom:14,padding:10,borderRadius:8,border:"1px solid var(--border)",background:"var(--bg2)"}}>
                <div style={{fontSize:11,fontWeight:700,color:"var(--txt2)",marginBottom:6}}>🗄 Archivage</div>
                {persInPlan.length===0
                  ?<div style={{fontSize:10,color:"var(--txt3)"}}>Aucune période close dans les données actives — rien à archiver pour l'instant.</div>
                  :<div>
                    <div style={{fontSize:10,color:"var(--txt2)",marginBottom:5}}>L'archivage copie dans Firebase les cases de la période <b>et ses données datées</b> (tour, notes, souhaits, reports, Construire), télécharge un fichier sur cet appareil (à conserver : c'est votre copie hors Firebase), puis les retire des données actives. Le planning, le tour et les notes restent consultables en naviguant vers la période (lecture).</div>
                    {anx.n>0&&<div style={{fontSize:10,color:"var(--txt3)",marginBottom:5,padding:"4px 7px",borderRadius:6,border:"1px dashed var(--border)"}}>Données datées qui partiraient : {anx.lib}. Une semaine suit sa période, celle de son dimanche.</div>}
                    {persInPlan.map(pid=>(
                      <div key={pid} style={{display:"flex",alignItems:"center",gap:8,marginBottom:5}}>
                        <span style={{fontSize:11,fontWeight:700,color:"var(--txt)"}}>{perLib(pid)}</span>
                        <button onClick={()=>archiverPers([pid])} style={{fontSize:11,padding:"3px 12px",borderRadius:6,border:"1.5px solid #7c3aed",background:"rgba(124,58,237,.10)",color:"#7c3aed",fontWeight:800,cursor:"pointer"}}>🗄 Archiver</button>
                      </div>
                    ))}
                    {persInPlan.length>1&&<button onClick={()=>archiverPers(persInPlan)} style={{marginTop:2,fontSize:11,padding:"4px 14px",borderRadius:6,border:"1.5px solid #7c3aed",background:"rgba(124,58,237,.18)",color:"#7c3aed",fontWeight:800,cursor:"pointer"}}>🗄 Tout archiver ({persInPlan.length} périodes)</button>}
                  </div>}
                {archivedList.length>0&&<div style={{marginTop:8,paddingTop:7,borderTop:"1px dashed var(--border)"}}>
                  <div style={{fontSize:10,fontWeight:700,color:"var(--txt2)",marginBottom:4}}>Périodes archivées ({archivedList.length}) :</div>
                  <div style={{display:"flex",flexWrap:"wrap",gap:4}}>
                    {archivedList.map(pid=>(
                      <span key={pid} style={{display:"inline-flex",alignItems:"center",gap:4,fontSize:10,fontWeight:700,padding:"3px 7px",borderRadius:12,border:"1px solid #7c3aed",background:"rgba(124,58,237,.07)",color:"#7c3aed"}}>
                        🗄 {perLib(pid)}
                        <button title="Désarchiver : remettre cette période dans les données actives" onClick={async()=>{
                            if(!window.confirm("Désarchiver la période "+perLib(pid)+" ? Elle sera remise dans les données actives, cases ET données datées (les valeurs actives existantes sont conservées en cas de doublon)."))return;
                            try{
                              const ref=window.firebaseDB.collection("archives").doc("per-"+pid);
                              const d2=(await ref.get()).data();
                              if(!d2||!d2.plan){toast("Archive introuvable","warn");return;}
                              const frag=JSON.parse(d2.plan);
                              setPlan(p=>({...frag,...p}));
                              /* le désarchivage est SYMÉTRIQUE — les annexes reviennent aussi */
                              if(d2.annex){try{const an=JSON.parse(d2.annex)||{};
                                if(an.tourMed)setTourMed(c=>arFusion("tourMed",c,an.tourMed));
                                if(an.tourDerog)setTourDerog(c=>arFusion("tourDerog",c,an.tourDerog));
                                if(an.notes)setNotes(c=>arFusion("notes",c,an.notes));
                                if(an.tourWish)setTourWish(c=>arFusion("tourWish",c,an.tourWish));
                                if(an.tourAvoid)setTourAvoid(c=>arFusion("tourAvoid",c,an.tourAvoid));
                                if(an.gardeWish)setGardeWish(c=>arFusion("gardeWish",c,an.gardeWish));
                                if(an.gardeAvoid)setGardeAvoid(c=>arFusion("gardeAvoid",c,an.gardeAvoid));
                                if(an.build)setBuild(c=>arFusion("build",c,an.build));
                                if(an.csRep)setCsRep(c=>arFusion("csRep",c,an.csRep));
                                if(an.csBlanches)setCsBlanches(c=>arFusion("csBlanches",c,an.csBlanches));
                              }catch(e3){}}
                              setArchPlan(p=>{const n2={};Object.keys(p).forEach(k=>{if(arPerClair(k)!==pid)n2[k]=p[k];});return n2;});
                              const okP2=(p2)=>p2===pid;
                              setArchAnx(p=>({tourMed:arPurge(p.tourMed,arPerTechSem,okP2),tourDerog:arPurge(p.tourDerog,arPerClair,okP2),notes:arPurge(p.notes,arPerNote,okP2)}));
                              delete archFetched.current[pid];
                              await ref.delete();
                              await refreshArchList();
                              toast("Période "+perLib(pid)+" désarchivée — de retour dans les données actives","info");
                            }catch(e){toast("Échec du désarchivage","warn");}
                          }} style={{border:"none",background:"none",cursor:"pointer",fontSize:10,padding:0,color:"#16a34a",fontWeight:900}}>↩</button>
                      </span>
                    ))}
                  </div>
                </div>}
              </div>);
            })()}
          </div>

          <div style={S.card}>
            <div style={{fontWeight:700,color:"var(--txt2)",fontSize:13,marginBottom:6}}>☁️ Synchronisation Firebase</div>
            <div style={{display:"flex",alignItems:"center",gap:8}}>
              <div style={{width:10,height:10,borderRadius:"50%",flexShrink:0,background:netOff?"#94a3b8":fbStatus==="ok"?"#4ade80":fbStatus==="error"?"#ef4444":fbStatus==="offline"?"#94a3b8":"#f59e0b"}}/>
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
            const a=(cellEs(e).find(x=>x&&EXCL_IDS.includes(x.acteId))||{}).acteId;
            if(a)blockedBy.push(a==="ABSENCE"?"absent":a==="TP"?"temps partiel":a==="GARDE"?"garde":a==="REPOS_GARDE"?"repos de garde":"formation");
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
                  <span style={{width:26,height:26,borderRadius:"50%",background:m2.color,color:"#fff",fontSize:10,fontWeight:800,display:"inline-flex",alignItems:"center",justifyContent:"center"}}>{m2.init}</span>
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

      {bipModal&&bipModalUI()}
      {histModal&&(()=>{
        const med3=djAff(medecins.find(x=>x.id===histModal.medId),dKey(histModal.y,histModal.m,histModal.d));
        return(
          <Ov onClose={()=>setHistModal(null)}>
            <div style={S.mHd}>
              <div><div style={S.mTit2}>🕘 Historique — {med3?med3.init:""} · {histModal.d} {MOIS[histModal.m]} {SLOTL[histModal.sl]||histModal.sl}</div></div>
              <button onClick={()=>setHistModal(null)} style={S.xBtn}>×</button>
            </div>
            {histModal.loading&&<div style={{fontSize:12,color:"var(--txt3)"}}>Chargement…</div>}
            {!histModal.loading&&histModal.list.length===0&&<div style={{fontSize:12,color:"var(--txt3)"}}>Aucune modification enregistrée pour cette case (le journal démarre avec la v9.9 et ne couvre que les modifications manuelles de cases).</div>}
            {!histModal.loading&&histModal.list.map((e,i)=>{
              const a3=actes.find(x=>x.id===e.act);
              const dt=new Date(e.t);
              return <div key={i} style={{display:"flex",alignItems:"center",gap:8,padding:"6px 0",borderBottom:"1px solid var(--border2)",fontSize:12}}>
                <span style={{color:"var(--txt3)",fontSize:10,minWidth:96}}>{String(dt.getDate()).padStart(2,"0")}/{String(dt.getMonth()+1).padStart(2,"0")}/{dt.getFullYear()} {String(dt.getHours()).padStart(2,"0")}:{String(dt.getMinutes()).padStart(2,"0")}</span>
                <span style={{fontWeight:800,color:e.x==="add"?"#16a34a":"#dc2626"}}>{e.x==="add"?"+ Posé":"− Retiré"}</span>
                {a3&&<span style={{padding:"0 6px",borderRadius:4,fontSize:9,fontWeight:800,fontFamily:"'JetBrains Mono',monospace",background:a3.color,color:"#111"}}>{a3.short}</span>}
                {!a3&&e.act&&<span style={{fontSize:10,color:"var(--txt2)"}}>{e.act}</span>}
                <span style={{marginLeft:"auto",color:"var(--txt2)",fontSize:11}}>{e.a}</span>
              </div>;
            })}
          </Ov>
        );
      })()}
      {modal==="cell"&&mData&&(()=>{
        const {medId,y:y2,m:m2,d:d2,slot}=mData;
        const med=djAff(medecins.find(x=>x.id===medId),dKey(y2,m2,d2));
        const we=isWE(y2,m2,d2),isNight=slot==="N",canGarde=(med&&med.garde)===true;
        const canEditThisMed=canEdit(medId);
        const dw2=dow(y2,m2,d2);
        const entries=getEntries(medId,y2,m2,d2,slot);
        const curIds=entries.filter(e=>!e._blocked&&!e._fullDay&&!e.cond).map(e=>e.acteId);
        const hasOther=curIds.some(id=>!["TOUR_HC","TOUR_USIC"].includes(id));
        /* v10.86 : le tour est SYNTHETISE a la semaine — la moindre entree reelle sur
           la case le masque (expEntries). Poser une consultation le faisait donc
           disparaitre de cette modale alors que le medecin est bien de tour. On le
           recalcule ici pour l'afficher A COTE, en lecture seule : un tour ne se
           retire pas d'une case, il s'echange. */
        const tourSy=(()=>{
          if(we||(slot!=="M"&&slot!=="AM"))return null;
          if(curIds.includes("TOUR_HC")||curIds.includes("TOUR_USIC"))return null;
          if(entries.some(e=>e&&(e._fullDay||e._blocked||EXCL_IDS.includes(e.acteId))))return null;
          const dgS=((tourDerog||{})[dKey(y2,m2,d2)]||{})[medId];
          if(dgS===true||(dgS&&dgS[slot]))return null;
          const wmS=(tourMed||{})[wKey(y2,m2,d2)]||{};
          if((wmS.HC||[]).includes(medId))return "TOUR_HC";
          if((wmS.USIC||[]).includes(medId))return "TOUR_USIC";
          return null;
        })();

        const eligible=actes.filter(a=>{
          if(isNight)return a.id==="GARDE"&&canGarde;
          if(we)return a.id==="ABSENCE"||(a.id==="GARDE"&&canGarde);
          if(SYS.includes(a.id)) return a.id==="ABSENCE";
          // Check if medecin is authorized for this activity
          if((a.medecinsAutorise&&a.medecinsAutorise.length)>0&&!(med&&a.medecinsAutorise.includes(authI(med))))return false;
          return true;
        }).filter(a=>!isAdminEdit||a[roleOkKey]===true||a.id==="ABSENCE"||a.id==="FORMATION"); // secrétaires/cadres : activités cochées ✏️ pour CE rôle + absences/formations

        const doGarde=()=>{ applyGarde(medId,y2,m2,d2); setModal(null); };
        const doAdd=(acteId,salle=null)=>{
          if(acteId==="GARDE"){doGarde();return;}
          /* v9.60 : une branche non tranchée n'est pas « déjà posée » — la reposer, c'est trancher */
          const _curA=getEntries(medId,y2,m2,d2,we?"JOUR":slot).filter(e2=>e2&&!e2.cond).map(e2=>e2.acteId);
          /* v9.67 : reposer avec une salle explicite = ATTRIBUER la salle (addEntry remplace, v9.63) */
          if(_curA.includes(acteId)&&!salle){toast("Cette activité est déjà posée sur ce créneau — retirez-la d'abord (×) si besoin","warn");return;}
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

            {(()=>{
              const cE=entries.filter(e=>e&&e.acteId&&e.cond);
              if(!cE.length)return null;
              /* v9.60 : les branches d'un choix ouvert sont posées SANS SALLE (c'est le principe).
                 Trancher depuis ici doit donc pouvoir attribuer la salle dans la foulée, et
                 surtout MONTRER avant de cliquer s'il en reste une de libre. */
              const busy={};
              actes.filter(ax=>ax.hasSalle||ax.fixedSalle).forEach(ax=>{
                const ao=salleOcc(ax.id,y2,m2,d2,slot);
                Object.keys(ao).forEach(s=>{if(!busy[s])busy[s]=[];ao[s].forEach(m=>{if(!busy[s].find(x=>x.id===m.id))busy[s].push(m);});});
              });
              const freeOf=a=>(a.salles||[]).filter(s=>!((busy[s]||[]).some(m=>m.id!==medId)));
              return(
                <div style={{marginBottom:10,padding:"7px 9px",borderRadius:8,border:"1.5px dashed "+COND_C,background:COND_BG}}>
                  <div style={{display:"flex",alignItems:"center",gap:6,marginBottom:6}}>
                    <span style={{fontSize:10,color:COND_C,fontWeight:800}}>{cE.length>1?("◇ CHOIX OUVERT — "+cE.length+" branches, non tranché"):"◇ EN ATTENTE — 1 activité, non tranchée"}</span>
                    {canEditThisMed&&<button title="Effacer tout le choix ouvert" onClick={()=>dropCond(medId,y2,m2,d2,slot,null)}
                      style={{marginLeft:"auto",background:"#fee2e2",border:"1px solid #fca5a5",borderRadius:4,color:"#dc2626",cursor:"pointer",fontSize:11,fontWeight:900,padding:"1px 6px"}}>×</button>}
                  </div>
                  {cE.map((e,i)=>{const a=acteById(e.acteId);if(!a)return null;
                    const tot=(a.salles||[]).length,fr=freeOf(a);
                    const dispo=tot===0?null:fr.length>0;
                    return(
                    <div key={i} style={{display:"flex",alignItems:"center",gap:5,marginBottom:4}}>
                      <Badge a={a} hideSalle={true}/>
                      <span style={{flex:1,fontSize:10,fontWeight:700,color:dispo===null?"var(--txt3)":dispo?"#2f9440":"#f85149"}}>
                        {dispo===null?"pas de salle":dispo?(fr.length+"/"+tot+" salle"+(tot>1?"s":"")+" libre"+(fr.length>1?"s":"")+" : "+fr.join(", ")):"aucune salle libre"}
                      </span>
                      {canEditThisMed&&<button onClick={()=>{
                          if(a.fixedSalle){doAdd(a.id,a.fixedSalle);return;}
                          if(tot>0){setMData(p=>({...p,_pickSalle:a.id}));return;}
                          settleCond(medId,y2,m2,d2,slot,a.id);
                        }}
                        style={{background:"transparent",border:"1px solid "+COND_C,color:COND_C,borderRadius:5,cursor:"pointer",fontSize:10,fontWeight:800,padding:"3px 8px",whiteSpace:"nowrap"}}>{tot>0&&!a.fixedSalle?"Choisir la salle…":"✓ c'est celle-ci"}</button>}
                      {canEditThisMed&&<button title="Retirer cette branche" onClick={()=>dropCond(medId,y2,m2,d2,slot,a.id)}
                        style={{background:"#fee2e2",border:"1px solid #fca5a5",borderRadius:4,color:"#dc2626",cursor:"pointer",fontSize:11,fontWeight:900,padding:"1px 6px"}}>×</button>}
                    </div>);})}
                  <div style={{fontSize:10,color:"var(--txt3)",lineHeight:1.45}}>{cE.length>1?"Attribuer une salle depuis un onglet de salles tranche aussi le choix.":"Tant qu'elle n'est pas tranchée, cette activité n'occupe aucune salle et reste à confirmer."}</div>
                </div>);
            })()}
            {(()=>{
              const wE=entries.filter(e=>e&&e.acteId&&!e.cond&&e.wasCond&&e.wasCond.length);
              if(!wE.length)return null;
              return wE.map((e,i)=>{const a=acteById(e.acteId);if(!a)return null;
                const lab=e.wasCond.map(id=>{const x=acteById(id);return x?x.short:id;}).join(" ou ");
                return(
                  <div key={"w"+i} style={{marginBottom:10,display:"flex",alignItems:"center",gap:6,padding:"6px 9px",borderRadius:8,border:"1px solid "+COND_C,background:COND_BG}}>
                    <span style={{fontSize:10,color:COND_C,fontWeight:700,flex:1,lineHeight:1.4}}>◇ {a.short} est issue d'un choix ouvert entre {lab}</span>
                    {canEditThisMed&&<button onClick={()=>restoreCond(medId,y2,m2,d2,slot,e.acteId)}
                      style={{background:"transparent",border:"1px solid "+COND_C,color:COND_C,borderRadius:5,cursor:"pointer",fontSize:10,fontWeight:800,padding:"3px 8px",whiteSpace:"nowrap"}}>↩ rétablir</button>}
                  </div>);});
            })()}
            {(curIds.length>0||tourSy)&&(
              <div style={{marginBottom:10}}>
                <div style={{fontSize:10,color:"var(--txt3)",fontWeight:700,textTransform:"uppercase",marginBottom:5}}>Activités</div>
                <div style={{display:"flex",flexWrap:"wrap",gap:4}}>
                  {tourSy&&(()=>{const aT=acteById(tourSy);if(!aT)return null;
                    return(<div style={{display:"flex",alignItems:"center",gap:4}} title="Tour médical de la semaine — il ne se retire pas ici, il s'échange">
                      {/* v10.96 : mention textuelle retirée à sa demande du 19/08 —
                         il voulait seulement que la tuile HC/USIC se maintienne à côté
                         de l'activité posée, l'infobulle suffit pour le reste. */}
                      <Badge a={aT} hideSalle={true}/>
                    </div>);})()}
                  {entries.filter(e=>e.acteId&&!e.cond).map((e,i)=>{
                    const a=acteById(e.acteId);if(!a)return null;
                    return(
                      <div key={i} style={{display:"flex",alignItems:"center",gap:3}}>
                        <Badge a={a} hideSalle={true}/>
                        {e.salle&&<span style={{fontSize:11,fontWeight:800,fontFamily:"'JetBrains Mono',monospace",color:"var(--txt)",border:"1px solid var(--border)",background:"var(--bg2)",borderRadius:4,padding:"3px 7px",whiteSpace:"nowrap"}}>{e.salle}</span>}
                        {a.hasSalle&&!e.salle&&(()=>{
                          /* v9.67 : option A — disponibilité affichée et attribution sur place,
                             via le sélecteur _pickSalle ; doAdd remplace la ferme (v9.63). */
                          const busy={};
                          actes.filter(ax=>ax.hasSalle||ax.fixedSalle).forEach(ax=>{
                            const ao=salleOcc(ax.id,y2,m2,d2,slot);
                            Object.keys(ao).forEach(s2=>{if(!busy[s2])busy[s2]=[];ao[s2].forEach(mm=>{if(!busy[s2].find(x=>x.id===mm.id))busy[s2].push(mm);});});
                          });
                          const fr=(a.salles||[]).filter(s2=>!((busy[s2]||[]).some(mm=>mm.id!==medId)));
                          const tot=(a.salles||[]).length;
                          return(<>
                            <span style={{fontSize:11,fontWeight:800,fontFamily:"'JetBrains Mono',monospace",color:"#f85149",border:"1px solid rgba(248,81,73,.5)",background:"rgba(248,81,73,.10)",borderRadius:4,padding:"3px 7px",whiteSpace:"nowrap"}}>sans salle</span>
                            {tot>0&&<span style={{fontSize:10,fontWeight:700,color:fr.length?"#2f9440":"#f85149"}}>{fr.length?fr.length+"/"+tot+" libre"+(fr.length>1?"s":"")+" : "+fr.join(", "):"aucune salle libre"}</span>}
                            {canEditThisMed&&tot>0&&(!isAdminEdit||a[roleOkKey]===true)&&<button onClick={()=>setMData(p=>({...p,_pickSalle:a.id}))}
                              style={{background:"transparent",border:"1px solid var(--border)",color:"var(--txt2)",borderRadius:5,cursor:"pointer",fontSize:10,fontWeight:800,padding:"3px 8px",whiteSpace:"nowrap"}}>Choisir la salle…</button>}
                          </>);
                        })()}
                        {/* v10.86 : un tour ne se retire pas d'une case (il s'echange) — pas de croix */}
                        {canEditThisMed&&["TOUR_HC","TOUR_USIC"].indexOf(a.id)<0&&(!isAdminEdit||a[roleOkKey]===true||a.acteId==="ABSENCE"||a.id==="ABSENCE"||a.id==="FORMATION")&&<button onClick={()=>{
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

            {/* v10.75 : une absence qui court sur plusieurs jours se retire d'un geste —
                jusqu'a la fin, ou en entier si on a clique au milieu. Le reperage lit M,
                AM ET JOUR (lecon v9.65.1) et enjambe week-ends et feries (sa regle). */}
            {canEditThisMed&&(()=>{
              const absE=entries.find(e=>e&&!e.cond&&(e.acteId==="ABSENCE"||e.acteId==="FORMATION"));
              if(!absE)return null;
              const aid=absE.acteId;
              const aSlot=(yy,mm,dd,sl)=>getEntries(medId,yy,mm,dd,sl).some(x=>x&&!x.cond&&x.acteId===aid);
              const aJour=(yy,mm,dd)=>["JOUR","M","AM"].some(sl=>aSlot(yy,mm,dd,sl));
              const bal=(sens)=>{let cur=new Date(y2,m2,d2),last=new Date(y2,m2,d2);
                for(let i=0;i<400;i++){
                  cur=new Date(cur.getFullYear(),cur.getMonth(),cur.getDate()+sens);
                  const yy=cur.getFullYear(),mm=cur.getMonth(),dd=cur.getDate();
                  if(aJour(yy,mm,dd)){last=new Date(yy,mm,dd);continue;}
                  if(isWE(yy,mm,dd))continue;   /* week-end ou ferie sans absence : on enjambe */
                  break;}
                return last;};
              const dDeb=bal(-1),dFin=bal(1);
              const nJours=Math.round((dFin.getTime()-dDeb.getTime())/86400000)+1;
              if(nJours<=1)return null;
              const iso=t=>`${t.getFullYear()}-${String(t.getMonth()+1).padStart(2,"0")}-${String(t.getDate()).padStart(2,"0")}`;
              const court=t=>`${String(t.getDate()).padStart(2,"0")}/${String(t.getMonth()+1).padStart(2,"0")}`;
              const sD=aSlot(dDeb.getFullYear(),dDeb.getMonth(),dDeb.getDate(),"M")?"M":"AM";
              const sF=aSlot(dFin.getFullYear(),dFin.getMonth(),dFin.getDate(),"AM")?"AM":"M";
              const slotC=(we||slot==="JOUR"||slot==="N")?"M":slot;
              const jClic=new Date(y2,m2,d2);
              const lab=aid==="FORMATION"?"FMC":"absence";
              const finApres=dFin.getTime()>jClic.getTime()||(slotC==="M"&&sF==="AM");
              const go=mData._absGo;
              const cible=go==="fin"?{df:iso(jClic),sd:slotC,dt:iso(dFin),sf:sF,txt:`du ${court(jClic)} au ${court(dFin)}`}
                        :go==="tout"?{df:iso(dDeb),sd:sD,dt:iso(dFin),sf:sF,txt:`du ${court(dDeb)} au ${court(dFin)}`}:null;
              const bt={background:"#fee2e2",border:"1px solid #fca5a5",color:"#dc2626",borderRadius:6,cursor:"pointer",fontSize:11,fontWeight:800,padding:"5px 9px",whiteSpace:"nowrap"};
              return(
                <div style={{marginBottom:10,padding:"8px 10px",borderRadius:8,border:"1px solid var(--border)",background:"var(--bg2)"}}>
                  <div style={{fontSize:11.5,fontWeight:800,color:"var(--txt)",lineHeight:1.45}}>
                    📅 Cette {lab} court du {court(dDeb)} au {court(dFin)} — voulez-vous la retirer ?
                    <span style={{display:"block",fontSize:10,fontWeight:600,color:"var(--txt3)",marginTop:1}}>{nJours} jours{dDeb.getTime()<jClic.getTime()&&dFin.getTime()>jClic.getTime()?" — vous avez cliqué au milieu":""}</span>
                  </div>
                  {!cible?
                    <div style={{display:"flex",gap:5,flexWrap:"wrap",marginTop:7}}>
                      {finApres&&<button style={bt} onClick={()=>setMData(p=>({...p,_absGo:"fin"}))}>⏭ Jusqu'à la fin — {court(jClic)} au {court(dFin)}</button>}
                      <button style={bt} onClick={()=>setMData(p=>({...p,_absGo:"tout"}))}>⏮⏭ Toute l'{lab==="FMC"?"a FMC":"absence"} — {court(dDeb)} au {court(dFin)}</button>
                    </div>
                  :
                    <div style={{marginTop:7}}>
                      <div style={{fontSize:11,fontWeight:700,color:"#991b1b",marginBottom:5}}>Retirer l'{lab==="FMC"?"a FMC":"absence"} de {med&&med.init} {cible.txt} ?</div>
                      <div style={{display:"flex",gap:5}}>
                        <button style={{...bt,background:"var(--bg2)",border:"1px solid var(--border)",color:"var(--txt2)"}} onClick={()=>setMData(p=>({...p,_absGo:null}))}>Annuler</button>
                        <button style={{...bt,background:"#dc2626",border:"1px solid #dc2626",color:"#fff"}}
                          onClick={()=>{removeAbsence(perSlots({medId,dateFrom:cible.df,dateTo:cible.dt,slotDebut:cible.sd,slotFin:cible.sf,slots:["M","AM"]}));setModal(null);}}>Oui, retirer</button>
                      </div>
                    </div>}
                </div>);
            })()}

            {hasOther&&canEditThisMed&&(
              <div style={{display:"flex",alignItems:"center",gap:6,padding:"6px 10px",borderRadius:7,background:"rgba(245,158,11,.15)",border:"1px solid #f59e0b44",marginBottom:10}}>
                <span>⚠️</span><span style={{fontSize:11,color:"#f59e0b"}}>Ce médecin a déjà une activité sur ce créneau.</span>
              </div>
            )}

            {/* v10.81 : etat des preferences de tour et de garde, TOUJOURS visible
                (independant du bouton de coloration du Planning) et retirable ici —
                c'etait le seul reglage qu'on ne pouvait pas defaire simplement. */}
            {(()=>{
              if(!med||(!med.tourMed&&!med.garde))return null;
              if(isAdminEdit||isInterne)return null;
              if(!(isEdit||isInterEdit||canEditThisMed))return null;
              const wkP=wKey(y2,m2,d2),dkP=dKey(y2,m2,d2);
              const tP=((tourWish[wkP]||{})[medId])?"wish":(((tourAvoid[wkP]||{})[medId])?"avoid":null);
              const gP=((gardeWish[dkP]||{})[medId])?"wish":(((gardeAvoid[dkP]||{})[medId])?"avoid":null);
              if(!tP&&!gP)return null;
              const delP=(setter,key)=>setter(p=>{const n={...p};const o={...(n[key]||{})};delete o[medId];if(Object.keys(o).length===0)delete n[key];else n[key]=o;return n;});
              const wa=wkP.split("-").map(Number);
              const dLun=new Date(wa[0],wa[1],wa[2]),dVen=new Date(wa[0],wa[1],wa[2]+4);
              const frP=dt=>dt.getDate()+"/"+(dt.getMonth()+1);
              const ligneP=(txt,col,onClick)=>(
                <div onClick={canEditThisMed?onClick:undefined} title={canEditThisMed?"Cliquer pour retirer cette préférence":undefined}
                  style={{display:"flex",alignItems:"center",justifyContent:"space-between",gap:8,padding:"6px 10px",borderRadius:7,fontSize:11,fontWeight:700,
                    border:"1px solid "+col+"55",background:col+"18",color:col,cursor:canEditThisMed?"pointer":"default"}}>
                  <span>{txt}</span>{canEditThisMed&&<span style={{fontSize:13}}>×</span>}
                </div>);
              return (
                <div style={{display:"flex",flexDirection:"column",gap:5,marginBottom:10}}>
                  {tP&&!mData._prefGo&&ligneP(tP==="wish"?"⭐ Souhaite tourner cette semaine":"🚫 Préfère ne pas tourner cette semaine",
                    tP==="wish"?"#16a34a":"#dc2626",()=>setMData(p=>({...p,_prefGo:1})))}
                  {tP&&mData._prefGo&&(
                    <div style={{border:"1px solid #f59e0b",background:"rgba(245,158,11,.12)",borderRadius:7,padding:"7px 10px"}}>
                      <div style={{fontSize:11,fontWeight:700,color:"#b45309",marginBottom:6}}>Cela retire la préférence pour TOUTE la semaine du {frP(dLun)} au {frP(dVen)}.</div>
                      <div style={{display:"flex",gap:6}}>
                        <button style={{...S.qBtn}} onClick={()=>setMData(p=>({...p,_prefGo:0}))}>Annuler</button>
                        <button style={{...S.qBtn,borderColor:"#dc2626",background:"#fef2f2",color:"#dc2626"}}
                          onClick={()=>{delP(tP==="wish"?setTourWish:setTourAvoid,wkP);setMData(p=>({...p,_prefGo:0}));toast("Préférence de tour retirée pour la semaine","info");}}>Oui, retirer</button>
                      </div>
                    </div>)}
                  {gP&&ligneP(gP==="wish"?"⭐ Souhaite être de garde ce jour":"🚫 Préfère ne pas être de garde ce jour",
                    gP==="wish"?"#16a34a":"#dc2626",()=>{delP(gP==="wish"?setGardeWish:setGardeAvoid,dkP);toast("Préférence de garde retirée","info");})}
                </div>);
            })()}
            {canEditThisMed&&(
              <div style={{display:"flex",gap:5,marginBottom:10,flexWrap:"wrap"}}>
                {/* v9.92 : un seul bouton remplace « Pose et retrait Abs », « Effacer activités » et « Effacer mois » */}
                {canEditThisMed&&<button style={{...S.qBtn,borderColor:"#1d4ed8",background:"#eff6ff",color:"#1e40af"}} onClick={()=>{setMData({medId,y:y2,m:m2,d:d2,slot,_perMode:true});setModal("periode");}}>📅 Modifier sur une période…</button>}
                {/* v10.2 : réservé à l'éditeur — restaurer écrase le travail d'autrui sur la période */}
                {isEdit&&<button style={{...S.qBtn,borderColor:"#16a34a",background:"#f0fdf4",color:"#166534"}} onClick={()=>{setMData({medId,y:y2,m:m2,d:d2,slot,_resMode:true});refreshBackupList();setModal("restaure");}}>↩ Restaurer depuis une sauvegarde…</button>}
                {isEdit&&<button style={{...S.qBtn,borderColor:"#1d4ed8",background:"#eff6ff",color:"#1e40af"}} onClick={()=>{setModal(null);openPtModal(medId);}}>▶ PT {med&&med.init}</button>}
                {canEditThisMed&&!isAdminEdit&&med&&(med.tourMed||med.garde)&&<button style={{...S.qBtn,borderColor:"#7c3aed",background:"#f3e8ff",color:"#6d28d9"}}
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
                            if(cellHasAny(dm3[mid2],["TOUR_"+unitC])){const r=cellDrop(dm3[mid2],["TOUR_"+unitC]);if(r)dm3[mid2]=r;else delete dm3[mid2];ch=true;}
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
                {/* v10.1 : plus de pose de garde ici. Le bouton prenait trois apparences
                    différentes selon le contexte et disparaissait parfois — les gardes se
                    posent depuis la colonne Garde du Planning et depuis l'onglet Gardes. */}
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
                      {salleWarn&&<span style={{fontSize:9,fontWeight:800,color:"#b45309",background:"#fff8e6",border:"1px solid #f59e0b",borderRadius:4,padding:"1px 5px",marginTop:2,alignSelf:"flex-start",lineHeight:1.35}}>⚠ {fixedSalleOcc.map(m=>m.init).join(", ")} déjà assigné</span>}
                    </button>
                  );
                })}
              </div>
            )}

            {/* v9.47 : c'était `isEdit` — le rôle administratif et la cadre voyaient donc la
                grille des activités sans jamais obtenir le choix de salle, ce qui rendait
                inopérante toute activité en ayant une (c'est-à-dire presque toutes). */}
            {mData&&mData._pickSalle&&canEditThisMed&&(()=>{
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
                    <button style={{padding:"5px 9px",borderRadius:5,border:"1px solid var(--border)",cursor:"pointer",background:"var(--bg2)",color:"var(--txt2)",fontSize:11,fontWeight:700}} onClick={()=>setMData(p=>({...p,_pickSalle:null}))}>← Retour</button>
                    {!a.fixedSalle&&<button style={{padding:"5px 9px",borderRadius:5,border:"1px solid var(--border)",cursor:"pointer",background:"var(--bg2)",color:"var(--txt2)",fontSize:11,fontWeight:700}} onClick={()=>doAdd(a.id,null)}>Sans salle</button>}
                    {(a.salles||[]).map(s=>{
                      const roomOccs=fullRoomOcc[s]||[];
                      const selfOccs=occ[s]||[];
                      const isFull=a.maxParSalle&&selfOccs.length>=a.maxParSalle;
                      const hasOther=roomOccs.length>0&&!roomOccs.every(m=>m.id===medId);
                      const warn=isFull||hasOther;
                      const allOccs=uniqArr(roomOccs.concat(selfOccs).map(m=>m.init));
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
              <textarea value={notesAff[nk(medId,y2,m2,d2,slot)]||""} onChange={e=>setNotes(p=>({...p,[nk(medId,y2,m2,d2,slot)]:e.target.value}))}
                placeholder="Note visible au survol..." readOnly={(estClos(y2,m2,d2)&&!isEdit)||!canEditThisMed||(isAdminEdit&&!adminCanNotes&&!entries.some(e2=>{const a2=acteById(e2.acteId);return a2&&a2[roleOkKey]===true;}))}
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
          medecins={medsAff}
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

      {histConf&&<Ov onClose={()=>setHistConf(null)}>
        <div style={{minWidth:300,maxWidth:380}}>
          <div style={S.mHd}><div style={{...S.mTit2,color:"#b45309"}}>⚠ {histConf.sens==="undo"?"Annuler l'action précédente":"Rétablir l'action"}</div></div>
          <div style={{fontSize:12.5,lineHeight:1.6}}>
            Cette action modifie <b>{histConf.n} cases</b> du planning.<br/>
            {histConf.sens==="undo"
              ? "Elles reviendront à leur état précédent."
              : "Elles reprendront l'état d'après l'action."}
          </div>
          <div style={{fontSize:11,color:"var(--txt2)",marginTop:8}}>Vous pourrez faire le geste inverse juste après.</div>
          <div style={{display:"flex",gap:6,marginTop:13}}>
            <button style={{...S.icnBtn,flex:1}} onClick={()=>setHistConf(null)}>Annuler</button>
            <button style={{...S.btnP,flex:1,background:"#b45309"}} onClick={histGo}>{histConf.sens==="undo"?"Revenir en arrière":"Rétablir"}</button>
          </div>
        </div>
      </Ov>}
      {modal==="vacColler"&&<Ov onClose={()=>setModal(null)}>
        <VacCollerModal onClose={()=>setModal(null)}
          onValider={lignes=>{setVacs(v=>v.filter(x=>!lignes.some(n2=>n2.an===x.an)).concat(lignes));setModal(null);toast(lignes.length+" période(s) enregistrée(s)","info");}}/>
      </Ov>}
      {modal==="restaure"&&mData&&<Ov onClose={()=>setModal(null)}>
        <RestoreModal med={medecins.find(m=>m.id===mData.medId)} backups={backupList}
          y={mData.y} m={mData.m} d={mData.d}
          onDiff={(id,df,dt)=>diffMedPeriod(id,mData.medId,df,dt)}
          onGo={(id,df,dt)=>{restoreMedPeriod(id,mData.medId,df,dt);setModal(null);}}
          onClose={()=>setModal(null)}/>
      </Ov>}
      {modal==="periode"&&mData&&<Ov onClose={()=>setModal(null)}>
        <PeriodModal
          medecins={medsAff}
          initMedId={mData.medId}
          initDate={`${mData.y}-${String(mData.m+1).padStart(2,"0")}-${String(mData.d).padStart(2,"0")}`}
          year={year} month={month} mois={ptPeriodMonths} finPer={(()=>{const p=perStart(year,month);const e=perEnd(p.sy,p.sm);return `${e.getFullYear()}-${String(e.getMonth()+1).padStart(2,"0")}-${String(e.getDate()).padStart(2,"0")}`;})()} allowActs={!isAdminEdit} compter={countPeriodActs}
          onPose={p=>{applyAbsence(perSlots(p));setModal(null);}}
          onRetraitAbs={p=>{removeAbsence(perSlots(p));setModal(null);}}
          onEffacer={p=>{
            clearPeriodActs(perSlots(p));
            /* v10.13 : le TOUR ne vit pas dans le planning mais dans une liste de semaines —
               il fallait donc le retirer à part, sinon il restait en place. */
            if(p.keepGardes===false)removeTourPeriod(p.medId,p.dateFrom,p.dateTo);
            setModal(null);}}
          onClose={()=>setModal(null)}/>
      </Ov>}
      {modal==="absence"&&<Ov onClose={()=>setModal(null)}><AbsModal medecins={medsAff}
  initMedId={mData&&mData._absMode?mData.medId:null}
  initDate={mData&&mData._absMode?`${mData.y}-${String(mData.m+1).padStart(2,"0")}-${String(mData.d).padStart(2,"0")}`:null}
  onApply={p=>{applyAbsence(p);setModal(null);}}
  onRemove={p=>{removeAbsence(p);setModal(null);}}
  onClose={()=>setModal(null)}/></Ov>}
      {modal==="colOrder"&&colModal&&<div style={S.ov} onClick={()=>{setModal(null);setColModal(null);}}>
        <div style={{...S.mb,width:330}} onClick={e=>e.stopPropagation()}>
          <div style={S.mHd}><div style={S.mTit2}>↔ Ordre des colonnes — {colModal.site}</div><button style={S.xBtn} onClick={()=>{setModal(null);setColModal(null);}}>×</button></div>
          <div style={{fontSize:11,color:"var(--txt2)",marginBottom:8}}>Cet ordre est partagé par toute l'équipe. Une colonne ajoutée plus tard se place en dernier.</div>
          <div style={{display:"flex",flexDirection:"column",gap:4,maxHeight:340,overflowY:"auto"}}>
            {(colModal.cols||[]).map((c,i)=>{
              const lab=c==="CHB-BIP"?"BIP":(String(c).indexOf("RECAP:")===0?((actes.find(a2=>a2.id===c.slice(6))||{}).label||c.slice(6)):c);
              const isRec=c==="CHB-BIP"||String(c).indexOf("RECAP:")===0;
              return(
                <div key={c} style={{display:"flex",alignItems:"center",gap:6,padding:"4px 6px",border:"1px solid var(--border)",borderRadius:6,background:"var(--bg2)"}}>
                  <span style={{fontSize:10,color:"var(--txt3)",width:14}}>{isRec?"↩":"🚪"}</span>
                  <span style={{flex:1,fontSize:12,fontWeight:700}}>{lab}</span>
                  <button disabled={i===0} title="Monter" style={{...S.icnBtn,fontSize:11,fontWeight:800,opacity:i===0?.3:1}} onClick={()=>moveCol(colModal.site,c,-1)}>▲</button>
                  <button disabled={i===(colModal.cols||[]).length-1} title="Descendre" style={{...S.icnBtn,fontSize:11,fontWeight:800,opacity:i===(colModal.cols||[]).length-1?.3:1}} onClick={()=>moveCol(colModal.site,c,1)}>▼</button>
                </div>);
            })}
          </div>
          <button style={{...S.icnBtn,width:"100%",marginTop:10}} onClick={()=>{setColOrder(p=>({...p,[colModal.site]:[]}));setModal(null);setColModal(null);}}>↩ Ordre par défaut</button>
        </div>
      </div>}
      {modal==="ptOrder"&&<div style={S.ov} onClick={()=>setModal(null)}>
        <div style={{...S.mb,width:330}} onClick={e=>e.stopPropagation()}>
          <div style={S.mHd}><div style={S.mTit2}>↔ Ordre des colonnes — PT Cardio</div><button style={S.xBtn} onClick={()=>setModal(null)}>×</button></div>
          <div style={{fontSize:11,color:"var(--txt2)",marginBottom:8}}>Cet ordre est partagé par toute l'équipe. Une activité que l'on vient de cocher « ❤️ PT Cardio » se place en dernier.</div>
          <div style={{display:"flex",flexDirection:"column",gap:4,maxHeight:340,overflowY:"auto"}}>
            {ptRows.map((r,i)=>(
              <div key={r.key} style={{display:"flex",alignItems:"center",gap:6,padding:"4px 6px",border:"1px solid var(--border)",borderRadius:6,background:"var(--bg2)"}}>
                <span style={{width:8,height:18,borderRadius:3,background:r.color,flexShrink:0}}/>
                <span style={{flex:1,fontSize:12,fontWeight:700}}>{r.label}</span>
                <button disabled={i===0} title="Monter" style={{...S.icnBtn,fontSize:11,fontWeight:800,opacity:i===0?.3:1}} onClick={()=>movePtRow(r.key,-1)}>▲</button>
                <button disabled={i===ptRows.length-1} title="Descendre" style={{...S.icnBtn,fontSize:11,fontWeight:800,opacity:i===ptRows.length-1?.3:1}} onClick={()=>movePtRow(r.key,1)}>▼</button>
              </div>
            ))}
          </div>
          <button style={{...S.icnBtn,width:"100%",marginTop:10}} onClick={()=>setPtOrder([])}>↩ Ordre par défaut</button>
          <div style={{fontSize:9,color:"var(--txt3)",marginTop:8,lineHeight:1.45}}>Les colonnes se déduisent des activités : la salle indiquée sur chaque fiche d'activité décide de la colonne où elle apparaît. Modifier une salle dans l'onglet Activités déplace donc la colonne ici.</div>
        </div>
      </div>}
      {modal==="print"&&(()=>{
        const TABN={planning:"📅 Planning équipe",chl:"🏥 CHL",chb:"🏥 CHB",plateau:"❤️ PT Cardio",angio:"🔬 PT Angio",garde:"🌙 Gardes",attache:"👔 Attachés",astreinte:"📞 Astreinte"};
        const isG=tab==="garde"||tab==="astreinte";
        /* l'onglet Astreinte navigue sur sa propre période */
        const pBase=tab==="astreinte"?perStart(astYear,astMonth):perStart(year,month);
        const mois=[];for(let i=0;i<PCFG.len;i++){const m3=(pBase.sm+i)%12,y3=pBase.sm+i>11?pBase.sy+1:pBase.sy;mois.push({y:y3,m:m3});}
        const doPrint=(range)=>{setPrintWk(range);setModal(null);setTimeout(()=>{window.print();setTimeout(()=>setPrintWk(null),600);},350);};
        return(
        <div style={S.ov} onClick={()=>setModal(null)}>
          <div style={{...S.mb,width:330}} onClick={e=>e.stopPropagation()}>
            <div style={S.mHd}><div style={S.mTit2}>{"🖨️ Imprimer — "+(TABN[tab]||"")}</div><button style={S.xBtn} onClick={()=>setModal(null)}>×</button></div>
            <div style={S.fl}>{isG?"Période à imprimer":"Semaine à imprimer"}</div>
            <div style={{maxHeight:250,overflowY:"auto",marginBottom:10}}>
              {isG
                ?<>
                   {mois.map(o=><button key={o.y+"-"+o.m} onClick={()=>doPrint({k:"m",y:o.y,m:o.m})} style={{width:"100%",textAlign:"left",...S.fi,marginBottom:4,cursor:"pointer",fontSize:12,fontWeight:700,background:"var(--bg2)",color:"var(--txt)"}}>{MOIS[o.m]+" "+o.y}</button>)}
                   <button onClick={()=>doPrint({k:"p"})} style={{width:"100%",textAlign:"left",...S.fi,marginBottom:4,cursor:"pointer",fontSize:12,fontWeight:800,background:"rgba(63,185,80,.15)",color:"#3fb950",border:"1px solid #3fb950"}}>{"Toute la période ("+_titlePeriod+")"}</button>
                 </>
                :printWeekList(year,month).map(w=>
                   <button key={w.y+"-"+w.m+"-"+w.d} onClick={()=>doPrint({k:"w",y:w.y,m:w.m,d:w.d})} style={{width:"100%",textAlign:"left",...S.fi,marginBottom:4,cursor:"pointer",fontSize:12,fontWeight:700,background:"var(--bg2)",color:"var(--txt)"}}>{"Semaine du lundi "+w.d+" "+MOIS[w.m]}</button>)}
            </div>
            <div style={{fontSize:9,color:"var(--txt3)"}}>La boîte d'impression du navigateur s'ouvrira : choisissez l'imprimante, ou « Enregistrer en PDF » pour envoyer la feuille.</div>
          </div>
        </div>);
      })()}

      {modal==="pickMedAct"&&mData&&<PickMedActModal patchAct={patchActivity} canDif={isEdit||(isAdminEdit&&isCadre)} intCfg={intCfg} canInt={isEdit||isInterEdit||(isAdminEdit&&isCadre)} mData={mData} setMData={setMData} medecins={medsAff} actes={actes} getEntries={getEntries} isMedAvailable={isMedAvailable} addEntry={addEntry} removeEntry={removeEntry} adminOnly={isAdminEdit} okKey={roleOkKey} notes={notesAff} setNotes={setNotes} canNotes={adminCanNotes} selfOnly={isMedEdit&&!isInterEdit?editMedId:null} onClose={()=>setModal(null)}/>}
      {modal==="pickMedSite"&&mData&&<PickMedSiteModal intCfg={intCfg} canInt={isEdit||isInterEdit||(isAdminEdit&&isCadre)} mData={mData} medecins={medsAff} actes={actes} getEntries={getEntries} isMedAvailable={isMedAvailable} addEntry={addEntry} removeEntry={removeEntry} adminOnly={isAdminEdit} okKey={roleOkKey} notes={notesAff} setNotes={setNotes} canNotes={adminCanNotes} selfOnly={isMedEdit&&!isInterEdit?editMedId:null} onClose={()=>setModal(null)} darkMode={darkMode}/>}
      {modal==="editPT"&&mData&&<EditPTModal mData={mData} setMData={setMData} medecins={medsAff} actes={actes} planningType={planningType} setPlanningType={setPlanningType} onClose={()=>setModal(null)}/>}

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
            <div style={{gridColumn:"1/-1",display:"flex",gap:8,alignItems:"center"}}><input type="checkbox" checked={!!mData.csReport} onChange={e=>setMData(p=>({...p,csReport:e.target.checked}))} style={{width:14,height:14}}/><label style={{color:"var(--txt2)",fontSize:12}}>📥 Consultation à reporter (proposée dans l'onglet Reports)</label></div>
            {!(mData.id==="GARDE"||mData.id==="REPOS_GARDE"||mData.id==="TP")&&<div style={{gridColumn:"1/-1",display:"flex",gap:8,alignItems:"center"}}><input type="checkbox" checked={!!mData.adminOk} onChange={e=>setMData(p=>({...p,adminOk:e.target.checked}))} style={{width:14,height:14}}/><label style={{color:"var(--txt2)",fontSize:12}}>✏️ Modifiable par les secrétaires (rôle administratif)</label></div>}
            {!(mData.id==="GARDE"||mData.id==="REPOS_GARDE"||mData.id==="TP")&&<div style={{gridColumn:"1/-1",display:"flex",gap:8,alignItems:"center"}}><input type="checkbox" checked={!!mData.cadreOk} onChange={e=>setMData(p=>({...p,cadreOk:e.target.checked}))} style={{width:14,height:14}}/><label style={{color:"var(--txt2)",fontSize:12}}>✏️ Modifiable par les cadres (PIN cadre)</label></div>}
            {!(mData.id==="GARDE"||mData.id==="REPOS_GARDE"||mData.id==="TP")&&<div style={{gridColumn:"1/-1",display:"flex",gap:8,alignItems:"center"}}><input type="checkbox" checked={!!mData.interneOk} onChange={e=>setMData(p=>({...p,interneOk:e.target.checked}))} style={{width:14,height:14}}/><label style={{color:"var(--txt2)",fontSize:12}}>🎓 Accessible aux internes</label></div>}
            {!(mData.id==="GARDE"||mData.id==="REPOS_GARDE"||mData.id==="TP")&&!!mData.interneOk&&<div style={{gridColumn:"1/-1",display:"flex",gap:8,alignItems:"center",marginLeft:22}}><input type="checkbox" checked={!!mData.interneSelf} onChange={e=>setMData(p=>({...p,interneSelf:e.target.checked}))} style={{width:14,height:14}}/><label style={{color:"var(--txt2)",fontSize:12}}>Posable par les internes eux-mêmes (sinon : secrétaire, cadre, intermédiaire ou éditeur)</label></div>}
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
              {(()=>{
                const inSite=(x,site3)=>Array.isArray(x.s)?x.s.indexOf(site3)>=0:x.s===site3;
                const regN=salleReg.map(x=>x.n);
                const orph=actes.flatMap(a2=>a2.salles||[]).filter(s=>regN.indexOf(s)<0);
                /* v9.79 : regroupement par LIEU réel, plus par onglet d'affichage */
                const groups=[["Lens (CHL)",salleReg.filter(x=>salleSite(x)==="CHL").map(x=>x.n)],
                              ["Béthune (CHB)",salleReg.filter(x=>salleSite(x)==="CHB").map(x=>x.n)],
                              ["Hors registre",orph]];
                return groups.filter(([g0])=>mData.site==="CHL"?g0!=="Béthune (CHB)":mData.site==="CHB"?g0!=="Lens (CHL)":true).map(([g,list3])=>{
                  const uniq=list3.filter((s,ix,arr)=>arr.indexOf(s)===ix).sort();
                  if(uniq.length===0)return null;
                  return <div key={g} style={{marginBottom:6}}>
                    <div style={{fontSize:9,fontWeight:800,color:"var(--txt3)",textTransform:"uppercase",letterSpacing:.4,marginBottom:3}}>{g}</div>
                    <div style={{display:"flex",flexWrap:"wrap",gap:4}}>
                      {uniq.map(s=>{
                        const on=(mData.salles||[]).includes(s);
                        return <button key={s} type="button" onClick={()=>setMData(p=>{const cur=p.salles||[];const nx=on?cur.filter(x=>x!==s):cur.concat([s]);return {...p,salles:nx,sallesStr:nx.join(", ")};})}
                          style={{fontSize:10,padding:"3px 8px",borderRadius:12,cursor:"pointer",fontWeight:700,border:on?"1.5px solid #388bfd":"1px solid var(--border)",background:on?"rgba(56,139,253,.15)":"var(--bg2)",color:on?"#388bfd":"var(--txt2)"}}>{s}</button>;
                      })}
                    </div>
                  </div>;
                });
              })()}
              <div style={{fontSize:9,color:"var(--txt3)"}}>Créer/renommer une salle : Paramètres → 🏥 Salles.</div></div>}
            <div style={{gridColumn:"1 / -1",display:"flex",alignItems:"center",gap:8,margin:"2px 0"}}>
              <label style={{...S.fl,margin:0}}>🩺 IDE nécessaires</label>
              <input type="number" min={0} max={9} value={mData.ideN||0} onChange={e=>{const v=Math.max(0,Math.min(9,parseInt(e.target.value||"0",10)||0));setMData(p=>({...p,ideN:v}));}} style={{...S.fi,width:64,textAlign:"center"}}/>
              <span style={{fontSize:10,color:"var(--txt3)"}}>0 = aucune IDE requise</span>
            </div>
            <div style={{gridColumn:"1/-1"}}><label style={S.fl}>{(mData.id==="GARDE"||mData.id==="REPOS_GARDE"||mData.id==="TP")?"Médecins autorisés":"Médecins autorisés (vide = tous)"}</label>
              {(mData.id==="GARDE"||mData.id==="REPOS_GARDE"||mData.id==="TP")?(
                <div>
                  <div style={{display:"flex",flexWrap:"wrap",gap:4,marginBottom:6}}>
                    {medecins.filter(m2=>(mData.id==="TP"?m2.partTime===true:m2.garde===true)).map(m2=>(
                      <span key={m2.id} title={((m2.prenom||"")+" "+(m2.nom||"")).trim()} style={{fontSize:10,padding:"3px 8px",borderRadius:12,fontWeight:700,display:"inline-flex",alignItems:"center",gap:4,border:"1.5px solid "+m2.color,background:m2.color+"26",color:"var(--txt)"}}>
                        <span style={{width:12,height:12,borderRadius:"50%",background:m2.color,display:"inline-block"}}/>{m2.init}
                      </span>
                    ))}
                  </div>
                  <div style={{fontSize:10,color:"#16a34a",fontWeight:700}}>{mData.id==="TP"?"⚙ Liste gérée par la coche « Temps partiel » des fiches médecins (Équipe) — modifiez-la là-bas.":"⚙ Liste gérée par la coche « Garde » de l'onglet Équipe — modifiez-la là-bas."}</div>
                </div>
              ):(
              <div style={{display:"flex",flexWrap:"wrap",gap:4,maxHeight:120,overflowY:"auto"}}>
                {(()=>{const aucun=(mData.medecinsAutorise||[]).includes("__AUCUN__");return <button type="button" onClick={()=>setMData(p=>{const nx=aucun?[]:["__AUCUN__"];return {...p,medecinsAutorise:nx,medStr:aucun?"":"Aucun"};})} style={{fontSize:10,padding:"3px 8px",borderRadius:12,cursor:"pointer",fontWeight:800,border:aucun?"1.5px solid #f85149":"1px solid var(--border)",background:aucun?"rgba(248,81,73,.15)":"var(--bg2)",color:aucun?"#f85149":"var(--txt3)"}}>🚫 Aucun médecin</button>;})()}
                {medecins.filter(m2=>m2.role!=="ide").map(m2=>{
                  const on=(mData.medecinsAutorise||[]).includes(m2.init);
                  return <button key={m2.id} type="button" title={((m2.prenom||"")+" "+(m2.nom||"")).trim()} onClick={()=>setMData(p=>{const cur=(p.medecinsAutorise||[]).filter(x=>x!=="__AUCUN__");const nx=on?cur.filter(x=>x!==m2.init):cur.concat([m2.init]);return {...p,medecinsAutorise:nx,medStr:nx.join(", ")};})}
                    style={{fontSize:10,padding:"3px 8px",borderRadius:12,cursor:"pointer",fontWeight:700,opacity:(mData.medecinsAutorise||[]).includes("__AUCUN__")?.3:1,pointerEvents:(mData.medecinsAutorise||[]).includes("__AUCUN__")?"none":"auto",display:"inline-flex",alignItems:"center",gap:4,border:on?"1.5px solid "+m2.color:"1px solid var(--border)",background:on?m2.color+"26":"var(--bg2)",color:on?"var(--txt)":"var(--txt3)"}}>
                    <span style={{width:12,height:12,borderRadius:"50%",background:m2.color,display:"inline-block"}}/>{m2.init}</button>;
                })}
              </div>)}</div>
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
            <label style={{...S.fl,marginTop:10,display:"block"}}>Lieu (hôpital où se trouve la salle)</label>
            <div style={{display:"flex",gap:6}}>
              {[["CHL","🏥 Lens"],["CHB","🏥 Béthune"]].map(([v3,l3])=>(
                <button key={v3} onClick={()=>setMData(p=>({...p,site:v3}))}
                  style={{flex:1,fontSize:12,padding:"7px 10px",borderRadius:8,cursor:"pointer",fontWeight:700,
                    border:salleSite(mData)===v3?"1.5px solid #388bfd":"1px solid var(--border)",
                    background:salleSite(mData)===v3?"rgba(56,139,253,.15)":"var(--bg2)",color:"var(--txt)"}}>{l3}</button>
              ))}
            </div>
            <div style={{fontSize:9,color:"var(--txt3)",marginTop:3}}>Sert à proposer la salle aux activités du bon hôpital et à repérer un praticien attendu sur les deux sites.</div>
            <label style={{...S.fl,marginTop:10,display:"block"}}>Onglets où la salle s'affiche</label>
            <div style={{display:"flex",gap:6,flexWrap:"wrap"}}>
              {[["CHL","\ud83c\udfe5 CHL"],["CHB","\ud83c\udfe5 CHB"],["ANGIO","\ud83d\udd2c PT Angio"],["PLATEAU","\u2764\ufe0f PT Cardio"]].map(([v2,l2])=>(
                <button key={v2} onClick={()=>setMData(p=>{const cur=Array.isArray(p.s)?p.s:(p.s?[p.s]:[]);const nx=cur.includes(v2)?cur.filter(x=>x!==v2):cur.concat([v2]);return {...p,s:nx};})} style={{flex:"1 1 40%",padding:"9px 6px",borderRadius:8,border:"none",cursor:"pointer",fontWeight:700,fontSize:13,background:(Array.isArray(mData.s)?mData.s:[mData.s]).includes(v2)?"#1d4ed8":"var(--bg2)",color:(Array.isArray(mData.s)?mData.s:[mData.s]).includes(v2)?"#fff":"var(--txt2)"}}>{l2}</button>
              ))}
            </div>
            {/* v10.49 : participation aux demi-journées off (onglet Reports) */}
            <label style={{...S.fl,marginTop:10,display:"block"}}>Demi-journées off (onglet Reports)</label>
            <div onClick={()=>setMData(pp=>({...pp,offOuv:!offOuvOn(pp,actes)}))}
              style={{display:"flex",gap:9,alignItems:"flex-start",cursor:"pointer",border:"1.5px dashed #7c3aed",background:"rgba(124,58,237,.05)",borderRadius:9,padding:"8px 11px",marginTop:2}}>
              <input type="checkbox" readOnly checked={offOuvOn(mData,actes)} style={{width:16,height:16,accentColor:"#7c3aed",marginTop:1,pointerEvents:"none"}}/>
              <div style={{fontSize:11.5,lineHeight:1.45,color:"var(--txt2)"}}>
                <b style={{color:"var(--txt)"}}>Ouvrable sur un off</b><br/>
                Une consultation peut s'ouvrir dans cette salle sur une demi-journée off (onglet Reports). Les activités proposées en découlent : celles de cette salle, rien d'autre.
              </div>
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
            {/* v9.79 : bouton de position retiré — une salle pouvant vivre dans plusieurs onglets, l'ordre se règle désormais dans chaque onglet (bouton ↕). */}
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
                    setSalleReg(p=>[...p,{n:nm,s:sArr.length===1?sArr[0]:sArr,...(mData.offOuv!==undefined?{offOuv:!!mData.offOuv}:{})}]);
                    if((mData._acts||[]).length>0)setActes(p=>p.map(a=>(mData._acts.includes(a.id)&&!(a.salles||[]).includes(nm))?{...a,salles:(a.salles||[]).concat([nm])}:a));
                    toast("Salle créée : "+nm,"info");
                  }else if(nm!==mData._origN){
                    if(salleReg.some(x=>x.n===nm))return toast("Ce nom existe déjà","warn");
                    setSalleReg(p=>p.map(x=>x.n===mData._origN?{...x,n:nm,s:mData.s,...(mData.offOuv!==undefined?{offOuv:!!mData.offOuv}:{})}:x));
                    setActes(p=>p.map(a=>({...a,salles:(a.salles||[]).map(s2=>s2===mData._origN?nm:s2)})));
                    setPlan(p=>{const n2={};Object.keys(p).forEach(k=>{const dm={};Object.keys(p[k]).forEach(mid=>{const e=p[k][mid];const fx=(o)=>o&&o.salle===mData._origN?{...o,salle:nm}:o;dm[mid]=Array.isArray(e)?e.map(fx):fx(e);});n2[k]=dm;});return n2;});
                    toast("Salle renommée partout : "+mData._origN+" \u2192 "+nm,"info");
                  }else{
                    setSalleReg(p=>p.map(x=>x.n===mData._origN?{...x,s:mData.s,...(mData.offOuv!==undefined?{offOuv:!!mData.offOuv}:{})}:x));
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
            <FF l={djRole(mData)?"Rôle du Dr Junior":"Nom"} v={mData.nom} c={v=>setMData(p=>({...p,nom:v}))}/>
            {!djRole(mData)&&<FF l="Prénom" v={mData.prenom} c={v=>setMData(p=>({...p,prenom:v}))}/>}
            {!djRole(mData)&&<FF l="Initiales (max 4)" v={mData.init} c={v=>setMData(p=>({...p,init:v.toUpperCase().slice(0,4)}))}/>}
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
            {(mData.role||"medecin")!=="medecin"&&<div style={{gridColumn:"1/-1"}}>
              <label style={{display:"flex",gap:6,alignItems:"center",color:"var(--txt2)",fontSize:13,cursor:"pointer"}}>
                <input type="checkbox" checked={mData.suiviAbs!==false} onChange={e=>setMData(p=>({...p,suiviAbs:e.target.checked}))} style={{width:14,height:14}}/>
                🚫 Absences à recueillir
              </label>
              <div style={{fontSize:11,color:"var(--txt3)",marginTop:3}}>Décochez si vous n'avez pas à recueillir ses absences : la personne ne figurera plus dans l'étape 4 de l'onglet Construire.</div>
            </div>}
            {(mData.role||"medecin")==="medecin"&&<div style={{gridColumn:"1/-1"}}>
              <label style={{fontSize:10,color:"var(--txt3)",fontWeight:700,textTransform:"uppercase",display:"block",marginBottom:4}}>Statut</label>
              <div style={{display:"flex",gap:4}}>
                {[["senior","Sénior"],["junior","Junior"]].map(([v,l])=><button key={v} onClick={()=>setMData(p=>(v==="junior"&&p.statut!=="junior"?{...p,statut:v,prenom:"",init:djCodeRole(p.init,medecins,p.id)}:{...p,statut:v}))} style={{padding:"4px 10px",borderRadius:6,border:"none",cursor:"pointer",fontWeight:700,fontSize:11,background:(mData.statut||"senior")===v?"#1d4ed8":"var(--bg2)",color:(mData.statut||"senior")===v?"#fff":"var(--txt2)"}}>{l}</button>)}
              </div>
              {djRole(mData)&&<DJEquipe mData={mData} setMData={setMData} intCfg={intCfg} prisInit={medecins.filter(m3=>m3.id!==mData.id).map(m3=>m3.init)} countActs={mData._new?null:((du,au)=>offCount(mData.id,du,au))} onClear={mData._new?null:((du,au)=>offClear(mData.id,du,au))}/>}
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
                {/* v9.85 : couleurs prises dans les paramètres, plus écrites ici */}
                {SPEC_LIST.map(([v,l])=>{const c=(specColors&&specColors[v])||SPEC_COLORS_DEF[v];return(
                  <button key={v} onClick={()=>setMData(p=>({...p,surSpec:p.surSpec===v?null:v}))}
                    style={{padding:"5px 12px",borderRadius:6,border:"1px solid "+c,cursor:"pointer",fontWeight:700,fontSize:12,
                      background:mData.surSpec===v?c:"var(--bg2)",color:mData.surSpec===v?"#fff":c}}>
                    {l}
                  </button>
                );})}
              </div>
            </div>}
            <div style={{gridColumn:"1/-1",borderTop:"1px solid var(--border)",marginTop:8,paddingTop:8,fontSize:10,fontWeight:800,color:"#e3b341",textTransform:"uppercase",letterSpacing:.5}}>🔐 Niveau de droits (avec son PIN personnel)</div>
            <div style={{gridColumn:"1/-1"}}>
              <div style={{display:"flex",flexWrap:"wrap",gap:5}}>
                {[["basic","Basique","Sa ligne uniquement"],["inter","Intermédiaire","Tous les médecins, sans le paramétrage"],["editeur","Éditeur","Accès complet"]]
                  .filter(([v])=>{const r=mData.role||"medecin";return r==="ide"?v==="basic":r==="attache"?v!=="editeur":true;})  /* v10.73 */
                  .map(([v,lab,desc])=>{
                  const on=((mData.niveau)||"basic")===v;
                  return <button key={v} type="button" onClick={()=>setMData(p=>({...p,niveau:v}))} title={desc}
                    style={{fontSize:11,padding:"4px 10px",borderRadius:11,cursor:"pointer",fontWeight:800,
                      border:on?"1.5px solid "+(v==="editeur"?"#dc2626":v==="inter"?"#e3b341":"#94a3b8"):"1px solid var(--border)",
                      background:on?(v==="editeur"?"rgba(220,38,38,.12)":v==="inter"?"rgba(227,179,65,.15)":"var(--bg2)"):"var(--bg2)",
                      color:on?(v==="editeur"?"#dc2626":v==="inter"?"#b45309":"var(--txt)"):"var(--txt3)"}}>{lab}</button>;
                })}
              </div>
              <div style={{fontSize:9,color:"var(--txt3)",marginTop:4}}>{(mData.role||"medecin")==="attache"
                ?(((mData.niveau)||"basic")==="inter"?"Modifie sa ligne et celles des attachés cochés ci-dessous, uniquement dans l'onglet Attachés. Les autres onglets restent en consultation."
                  :"Ne modifie que sa propre ligne, dans l'onglet Attachés. Les autres onglets restent en consultation.")
                :((mData.niveau)||"basic")==="editeur"?"Accès complet, y compris Paramètres, Équipe, Activités et la récupération des codes PIN.":((mData.niveau)||"basic")==="inter"?"Planning de tous les médecins, gardes et échanges, semaines de tour, planning type, attachés. Pas de Paramètres, Équipe ni Activités.":"Ne modifie que sa propre ligne (+ ses activités dans CHL, CHB et les plateaux)."}</div>
              {/* v10.73 : sa demande — les attachés dont un attaché INTERMÉDIAIRE peut
                  modifier le planning. Toujours limité à l'onglet Attachés. */}
              {(mData.role||"medecin")==="attache"&&((mData.niveau)||"basic")==="inter"&&<div style={{marginTop:8,paddingTop:8,borderTop:"1px dashed var(--border)"}}>
                <div style={{fontSize:10,fontWeight:800,color:"#e3b341",marginBottom:4}}>👔 Plannings d'attachés qu'il peut modifier</div>
                <div style={{display:"flex",flexWrap:"wrap",gap:4}}>
                  {medecins.filter(m2=>((m2.role||"medecin")==="attache")&&m2.init&&m2.init!==mData.init).map(m2=>{
                    const on=((mData.attEdit)||[]).indexOf(m2.init)>=0;
                    return <button key={m2.id} type="button" title={((m2.prenom||"")+" "+(m2.nom||"")).trim()}
                      onClick={()=>setMData(p=>{const cur=(p.attEdit)||[];return {...p,attEdit:on?cur.filter(x=>x!==m2.init):cur.concat([m2.init])};})}
                      style={{fontSize:11,padding:"3px 9px",borderRadius:11,cursor:"pointer",fontWeight:800,
                        border:on?"1.5px solid #e3b341":"1px solid var(--border)",
                        background:on?"rgba(227,179,65,.15)":"var(--bg2)",color:on?"#b45309":"var(--txt3)"}}>{m2.init}</button>;
                  })}
                </div>
                <div style={{fontSize:9,color:"var(--txt3)",marginTop:4}}>Sa propre ligne est toujours modifiable. Ni les IDE ni les internes ne figurent dans cette liste.</div>
              </div>}
            </div>
            {(mData.role||"medecin")!=="ide"&&<div style={{gridColumn:"1/-1",borderTop:"1px solid var(--border)",marginTop:8,paddingTop:8,fontSize:10,fontWeight:800,color:"#388bfd",textTransform:"uppercase",letterSpacing:.5}}>🎯 Activités autorisées</div>}
            {(mData.role||"medecin")!=="ide"&&<div style={{gridColumn:"1/-1"}}>
              {!mData.init
                ?<div style={{fontSize:11,color:"var(--txt3)"}}>Renseignez d'abord les initiales pour gérer les activités.</div>
                :[["Général",a2=>a2.site!=="CHL"&&a2.site!=="CHB"],["CHL",a2=>a2.site==="CHL"],["CHB",a2=>a2.site==="CHB"]].map(([grp,fil])=>{
                  const glist=actes.filter(a2=>!a2.isSystem&&a2.id!=="TP"&&!(a2.medecinsAutorise||[]).includes("__AUCUN__")&&fil(a2));
                  const authInit=((medecins.find(m3=>m3.id===mData.id)||{}).init)||mData._authInit||mData.init;
                  if(glist.length===0)return null;
                  return <div key={grp} style={{marginBottom:8}}>
                    <div style={{fontSize:9,fontWeight:800,color:"var(--txt3)",textTransform:"uppercase",letterSpacing:.4,marginBottom:3}}>{grp}</div>
                    <div style={{display:"flex",flexWrap:"wrap",gap:4}}>
                      {glist.map(a2=>{
                        const allowed=!(a2.medecinsAutorise&&a2.medecinsAutorise.length)||a2.medecinsAutorise.includes(authInit);
                        return <button key={a2.id} type="button" onClick={()=>{
                          if(!mData._authInit)setMData(p=>({...p,_authInit:authInit}));
                          setActes(prev=>prev.map(act=>{
                            if(act.id!==a2.id)return act;
                            const cur=act.medecinsAutorise||[];
                            if(!allowed){if(cur.length===0)return act;return{...act,medecinsAutorise:[...cur,authInit]};}
                            if(cur.length===0){const all2=medecins.map(m3=>m3.init).filter(i2=>i2!==authInit);return{...act,medecinsAutorise:all2};}
                            return{...act,medecinsAutorise:cur.filter(i2=>i2!==authInit)};
                          }));
                        }} style={{fontSize:10,padding:"3px 8px",borderRadius:11,cursor:"pointer",fontWeight:700,border:allowed?"1.5px solid "+a2.color:"1px solid var(--border)",background:allowed?a2.color+"33":"var(--bg2)",color:allowed?"var(--txt)":"var(--txt3)"}}>{a2.short}</button>;
                      })}
                    </div>
                  </div>;
                })}
              <div style={{fontSize:9,color:"var(--txt3)"}}>Modifications enregistrées immédiatement. « Général » = disponible sur toute l'application.</div>
            </div>}
          </div>
          <button style={{...S.btnP,width:"100%",marginTop:10}} onClick={()=>{
            if(!mData.nom||(!mData.init&&!djRole(mData)))return toast(djRole(mData)?"Rôle du Dr Junior requis":"Nom et initiales requis","warn");
            // v9.52 : medecinsAutorise indexe les INITIALES ; un changement d'initiales
            // orphelinait donc toutes les activités du médecin. On les renomme ici.
            const newInit=djRole(mData)?djCodeRole(mData.init,medecins,mData.id):String(mData.init).trim();
            const oldInit=((medecins.find(m3=>m3.id===mData.id)||{}).init)||mData._authInit||"";
            if(newInit!==oldInit&&medecins.some(m3=>m3.id!==mData.id&&m3.init===newInit))
              return toast("Initiales déjà utilisées par un autre membre","warn");
            const {_new,_authInit,...rest}=mData;
            rest.init=newInit;
            if(djRole(rest))rest.prenom="";
            if(oldInit&&oldInit!==newInit)setActes(prev=>prev.map(act=>{
              const cur=act.medecinsAutorise;
              if(!cur||!cur.length||!cur.includes(oldInit))return act;
              return{...act,medecinsAutorise:cur.map(i2=>i2===oldInit?newInit:i2)};
            }));
            if(_new)setMedecins(p=>[...p,rest]);else setMedecins(p=>p.map(m=>m.id===rest.id?rest:m));
            setModal(null);toast("Médecin enregistré");
          }}>Enregistrer</button>
        </Ov>
      )}



    </div>
  );
}
