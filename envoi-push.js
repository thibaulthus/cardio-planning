// CardioPlanning — envoi des notifications (v10.211, 11/09/2026).
// Lancé par GitHub Actions (.github/workflows/push.yml) toutes les 10 minutes, ou à la main.
// Aucune bibliothèque à installer : Node ≥ 18 suffit (fetch et crypto sont intégrés).
//
// Ce que fait le script, à chaque passage :
//   1. s'authentifie auprès de Google avec la clé de compte de service (secret FCM_SERVICE_ACCOUNT) ;
//   2. lit dans Firestore le document planning/main (ses « annonces ») et la collection « push »
//      (un document par appareil : jeton, personne, rôle) ;
//   3. pour chaque bannière RÉCENTE (créée il y a moins de 30 jours), ACTIVE (d1 ≤ aujourd'hui ≤ d2)
//      et pas encore poussée, trouve les personnes visées — nommées (meds), ou par famille (médecins,
//      attachés) — et envoie à chacun de leurs appareils une notification NEUTRE :
//      « Un message vous attend dans CardioPlanning » ;
//   4. note la bannière comme poussée dans le document push/_etat, efface les jetons morts.
// Rien n'est jamais envoyé deux fois pour une même bannière. Un appareil enregistré APRÈS l'envoi
// ne reçoit pas les bannières antérieures — il ouvre l'application, elles y sont.
//
// Variables : FCM_SERVICE_ACCOUNT (JSON de la clé, secret du dépôt), APP_URL (adresse de l'application),
//             ESSAI=1 → lit et affiche tout, n'envoie rien, n'écrit rien.
const crypto = require("crypto");

const SA = JSON.parse(process.env.FCM_SERVICE_ACCOUNT || "null");
if (!SA || !SA.client_email || !SA.private_key || !SA.project_id) { console.error("FCM_SERVICE_ACCOUNT manquant ou incomplet (JSON de la clé de compte de service)."); process.exit(2); }
const PID = SA.project_id;
const APP_URL = process.env.APP_URL || "https://thibaulthus.github.io/cardio-planning/";
const ESSAI = !!process.env.ESSAI;
const PLAN_ID = process.env.PLAN_ID || "main";
const FS = "https://firestore.googleapis.com/v1/projects/" + PID + "/databases/(default)/documents";
const TITRE = "CardioPlanning", CORPS = "Un message vous attend dans CardioPlanning";
const JOURS_MAX = 30;

const b64 = (s) => Buffer.from(s).toString("base64").replace(/\+/g, "-").replace(/\//g, "_").replace(/=+$/, "");
async function jeton() {
  const now = Math.floor(Date.now() / 1000);
  const ent = b64(JSON.stringify({ alg: "RS256", typ: "JWT" }));
  const corps = b64(JSON.stringify({ iss: SA.client_email, scope: "https://www.googleapis.com/auth/firebase.messaging https://www.googleapis.com/auth/datastore", aud: "https://oauth2.googleapis.com/token", iat: now, exp: now + 3600 }));
  const sig = crypto.createSign("RSA-SHA256").update(ent + "." + corps).sign(SA.private_key);
  const jwt = ent + "." + corps + "." + b64(sig);
  const r = await fetch("https://oauth2.googleapis.com/token", { method: "POST", headers: { "Content-Type": "application/x-www-form-urlencoded" }, body: "grant_type=urn%3Aietf%3Aparams%3Aoauth%3Agrant-type%3Ajwt-bearer&assertion=" + jwt });
  const j = await r.json();
  if (!j.access_token) throw new Error("authentification refusée : " + JSON.stringify(j).slice(0, 200));
  return j.access_token;
}

// lecture des valeurs Firestore (format REST : { stringValue }, { integerValue }, { mapValue }…)
function val(v) {
  if (!v) return null;
  if ("stringValue" in v) return v.stringValue;
  if ("integerValue" in v) return Number(v.integerValue);
  if ("doubleValue" in v) return v.doubleValue;
  if ("booleanValue" in v) return v.booleanValue;
  if ("nullValue" in v) return null;
  if ("mapValue" in v) { const o = {}; Object.keys((v.mapValue || {}).fields || {}).forEach(k => o[k] = val(v.mapValue.fields[k])); return o; }
  if ("arrayValue" in v) return ((v.arrayValue || {}).values || []).map(val);
  return null;
}
const champs = (doc) => { const o = {}; Object.keys((doc && doc.fields) || {}).forEach(k => o[k] = val(doc.fields[k])); return o; };
async function fsGet(tok, chemin) {
  const r = await fetch(FS + "/" + chemin, { headers: { Authorization: "Bearer " + tok } });
  if (r.status === 404) return null;
  if (!r.ok) throw new Error("Firestore " + chemin + " : " + r.status + " " + (await r.text()).slice(0, 200));
  return r.json();
}
async function fsList(tok, col) {
  const out = []; let page = "";
  do {
    const r = await fetch(FS + "/" + col + "?pageSize=300" + (page ? "&pageToken=" + encodeURIComponent(page) : ""), { headers: { Authorization: "Bearer " + tok } });
    if (!r.ok) throw new Error("Firestore " + col + " : " + r.status + " " + (await r.text()).slice(0, 200));
    const j = await r.json(); (j.documents || []).forEach(d => out.push(d)); page = j.nextPageToken || "";
  } while (page);
  return out;
}
async function fsDel(tok, nom) { if (ESSAI) return; await fetch("https://firestore.googleapis.com/v1/" + nom, { method: "DELETE", headers: { Authorization: "Bearer " + tok } }); }
async function fsEtat(tok, done) {
  if (ESSAI) return;
  const r = await fetch(FS + "/push/_etat?updateMask.fieldPaths=done&updateMask.fieldPaths=at", { method: "PATCH", headers: { Authorization: "Bearer " + tok, "Content-Type": "application/json" },
    body: JSON.stringify({ fields: { done: { stringValue: JSON.stringify(done) }, at: { integerValue: String(Date.now()) } } }) });
  if (!r.ok) throw new Error("écriture push/_etat : " + r.status + " " + (await r.text()).slice(0, 200));
}
// envoi d'une notification à un jeton — rend "ok", "mort" (jeton à effacer) ou "erreur" (à retenter au prochain passage)
async function envoyer(tok, jetonAppareil, tag) {
  if (ESSAI) return "ok";
  const r = await fetch("https://fcm.googleapis.com/v1/projects/" + PID + "/messages:send", { method: "POST", headers: { Authorization: "Bearer " + tok, "Content-Type": "application/json" },
    body: JSON.stringify({ message: { token: jetonAppareil,
      notification: { title: TITRE, body: CORPS },
      data: { title: TITRE, body: CORPS, url: APP_URL, tag: "cardioplanning" },
      webpush: { headers: { Urgency: "high", TTL: "86400" }, fcm_options: { link: APP_URL } } } }) });
  if (r.ok) return "ok";
  const t = await r.text();
  if (r.status === 404 || /UNREGISTERED|not a valid FCM registration token|INVALID_ARGUMENT/.test(t)) return "mort";
  console.log("   envoi refusé (" + r.status + ") : " + t.slice(0, 160));
  return "erreur";
}

const auj = () => { const t = new Date(); return t.getFullYear() + "-" + String(t.getMonth() + 1).padStart(2, "0") + "-" + String(t.getDate()).padStart(2, "0"); };
// la bannière vise-t-elle cet appareil ? (même règle que annVise dans l'application)
const vise = (a, app) => { if (a.meds && a.meds.length) return a.meds.map(String).indexOf(String(app.med)) >= 0; const aud = a.aud || {}; return app.role === "attache" ? !!aud.att : !!aud.med; };

(async () => {
  const tok = await jeton();
  const plan = champs(await fsGet(tok, "planning/" + PLAN_ID));
  let annonces = []; try { annonces = JSON.parse(plan.annonces || "[]"); } catch (e) { annonces = []; }
  const docs = await fsList(tok, "push");
  const etatDoc = docs.find(d => /\/push\/_etat$/.test(d.name));
  let done = {}; try { done = JSON.parse((champs(etatDoc).done) || "{}") || {}; } catch (e) { done = {}; }
  const appareils = docs.filter(d => !/\/push\/_etat$/.test(d.name)).map(d => Object.assign({ nom: d.name }, champs(d))).filter(a => a.tok && a.med);
  const jour = auj(), lim = Date.now() - JOURS_MAX * 86400000;
  const aFaire = annonces.filter(a => a && a.ban && a.at && a.at >= lim && (!a.d1 || a.d1 <= jour) && (!a.d2 || a.d2 >= jour) && !done[a.id]);
  console.log(annonces.length + " message(s) dans planning/" + PLAN_ID + ", " + appareils.length + " appareil(s) enregistré(s), " + aFaire.length + " bannière(s) à pousser" + (ESSAI ? " — ESSAI, rien ne part" : ""));
  const morts = new Set(); let nEnv = 0, nErr = 0;
  for (const a of aFaire) {
    const cibles = appareils.filter(ap => vise(a, ap) && !morts.has(ap.nom));
    console.log("· « " + String(a.txt || "").slice(0, 60).replace(/\n/g, " ") + " » → " + cibles.length + " appareil(s)" + (cibles.length ? " : " + cibles.map(c => (c.init || c.med) + "/" + (c.lib || "?")).join(", ") : ""));
    let transitoire = false;
    for (const c of cibles) {
      const r = await envoyer(tok, c.tok, a.id);
      if (r === "ok") nEnv++; else if (r === "mort") { morts.add(c.nom); } else { transitoire = true; nErr++; }
    }
    if (!transitoire) done[a.id] = Date.now();
  }
  // ménage : jetons morts effacés, état allégé des bannières disparues
  for (const nom of morts) { console.log("   jeton mort effacé : " + nom.split("/").pop()); await fsDel(tok, nom); }
  const ids = new Set(annonces.map(a => a.id)); Object.keys(done).forEach(k => { if (!ids.has(k)) delete done[k]; });
  await fsEtat(tok, done);
  console.log(nEnv + " notification(s) envoyée(s), " + morts.size + " jeton(s) effacé(s)" + (nErr ? ", " + nErr + " échec(s) à retenter" : ""));
  process.exit(0);
})().catch(e => { console.error("ÉCHEC : " + (e && e.message || e)); process.exit(1); });
