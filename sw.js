/* CardioPlanning — service worker (v10.214)
   Page : réseau d'abord (toujours la dernière version quand il y a du réseau),
          cache en secours (l'app s'ouvre hors ligne).
   Bibliothèques CDN : cache d'abord (URL versionnées, jamais périmées).
   Données Firestore : jamais mises en cache ici — c'est le cache interne du SDK qui s'en charge. */
var CACHE = "cardioplanning-v10-214";   /* v10.135 : nouveau nom = les vieilles entrées (dont une v9.22) sont effacées ; v10.211 : notifications */

self.addEventListener("install", function (e) {
  self.skipWaiting();
});

self.addEventListener("activate", function (e) {
  e.waitUntil(
    caches.keys().then(function (ks) {
      return Promise.all(ks.map(function (k) { return k === CACHE ? null : caches.delete(k); }));
    }).then(function () { return self.clients.claim(); })
  );
});

self.addEventListener("fetch", function (e) {
  var req = e.request;
  if (req.method !== "GET") return;
  var url;
  try { url = new URL(req.url); } catch (err) { return; }
  // Trafic de données Firestore : laissé au SDK (qui a sa propre persistance hors ligne)
  if (url.hostname.indexOf("firestore.googleapis.com") >= 0 ||
      url.hostname.indexOf("firebaseio.com") >= 0 ||
      url.hostname.indexOf("googleapis.com") >= 0) return;

  if (req.mode === "navigate") {
    e.respondWith(
      fetch(req).then(function (res) {
        var copy = res.clone();
        /* v10.135 : la page est rangée sous UNE clé, toujours la dernière chargée — quelle que
           soit l'adresse demandée (avec ou sans « index.html », avec ou sans paramètres). */
        caches.open(CACHE).then(function (c) { c.put("index.html", copy); });
        return res;
      }).catch(function () {
        return caches.match("index.html");
      })
    );
    return;
  }

  e.respondWith(
    caches.match(req).then(function (m) {
      if (m) return m;
      return fetch(req).then(function (res) {
        if (res && (res.status === 200 || res.type === "opaque")) {
          var copy = res.clone();
          caches.open(CACHE).then(function (c) { c.put(req, copy); });
        }
        return res;
      }).catch(function () { return m; });
    })
  );
});

/* v10.211 : NOTIFICATIONS. Le script envoi-push.js (GitHub Actions) envoie par Firebase Cloud Messaging
   un message qui porte le texte dans « notification » ET dans « data » ; on l'affiche ici nous-mêmes,
   sans charger la bibliothèque Firebase dans le service worker. Contenu neutre, voulu (11/09/2026) :
   « Un message vous attend dans CardioPlanning ». Un appui ouvre (ou ramène) l'application. */
self.addEventListener("push", function (e) {
  var j = {};
  try { j = e.data ? e.data.json() : {}; } catch (err) { j = {}; }
  var n = j.notification || {}, d = j.data || {};
  var titre = n.title || d.title || "CardioPlanning";
  var corps = n.body || d.body || "Un message vous attend dans CardioPlanning";
  e.waitUntil(self.registration.showNotification(titre, {
    body: corps,
    icon: d.icon || n.icon || "icon-180.png",
    badge: d.badge || "icon-180.png",
    tag: d.tag || "cardioplanning",   /* même étiquette = une seule notification visible, la plus récente remplace */
    renotify: true,
    data: { url: d.url || "./" }
  }));
});

self.addEventListener("notificationclick", function (e) {
  e.notification.close();
  var url = (e.notification.data && e.notification.data.url) || "./";
  e.waitUntil(self.clients.matchAll({ type: "window", includeUncontrolled: true }).then(function (cs) {
    for (var i = 0; i < cs.length; i++) { if ("focus" in cs[i]) return cs[i].focus(); }
    return self.clients.openWindow(url);
  }));
});
