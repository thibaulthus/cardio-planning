/* CardioPlanning — service worker (v10.135)
   Page : réseau d'abord (toujours la dernière version quand il y a du réseau),
          cache en secours (l'app s'ouvre hors ligne).
   Bibliothèques CDN : cache d'abord (URL versionnées, jamais périmées).
   Données Firestore : jamais mises en cache ici — c'est le cache interne du SDK qui s'en charge. */
var CACHE = "cardioplanning-v10-135";   /* v10.135 : nouveau nom = les vieilles entrées (dont une v9.22) sont effacées */

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
