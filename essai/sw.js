/* CardioPlanning — service worker (v10.287)
   Page : réseau d'abord, mais 3 s au plus (v10.274) — avec une barre de 5G la demande ne réussit ni n'échoue et
          l'écran restait figé ; passé ce délai, la copie gardée s'ouvre et la nouvelle version finit de se
          télécharger en arrière-plan pour la prochaine ouverture. Sans réseau du tout : la copie, aussitôt.
   Bibliothèques CDN : cache d'abord (URL versionnées, jamais périmées).
   Données Firestore : jamais mises en cache ici — c'est le cache interne du SDK qui s'en charge. */
var CACHE = "cardioplanning-essai-v10-287";   /* v10.266 : cache de la VERSION D'ESSAI, distinct du vrai */
var PATIENCE = 3000;   /* v10.274 : attente maximale du réseau pour la page, en millisecondes */
/* v10.135 : nouveau nom = les vieilles entrées (dont une v9.22) sont effacées ; v10.211 : notifications */

self.addEventListener("install", function (e) {
  self.skipWaiting();
});

self.addEventListener("activate", function (e) {
  /* v10.274 : on n'efface que les vieux caches de la MÊME application — la vraie et la version d'essai (essai/) partagent
     l'adresse, et jusqu'ici chacune effaçait le cache de l'autre à chaque mise à jour (plus de copie hors ligne). */
  var famille = function (k) { return String(k).replace(/v\d[\d-]*$/, ""); };
  e.waitUntil(
    caches.keys().then(function (ks) {
      var vieux = ks.filter(function (k) { return k !== CACHE && famille(k) === famille(CACHE); });
      /* avant d'effacer, on garde la dernière page d'un vieux cache si le nouveau n'en a pas encore — sinon, juste après
         une mise à jour, un réseau faible ramènerait à l'attente sans fin (la copie ne sert qu'en secours ; une version
         plus ancienne que celle en service se met d'elle-même en lecture seule et propose la mise à jour). */
      return caches.open(CACHE).then(function (c) {
        return c.match("index.html").then(function (deja) {
          if (deja) return null;
          return vieux.reduce(function (p, k) {
            return p.then(function (trouve) {
              if (trouve) return trouve;
              return caches.open(k).then(function (vc) { return vc.match("index.html"); });
            });
          }, Promise.resolve(null)).then(function (page) { return page ? c.put("index.html", page) : null; });
        });
      }).catch(function () {}).then(function () {
        return Promise.all(vieux.map(function (k) { return caches.delete(k); }));
      });
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
    /* v10.274 : on attend la page ENTIÈRE (pas seulement son début : sur une barre de 5G, l'en-tête arrive et le reste
       se traîne). Reçue en entier → rangée sous UNE clé, toujours la dernière (v10.135), et servie. Une réponse en erreur
       (404, 500…) n'écrase jamais la bonne copie. */
    var complet = fetch(req).then(function (res) {
      if (!res || !res.ok) return { ko: res };
      return res.blob().then(function (b) {
        var h = { "Content-Type": res.headers.get("Content-Type") || "text/html; charset=utf-8" };
        var garde = new Response(b, { status: 200, headers: h });
        return caches.open(CACHE).then(function (c) { return c.put("index.html", garde); })
          .catch(function () {})
          .then(function () { return { ok: new Response(b, { status: 200, headers: h }) }; });
      });
    });
    e.respondWith(new Promise(function (resolve) {
      var fini = false, t = null;
      var servir = function (r) { if (!fini && r) { fini = true; if (t) clearTimeout(t); resolve(r); } };
      var copie = function () { return caches.match("index.html"); };
      /* PATIENCE écoulée sans la page entière : la copie gardée, si elle existe — sinon on continue d'attendre le réseau */
      t = setTimeout(function () { copie().then(servir); }, PATIENCE);
      complet.then(function (x) {
        if (x.ok) return servir(x.ok);
        /* réponse en erreur : la copie si elle existe, sinon la réponse telle quelle */
        return copie().then(function (m) { servir(m || x.ko); });
      }).catch(function () {
        /* pas de réseau du tout : la copie aussitôt */
        copie().then(function (m) { servir(m || Response.error()); });
      });
    }));
    /* le téléchargement continue après la réponse donnée : la prochaine ouverture aura la nouvelle version */
    e.waitUntil(complet.catch(function () {}));
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
  var corps = n.body || d.body || "Un message vous attend dans CardioPlanning ESSAI";
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
