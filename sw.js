const V = 'trail-map-v1';
const SHELL = ['./', 'index.html', 'app.css', 'app.js', 'manifest.webmanifest', 'vendor/maplibre-gl.js', 'vendor/maplibre-gl.css',
  'data/trails.geojson', 'data/points.geojson', 'data/areas.geojson', 'data/network.json', 'data/meta.json',
  'icons/icon-180.png', 'icons/icon-192.png', 'icons/icon-512.png', 'icons/owl.jpg'];
const TILES = 'trail-tiles-v1', MAX_TILES = 2500;
self.addEventListener('install', e => e.waitUntil(caches.open(V).then(c => c.addAll(SHELL)).then(() => self.skipWaiting())));
self.addEventListener('activate', e => e.waitUntil(caches.keys().then(ks => Promise.all(ks.filter(k => k !== V && k !== TILES).map(k => caches.delete(k)))).then(() => self.clients.claim())));
async function trim() { const c = await caches.open(TILES); const k = await c.keys(); for (let i = 0; i < k.length - MAX_TILES; i++) await c.delete(k[i]); }
self.addEventListener('fetch', e => {
  const u = new URL(e.request.url);
  if (e.request.method !== 'GET') return;
  if (u.origin === location.origin) {
    // app shell + trail data: network first (so updates arrive), cache fallback when offline on the trail
    e.respondWith(fetch(e.request).then(r => { if (r.ok) { const cl = r.clone(); caches.open(V).then(c => c.put(e.request, cl)); } return r; }).catch(() => caches.match(e.request, { ignoreSearch: true }).then(r => r || caches.match('index.html'))));
    return;
  }
  if (/arcgisonline\.com|elevation-tiles-prod|openfreemap\.org/.test(u.host + u.pathname)) {
    e.respondWith(caches.open(TILES).then(async c => { const hit = await c.match(e.request); if (hit) return hit; const r = await fetch(e.request); if (r.ok || r.type === 'opaque') { c.put(e.request, r.clone()); trim(); } return r; }));
  }
});
