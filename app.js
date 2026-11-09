'use strict';
// Ardagh Bluffs Trails PWA. Data: OSM (Overpass) classified against the City of Barrie trail map; DEM: AWS Terrarium.
const C = { // colours sampled from the City of Barrie "Ardagh Bluffs Trails" map (Nov 27 2014 edition)
  ring: '#FCFC00', west: '#0036D8', central: '#FC00FC', east: '#FC7E00', emms: '#7200E4', other: '#EDE8DC'
};
const NAMES = { ring: 'Ardagh Ring Trail', west: 'West Creek Trail', central: 'Central Creek Trail', east: 'East Creek Trail', emms: 'Emms / Bloom Walkway' };
const SIGN_KM = { west: 2.2, ring: 5, central: 1.9, east: 1.3 };
const WALK_KMH = 4.5;
const $ = s => document.querySelector(s);
const LS = { get: (k, d) => { try { return JSON.parse(localStorage.getItem(k)) ?? d } catch { return d } }, set: (k, v) => localStorage.setItem(k, JSON.stringify(v)) };
const ESRI = 'https://server.arcgisonline.com/ArcGIS/rest/services/';
const DEM = 'https://s3.amazonaws.com/elevation-tiles-prod/terrarium/{z}/{x}/{y}.png';

let map, NET, TRAILS, POINTS, state = { wps: LS.get('tm.wps', []), route: null, editing: false, follow: false, nav: false, fix: null, heading: null, home: LS.get('tm.home', null), approach: null, three: true };

function toast(msg, ms = 2600) { const t = $('#toast'); t.textContent = msg; t.classList.remove('hidden'); clearTimeout(toast.t); toast.t = setTimeout(() => t.classList.add('hidden'), ms); }
function ask(text, { input = null, ok = 'OK' } = {}) {
  return new Promise(res => {
    $('#dlgText').textContent = text; const inp = $('#dlgInput'); inp.classList.toggle('hidden', input === null); if (input !== null) inp.value = input;
    $('#dlgYes').textContent = ok; $('#dialog').classList.remove('hidden'); if (input !== null) setTimeout(() => inp.focus(), 50);
    const done = v => { $('#dialog').classList.add('hidden'); $('#dlgYes').onclick = $('#dlgNo').onclick = null; res(v); };
    $('#dlgYes').onclick = () => done(input !== null ? inp.value.trim() : true); $('#dlgNo').onclick = () => done(null);
  });
}

// ---------- geometry ----------
const R = 6371008.8, rad = Math.PI / 180;
function hav(a, b) { const dLa = (b[1] - a[1]) * rad, dLo = (b[0] - a[0]) * rad; const s = Math.sin(dLa / 2) ** 2 + Math.cos(a[1] * rad) * Math.cos(b[1] * rad) * Math.sin(dLo / 2) ** 2; return 2 * R * Math.asin(Math.sqrt(s)); }
function fmtKm(m) { return m < 1000 ? Math.round(m) + ' m' : (m / 1000).toFixed(m < 10000 ? 1 : 0) + ' km'; }
function fmtTime(min) { min = Math.round(min); return min < 60 ? min + ' min' : Math.floor(min / 60) + 'h ' + String(min % 60).padStart(2, '0') + 'm'; }

// ---------- routing graph ----------
function buildGraph(net) {
  const n = net.nodes.length, deg = new Uint32Array(n + 1);
  for (const e of net.edges) { deg[e[0]]++; deg[e[1]]++; }
  const off = new Uint32Array(n + 1); for (let i = 0; i < n; i++) off[i + 1] = off[i] + deg[i];
  const fill = off.slice(0, n), to = new Uint32Array(off[n]), len = new Float32Array(off[n]), cost = new Float32Array(off[n]), kind = new Uint8Array(off[n]);
  const pen = [1, 1.08, 1.6];
  for (const [a, b, k] of net.edges) {
    const L = hav(net.nodes[a], net.nodes[b]);
    for (const [x, y] of [[a, b], [b, a]]) { const j = fill[x]++; to[j] = y; len[j] = L; cost[j] = L * pen[k]; kind[j] = k; }
  }
  const trailNode = new Uint8Array(n), offNode = new Uint8Array(n);
  for (const [a, b, k] of net.edges) { if (k === 0) trailNode[a] = trailNode[b] = 1; if (k < 2) offNode[a] = offNode[b] = 1; }
  // spatial grid ~ 60 m
  const grid = new Map(), G = 0.0007;
  net.nodes.forEach((p, i) => { const key = Math.floor(p[0] / G) + ',' + Math.floor(p[1] / G); (grid.get(key) || grid.set(key, []).get(key)).push(i); });
  return { n, off, to, len, cost, kind, trailNode, offNode, grid, G, nodes: net.nodes };
}
function nearest(g, ll, maxM, filter) {
  const gx = Math.floor(ll[0] / g.G), gy = Math.floor(ll[1] / g.G), rr = Math.ceil(maxM / 50) + 1; let best = -1, bd = maxM;
  for (let dx = -rr; dx <= rr; dx++) for (let dy = -rr; dy <= rr; dy++) {
    const c = g.grid.get((gx + dx) + ',' + (gy + dy)); if (!c) continue;
    for (const i of c) { if (filter && !filter(i)) continue; const d = hav(ll, g.nodes[i]); if (d < bd) { bd = d; best = i; } }
  }
  return best < 0 ? null : { i: best, d: bd };
}
class Heap { constructor() { this.k = []; this.v = []; } push(k, v) { const K = this.k, V = this.v; let i = K.length; K.push(k); V.push(v); while (i > 0) { const p = (i - 1) >> 1; if (K[p] <= k) break; K[i] = K[p]; V[i] = V[p]; i = p; } K[i] = k; V[i] = v; }
  pop() { const K = this.k, V = this.v, top = V[0], lk = K.pop(), lv = V.pop(); if (K.length) { let i = 0; const n = K.length; while (true) { let l = 2 * i + 1, r = l + 1, m = i; let mk = lk; if (l < n && K[l] < mk) { m = l; mk = K[l]; } if (r < n && K[r] < mk) m = r; if (m === i) break; K[i] = K[m]; V[i] = V[m]; i = m; } K[i] = lk; V[i] = lv; } return top; } get size() { return this.k.length; } }
function dijkstra(g, src, isTarget) {
  const dist = new Float64Array(g.n).fill(Infinity), prev = new Int32Array(g.n).fill(-1), h = new Heap(); dist[src] = 0; h.push(0, src);
  while (h.size) { const u = h.pop(); if (isTarget(u)) return { u, prev }; const du = dist[u];
    for (let j = g.off[u]; j < g.off[u + 1]; j++) { const v = g.to[j], nd = du + g.cost[j]; if (nd < dist[v]) { dist[v] = nd; prev[v] = u; h.push(nd, v); } } }
  return null;
}
function path(g, a, b) { if (a === b) return [a]; const r = dijkstra(g, a, u => u === b); if (!r) return null; const p = []; for (let u = b; u !== -1; u = r.prev[u]) p.push(u); return p.reverse(); }
function stats(g, ids) {
  let d = 0, gain = 0, loss = 0; const coords = ids.map(i => g.nodes[i]);
  for (let i = 1; i < coords.length; i++) d += hav(coords[i - 1], coords[i]);
  // elevation gain with 2 m hysteresis to ignore DEM noise
  let ref = coords.length ? coords[0][2] : 0;
  for (const c of coords) { const dz = c[2] - ref; if (dz >= 2) { gain += dz; ref = c[2]; } else if (dz <= -2) { loss -= dz; ref = c[2]; } }
  const min = d / 1000 / WALK_KMH * 60 + gain / 10; // Naismith-style: +1 min per 10 m of climb
  const diff = (gain < 60 && d < 4000) ? 'Easy' : (gain < 180 && d < 10000) ? 'Moderate' : 'Hard';
  return { d, gain, loss, min, diff, coords };
}

// ---------- map ----------
function style() {
  return {
    version: 8, glyphs: 'https://tiles.openfreemap.org/fonts/{fontstack}/{range}.pbf',
    sources: {
      sat: { type: 'raster', tiles: [ESRI + 'World_Imagery/MapServer/tile/{z}/{y}/{x}'], tileSize: 256, maxzoom: 19, attribution: 'Imagery © Esri, Maxar, Earthstar Geographics' },
      ref: { type: 'raster', tiles: [ESRI + 'Reference/World_Transportation/MapServer/tile/{z}/{y}/{x}'], tileSize: 256, maxzoom: 19, attribution: 'Labels © Esri' },
      dem: { type: 'raster-dem', tiles: [DEM], encoding: 'terrarium', tileSize: 256, maxzoom: 15, attribution: 'Terrain: Mapzen/AWS Terrain Tiles' },
      hs: { type: 'raster-dem', tiles: [DEM], encoding: 'terrarium', tileSize: 256, maxzoom: 15 },
      trails: { type: 'geojson', data: 'data/trails.geojson', attribution: '© OpenStreetMap contributors · trail colours: City of Barrie' },
      areas: { type: 'geojson', data: 'data/areas.geojson' },
      pts: { type: 'geojson', data: 'data/points.geojson' },
      route: { type: 'geojson', data: fc([]) }, approach: { type: 'geojson', data: fc([]) }, wps: { type: 'geojson', data: fc([]) }, hl: { type: 'geojson', data: fc([]) }
    },
    sky: { 'sky-color': '#8fb8e8', 'horizon-color': '#dfe9f3', 'fog-color': '#dfe9f3', 'sky-horizon-blend': .6, 'horizon-fog-blend': .6, 'fog-ground-blend': .8 },
    layers: [
      { id: 'bg', type: 'background', paint: { 'background-color': '#e9e6dc' } },
      { id: 'sat', type: 'raster', source: 'sat', paint: { 'raster-saturation': -.05, 'raster-contrast': .05 } },
      { id: 'hill', type: 'hillshade', source: 'hs', paint: { 'hillshade-exaggeration': .45, 'hillshade-shadow-color': '#1d2a20', 'hillshade-highlight-color': '#fffbe8' } },
      { id: 'ref', type: 'raster', source: 'ref', paint: { 'raster-opacity': .85 } },
      { id: 'area-line', type: 'line', source: 'areas', filter: ['==', ['get', 'big'], true], paint: { 'line-color': '#9be27a', 'line-width': 1.5, 'line-opacity': .55, 'line-dasharray': [3, 2] } },
      { id: 'route-halo', type: 'line', source: 'route', layout: { 'line-cap': 'round', 'line-join': 'round' }, paint: { 'line-color': '#ffffff', 'line-width': 16, 'line-opacity': .45, 'line-blur': 2 } },
      { id: 'hl', type: 'line', source: 'hl', layout: { 'line-cap': 'round', 'line-join': 'round' }, paint: { 'line-color': '#fff', 'line-width': 14, 'line-opacity': .5, 'line-blur': 3 } },
      { id: 'other', type: 'line', source: 'trails', filter: ['==', ['get', 'cls'], 'other'], layout: { 'line-cap': 'round', 'line-join': 'round' }, paint: { 'line-color': C.other, 'line-width': ['interpolate', ['linear'], ['zoom'], 13, .6, 17, 2.2], 'line-opacity': .8 } },
      { id: 'main-case', type: 'line', source: 'trails', filter: ['all', ['!=', ['get', 'cls'], 'other'], ['!', ['get', 'minor']]], layout: { 'line-cap': 'round', 'line-join': 'round' }, paint: { 'line-color': 'rgba(0,0,0,.55)', 'line-width': ['interpolate', ['linear'], ['zoom'], 13, 3, 17, 8] } },
      { id: 'main', type: 'line', source: 'trails', filter: ['all', ['!=', ['get', 'cls'], 'other'], ['!', ['get', 'minor']]], layout: { 'line-cap': 'round', 'line-join': 'round' }, paint: { 'line-color': ['match', ['get', 'cls'], 'ring', C.ring, 'west', C.west, 'central', C.central, 'east', C.east, 'emms', C.emms, '#fff'], 'line-width': ['interpolate', ['linear'], ['zoom'], 13, 1.8, 17, 5] } },
      { id: 'minor', type: 'line', source: 'trails', filter: ['all', ['!=', ['get', 'cls'], 'other'], ['get', 'minor']], layout: { 'line-cap': 'round', 'line-join': 'round' }, paint: { 'line-color': ['match', ['get', 'cls'], 'ring', C.ring, 'west', C.west, 'central', C.central, 'east', C.east, 'emms', C.emms, '#fff'], 'line-width': ['interpolate', ['linear'], ['zoom'], 13, 1.6, 17, 4], 'line-dasharray': [0.1, 1.8] } },
      { id: 'approach', type: 'line', source: 'approach', layout: { 'line-cap': 'round', 'line-join': 'round' }, paint: { 'line-color': '#fff', 'line-width': 5, 'line-dasharray': [0.1, 2] } },
      { id: 'approach2', type: 'line', source: 'approach', layout: { 'line-cap': 'round' }, paint: { 'line-color': '#0a84ff', 'line-width': 3.5, 'line-dasharray': [2, 1.5] } },
      { id: 'route', type: 'line', source: 'route', layout: { 'line-cap': 'round', 'line-join': 'round' }, paint: { 'line-color': '#0a84ff', 'line-width': ['interpolate', ['linear'], ['zoom'], 13, 2, 17, 4], 'line-dasharray': [1.5, 1] } },
      { id: 'junction', type: 'circle', source: 'pts', minzoom: 14.5, filter: ['==', ['get', 'kind'], 'junction'], paint: { 'circle-radius': ['interpolate', ['linear'], ['zoom'], 14.5, 2, 18, 4.5], 'circle-color': '#fff', 'circle-stroke-color': '#222', 'circle-stroke-width': 1 } },
      { id: 'access', type: 'circle', source: 'pts', filter: ['==', ['get', 'kind'], 'access'], paint: { 'circle-radius': 4.5, 'circle-color': '#111', 'circle-stroke-color': '#fff', 'circle-stroke-width': 1.5 } },
      { id: 'wps', type: 'circle', source: 'wps', paint: { 'circle-radius': 8, 'circle-color': ['match', ['get', 'role'], 'start', '#34c759', 'end', '#ff3b30', '#0a84ff'], 'circle-stroke-color': '#fff', 'circle-stroke-width': 3 } },
      { id: 'wps-n', type: 'symbol', source: 'wps', layout: { 'text-field': ['get', 'n'], 'text-font': ['Noto Sans Bold'], 'text-size': 10, 'text-allow-overlap': true }, paint: { 'text-color': '#fff' } },
      { id: 'post', type: 'symbol', source: 'pts', minzoom: 14.6, filter: ['==', ['get', 'kind'], 'post'], layout: { 'icon-image': 'post', 'icon-size': ['interpolate', ['linear'], ['zoom'], 14.6, .55, 17, .9], 'icon-allow-overlap': true, 'text-field': ['to-string', ['get', 'num']], 'text-font': ['Noto Sans Bold'], 'text-size': ['interpolate', ['linear'], ['zoom'], 14.6, 8, 17, 12], 'text-allow-overlap': true } , paint: { 'text-color': '#000' } },
      { id: 'trailhead', type: 'symbol', source: 'pts', filter: ['==', ['get', 'kind'], 'trailhead'], layout: { 'icon-image': 'star', 'icon-size': ['interpolate', ['linear'], ['zoom'], 13, .45, 17, .8], 'icon-allow-overlap': true } },
      { id: 'parking', type: 'symbol', source: 'pts', filter: ['==', ['get', 'kind'], 'parking'], layout: { 'icon-image': 'parking', 'icon-size': .7, 'icon-allow-overlap': true } },
      { id: 'labels', type: 'symbol', source: 'pts', filter: ['in', ['get', 'kind'], ['literal', ['label', 'place']]], layout: { 'icon-image': ['case', ['==', ['get', 'kind'], 'label'], 'tree', ''], 'icon-size': .55, 'icon-anchor': 'bottom', 'text-field': ['get', 'name'], 'text-font': ['Noto Sans Bold'], 'text-size': ['case', ['get', 'big'], 14, 12], 'text-anchor': 'top', 'text-offset': [0, .2], 'text-max-width': 8 }, paint: { 'text-color': '#fff', 'text-halo-color': 'rgba(0,0,0,.75)', 'text-halo-width': 1.6 } }
    ]
  };
}
const fc = f => ({ type: 'FeatureCollection', features: f });
function canvasImg(sz, draw) { const c = document.createElement('canvas'); c.width = c.height = sz; const x = c.getContext('2d'); draw(x, sz); return { width: sz, height: sz, data: new Uint8Array(x.getImageData(0, 0, sz, sz).data.buffer) }; }
function addIcons() {
  map.addImage('post', canvasImg(48, (x, s) => { x.beginPath(); x.arc(s / 2, s / 2, s / 2 - 4, 0, 7); x.fillStyle = '#fff'; x.fill(); x.lineWidth = 4; x.strokeStyle = '#000'; x.stroke(); }), { pixelRatio: 2 });
  map.addImage('star', canvasImg(64, (x, s) => { x.beginPath(); for (let i = 0; i < 10; i++) { const r = i % 2 ? s * .2 : s * .46, a = -Math.PI / 2 + i * Math.PI / 5; x.lineTo(s / 2 + r * Math.cos(a), s / 2 + r * Math.sin(a)); } x.closePath(); x.fillStyle = '#000'; x.fill(); x.lineWidth = 3; x.strokeStyle = '#fff'; x.stroke(); }), { pixelRatio: 2 });
  map.addImage('parking', canvasImg(56, (x, s) => { x.beginPath(); x.arc(s / 2, s / 2, s / 2 - 3, 0, 7); x.fillStyle = '#fff'; x.fill(); x.lineWidth = 4; x.strokeStyle = '#e8351b'; x.stroke(); x.fillStyle = '#e8351b'; x.font = 'bold 32px sans-serif'; x.textAlign = 'center'; x.textBaseline = 'middle'; x.fillText('P', s / 2, s / 2 + 2); }), { pixelRatio: 2 });
  map.addImage('tree', canvasImg(56, (x, s) => { x.beginPath(); x.arc(s / 2, s / 2, s / 2 - 3, 0, 7); x.fillStyle = '#1f7a3a'; x.fill(); x.lineWidth = 3; x.strokeStyle = '#fff'; x.stroke(); x.fillStyle = '#fff'; x.beginPath(); x.moveTo(s / 2, 12); x.lineTo(s / 2 + 11, 32); x.lineTo(s / 2 - 11, 32); x.fill(); x.fillRect(s / 2 - 2, 31, 4, 9); }), { pixelRatio: 2 });
}

async function init() {
  map = new maplibregl.Map({ container: 'map', style: style(), center: [-79.722, 44.351], zoom: 14.6, pitch: 58, bearing: -12, maxPitch: 80, attributionControl: false, hash: false, maxBounds: [[-79.85, 44.28], [-79.6, 44.43]] });
  map.addControl(new maplibregl.AttributionControl({ compact: true }), 'top-left');
  map.on('styleimagemissing', () => {});
  const [net, trails, pts] = await Promise.all(['data/network.json', 'data/trails.geojson', 'data/points.geojson'].map(u => fetch(u).then(r => r.json())));
  NET = buildGraph(net); TRAILS = trails; POINTS = pts;
  map.on('load', () => {
    addIcons(); map.setTerrain({ source: 'dem', exaggeration: 1.5 });
    const b = new maplibregl.LngLatBounds(); trails.features.filter(f => f.properties.cls !== 'other').forEach(f => f.geometry.coordinates.forEach(c => b.extend(c)));
        map.setPadding({ top: 110, bottom: 280, left: 0, right: 40 });
    map.jumpTo({ center: b.getCenter(), zoom: map.cameraForBounds(b, { padding: 10 }).zoom - 0.1, pitch: 52, bearing: -10 });
    document.querySelectorAll('.maplibregl-ctrl-attrib.maplibregl-compact-show').forEach(el => el.classList.remove('maplibregl-compact-show'));
    restore(); bindMap(); window.__ready = true;
  });
  map.on('rotate', () => $('#northIco').style.transform = `rotate(${-map.getBearing()}deg)`);
  map.on('dragstart', () => { if (state.follow && !state.nav) setFollow(false); });
}
function restore() { if (state.wps.length) recompute(); if (state.home) setHome(state.home, false); }

// ---------- interactions ----------
function bindMap() {
  map.on('click', e => {
    if (state.editing) return addWaypoint([e.lngLat.lng, e.lngLat.lat]);
    const f = map.queryRenderedFeatures(e.point, { layers: ['post', 'trailhead', 'parking', 'main', 'minor', 'other'] })[0];
    if (!f) return;
    const p = f.properties; let html;
    if (p.kind === 'post') html = `<b>Trail post ${p.num}</b><br><small>Position from the City of Barrie map, snapped to the trail.</small>`;
    else if (p.kind === 'trailhead') html = '<b>Major trailhead access</b>';
    else if (p.kind === 'parking') html = `<b>${p.name}</b><br><small>Position from the City of Barrie map.</small>`;
    else html = `<b>${p.cls === 'other' ? (p.name || 'Unmarked path') : NAMES[p.cls] + (p.minor ? ' · minor trail' : '')}</b><br><small>${p.cls === 'other' ? 'OpenStreetMap path, not on the City map' : 'City of Barrie trail'} · segment ${fmtKm(p.len)}</small>`;
    new maplibregl.Popup({ closeButton: false, offset: 10 }).setLngLat(e.lngLat).setHTML(html).addTo(map);
  });
  // long-press = set Home (touch) ; right-click on desktop
  let lp = null, start = null;
  const cancel = () => { clearTimeout(lp); lp = null; };
  map.on('touchstart', e => { if (e.points.length !== 1) return cancel(); start = e.point; const ll = e.lngLat; lp = setTimeout(() => { lp = null; askHome([ll.lng, ll.lat]); }, 650); });
  map.on('touchmove', e => { if (lp && start && (Math.abs(e.point.x - start.x) > 8 || Math.abs(e.point.y - start.y) > 8)) cancel(); });
  map.on('touchend', cancel); map.on('movestart', e => { if (e.originalEvent && e.originalEvent.touches && e.originalEvent.touches.length > 1) cancel(); });
  map.on('contextmenu', e => askHome([e.lngLat.lng, e.lngLat.lat]));
}
async function askHome(ll) {
  if (navigator.vibrate) navigator.vibrate(20);
  if (await ask(state.home ? 'Move Home to this spot? It is saved only on this phone.' : 'Set Home here? It is saved only on this phone.', { ok: 'Set Home' })) setHome(ll, true);
}
let homeMarker, entryMarker;
function setHome(ll, save) {
  state.home = ll; if (save) LS.set('tm.home', ll);
  if (!homeMarker) { const el = document.createElement('div'); el.className = 'home'; el.innerHTML = '<i><svg viewBox="0 0 24 24"><path d="M4 11 12 4l8 7v9h-5v-6H9v6H4z"/></svg></i><span>Home</span>'; homeMarker = new maplibregl.Marker({ element: el, anchor: 'top', offset: [0, -17] }); }
  homeMarker.setLngLat(ll).addTo(map); computeApproach();
}
function clearHome() { state.home = null; localStorage.removeItem('tm.home'); homeMarker && homeMarker.remove(); entryMarker && entryMarker.remove(); map.getSource('approach').setData(fc([])); state.approach = null; }
function computeApproach() {
  const s = nearest(NET, state.home, 400); if (!s) { toast('Home is too far from any mapped path or street.'); return; }
  const r = dijkstra(NET, s.i, u => NET.trailNode[u] === 1);
  if (!r) return;
  const ids = []; for (let u = r.u; u !== -1; u = r.prev[u]) ids.push(u); ids.reverse();
  const st = stats(NET, ids); const d = st.d + s.d; const coords = [state.home, ...st.coords.map(c => [c[0], c[1]])];
  state.approach = { ids, d, min: d / 1000 / WALK_KMH * 60, entry: ids[ids.length - 1] };
  map.getSource('approach').setData(fc([{ type: 'Feature', properties: {}, geometry: { type: 'LineString', coordinates: coords } }]));
  const el = document.createElement('div'); el.className = 'entry';
  el.innerHTML = `<i>🥾</i><span><b>Trail Entry</b>${fmtTime(state.approach.min)} · ${fmtKm(d)}</span>`;
  el.onclick = ev => { ev.stopPropagation(); useApproachAsStart(); };
  entryMarker && entryMarker.remove(); entryMarker = new maplibregl.Marker({ element: el, anchor: 'left' }).setLngLat(NET.nodes[state.approach.entry].slice(0, 2)).addTo(map);
}
async function useApproachAsStart() {
  if (await ask(`Start your route from Home? Adds the ${fmtKm(state.approach.d)} walk to the trail entry.`, { ok: 'Start from Home' })) {
    state.wps = [{ i: nearest(NET, state.home, 400).i }, { i: state.approach.entry }]; setEditing(true); recompute(); toast('Now tap trails to extend the route.');
  }
}
function addWaypoint(ll) {
  const s = nearest(NET, ll, 60, i => NET.offNode[i] === 1) || nearest(NET, ll, 40);
  if (!s) return toast('Tap closer to a trail.');
  if (state.wps.length && path(NET, state.wps[state.wps.length - 1].i, s.i) === null) return toast('That point is not connected to your route.');
  state.wps.push({ i: s.i }); recompute();
}
function recompute() {
  LS.set('tm.wps', state.wps);
  const w = state.wps; let ids = [];
  for (let k = 1; k < w.length; k++) { const p = path(NET, w[k - 1].i, w[k].i); if (!p) continue; ids = ids.concat(k > 1 ? p.slice(1) : p); }
  state.route = ids.length > 1 ? { ids, ...stats(NET, ids) } : null;
  map.getSource('route').setData(fc(state.route ? [{ type: 'Feature', properties: {}, geometry: { type: 'LineString', coordinates: state.route.coords.map(c => [c[0], c[1]]) } }] : []));
  map.getSource('wps').setData(fc(w.map((p, k) => ({ type: 'Feature', properties: { n: String(k + 1), role: k === 0 ? 'start' : (k === w.length - 1 && w.length > 1 ? 'end' : 'via') }, geometry: { type: 'Point', coordinates: NET.nodes[p.i].slice(0, 2) } }))));
  const r = state.route;
  $('#stDist').textContent = r ? fmtKm(r.d) : '—'; $('#stGain').textContent = r ? Math.round(r.gain) + ' m' : '—';
  $('#stTime').textContent = r ? fmtTime(r.min) : '—'; $('#stDiff').textContent = r ? r.diff : '—';
  $('#btnStart').disabled = !r; $('#startSub').textContent = r ? 'Follow this custom route' : (w.length === 1 ? 'Add another point' : 'Build a route first');
  $('#rbHint').textContent = state.editing ? (w.length ? `${w.length} point${w.length > 1 ? 's' : ''} · tap the map to add more` : 'Tap a trail to set the start') : 'Combine connected trails to create your own route';
}
function setEditing(on) { state.editing = on; $('#btnEdit').classList.toggle('on', on); $('#btnEdit span').textContent = on ? 'Done' : 'Edit Route'; recompute(); if (on) toast(state.wps.length ? 'Tap the map to add points.' : 'Tap a trail to set your start point.'); }

// ---------- GPS ----------
let meMarker, watchId = null;
function startGPS() {
  if (!('geolocation' in navigator)) return gpsUI('err', 'GPS unavailable', '');
  if (watchId !== null) return;
  gpsUI('wait', 'Connecting GPS…', '');
  watchId = navigator.geolocation.watchPosition(onPos, err => { gpsUI('err', err.code === 1 ? 'GPS permission denied' : 'GPS signal lost', err.code === 1 ? 'Allow location in Settings › Safari' : 'retrying…'); if (err.code === 1) { navigator.geolocation.clearWatch(watchId); watchId = null; } }, { enableHighAccuracy: true, maximumAge: 2000, timeout: 20000 });
}
function gpsUI(cls, t, s) { const p = $('#gpsPill'); p.className = 'pill glass ' + cls; $('#gpsTxt').textContent = t; $('#gpsAcc').textContent = s; }
function onPos(pos) {
  const c = pos.coords; state.fix = [c.longitude, c.latitude, c.accuracy];
  if (c.heading != null && !isNaN(c.heading) && c.speed > 0.5) state.heading = c.heading;
  gpsUI('ok', 'GPS Connected', `± ${Math.round(c.accuracy)} m accuracy`);
  if (!meMarker) { const el = document.createElement('div'); el.className = 'me'; el.innerHTML = '<div class="h"></div><div class="c"></div>'; meMarker = new maplibregl.Marker({ element: el, rotationAlignment: 'map', pitchAlignment: 'map' }); meMarker.setLngLat(state.fix.slice(0, 2)).addTo(map); }
  meMarker.setLngLat(state.fix.slice(0, 2)); updateHeading();
  if (state.follow) map.easeTo({ center: state.fix.slice(0, 2), bearing: state.nav && state.heading != null ? state.heading : map.getBearing(), duration: 600, ...(state.nav ? { zoom: Math.max(map.getZoom(), 16.8), pitch: 62 } : {}) });
  if (state.nav) navUpdate();
}
function updateHeading() { const h = document.querySelector('.me .h'); if (!h) return; h.style.display = state.heading == null ? 'none' : ''; if (state.heading != null) h.style.transform = `rotate(${state.heading}deg)`; }
function onOrient(e) { const h = e.webkitCompassHeading != null ? e.webkitCompassHeading : (e.absolute && e.alpha != null ? 360 - e.alpha : null); if (h != null) { state.heading = h; updateHeading(); } }
async function enableCompass() {
  try { if (typeof DeviceOrientationEvent !== 'undefined' && DeviceOrientationEvent.requestPermission) { if (await DeviceOrientationEvent.requestPermission() !== 'granted') return; } window.addEventListener('deviceorientation', onOrient, true); window.addEventListener('deviceorientationabsolute', onOrient, true); } catch { }
}
function setFollow(on) { state.follow = on; $('#btnLocate').classList.toggle('on', on); if (on && state.fix) map.easeTo({ center: state.fix.slice(0, 2), zoom: Math.max(map.getZoom(), 16), duration: 700 }); }
function navUpdate() {
  const r = state.route; if (!r || !state.fix) return; const me = state.fix; let bi = 0, bd = Infinity;
  r.coords.forEach((c, i) => { const d = hav(me, c); if (d < bd) { bd = d; bi = i; } });
  let rem = 0; for (let i = bi + 1; i < r.coords.length; i++) rem += hav(r.coords[i - 1], r.coords[i]);
  const b = $('#navBanner'); b.classList.remove('hidden');
  b.textContent = bd > 40 ? `Off route · ${Math.round(bd)} m away` : (rem < 25 ? 'You have arrived 🎉' : `${fmtKm(rem)} to go · ${fmtTime(rem / 1000 / WALK_KMH * 60)}`);
}
function toggleNav() {
  if (state.nav) { state.nav = false; $('#navBanner').classList.add('hidden'); $('#btnStart b').textContent = 'Start Navigation'; $('#sheet').classList.remove('min'); setFollow(false); map.easeTo({ pitch: 58, duration: 600 }); return; }
  if (!state.route) return; startGPS(); enableCompass(); state.nav = true; setEditing(false); setFollow(true); $('#btnStart b').textContent = 'Stop Navigation'; $('#sheet').classList.add('min');
  if (!state.fix) toast('Waiting for GPS…'); else navUpdate();
  if (!state.fix) map.fitBounds(bbox(state.route.coords), { padding: 80, pitch: 60 });
}
function bbox(cs) { const b = new maplibregl.LngLatBounds(); cs.forEach(c => b.extend([c[0], c[1]])); return b; }

// ---------- panels ----------
function legendSVG(cls, kind) {
  const c = C[cls] || '#888';
  const line = (dash) => `<line x1="4" y1="11" x2="106" y2="11" stroke="#333" stroke-width="7" ${dash}/><line x1="4" y1="11" x2="106" y2="11" stroke="${c}" stroke-width="4.5" ${dash}/>`;
  if (kind === 'minor') return `<svg viewBox="0 0 110 22"><line x1="4" y1="11" x2="106" y2="11" stroke="#222" stroke-width="2.6" stroke-dasharray="1 3" stroke-linecap="round"/><path d="M55 5 61 16H49z" fill="#000"/></svg>`;
  const mark = cls === 'ring' ? `<circle cx="55" cy="11" r="5.5" fill="${c}" stroke="#333" stroke-width="1.5"/>` : `<rect x="49.5" y="5.5" width="11" height="11" fill="${c}" stroke="#333" stroke-width="1.5"/>`;
  if (cls === 'other') return `<svg viewBox="0 0 110 22"><line x1="4" y1="11" x2="106" y2="11" stroke="#bbb" stroke-width="3"/></svg>`;
  return `<svg viewBox="0 0 110 22">${line('')}${mark}</svg>`;
}
function legendHTML() {
  const rows = [
    ['<svg viewBox="0 0 110 22"><circle cx="55" cy="11" r="9" fill="#fff" stroke="#000" stroke-width="2.5"/><text x="55" y="15" font-size="10" text-anchor="middle" font-weight="700">22</text></svg>', 'Trail post location'],
    ['<svg viewBox="0 0 110 22"><path d="M55 1l2.9 6.2 6.6.7-5 4.5 1.4 6.6L55 15.6l-5.9 3.4 1.4-6.6-5-4.5 6.6-.7z" fill="#000"/></svg>', 'Major trail head access'],
    ['<svg viewBox="0 0 110 22"><circle cx="55" cy="11" r="4.5" fill="#000"/></svg>', 'Minor trail access'],
    [legendSVG('ring'), 'Ardagh Ring Trail'], [legendSVG('west'), 'West Creek Trail'], [legendSVG('central'), 'Central Creek Trail'],
    [legendSVG('east'), 'East Creek Trail'], [legendSVG('emms'), 'Emms / Bloom Walkway'], [legendSVG('', 'minor'), 'Minor trails <small>(by colour)</small>']];
  return rows.map(([s, t]) => `<div class="lg">${s}<span>${t}</span></div>`).join('') +
    `<div class="lg" style="text-transform:none;font-weight:500;color:#555">${legendSVG('other')}<span>Other paths (OpenStreetMap, not on the City map)</span></div>`;
}
function trailLen(cls) { return TRAILS.features.filter(f => f.properties.cls === cls && !f.properties.minor).reduce((s, f) => s + f.properties.len, 0); }
function openPanel(tab) {
  document.querySelectorAll('#tabs button').forEach(b => b.classList.toggle('on', b.dataset.tab === tab));
  if (tab === 'map') { $('#panel').classList.add('hidden'); return; }
  $('#panel').classList.remove('hidden'); const body = $('#pnBody');
  if (tab === 'trails') {
    $('#pnTitle').textContent = 'Trails';
    body.innerHTML = ['ring', 'west', 'central', 'east'].map(c => `<div class="card">${legendSVG(c).replace('viewBox', 'style="width:60px;flex:0 0 60px" viewBox')}<div class="meta"><b>${NAMES[c]}</b><span>Mapped ${fmtKm(trailLen(c))} · City sign ${SIGN_KM[c]} km</span></div><button class="go" data-show="${c}">Show</button></div>`).join('') +
      `<p class="note">Colours and trail names follow the City of Barrie Ardagh Bluffs trail map. Trail lines come from OpenStreetMap; each unnamed path was matched to the City map's colours by overlaying the two (≈2 m median fit). The Emms / Bloom Walkway is in the City legend but no path carries that name in OpenStreetMap yet, so it is not drawn. Trails are not maintained in winter.</p>`;
    body.querySelectorAll('[data-show]').forEach(b => b.onclick = () => showTrail(b.dataset.show));
  } else if (tab === 'saved') {
    $('#pnTitle').textContent = 'Saved routes'; const list = LS.get('tm.routes', []);
    body.innerHTML = list.length ? list.map((r, k) => `<div class="card"><div class="meta"><b>${esc(r.name)}</b><span>${fmtKm(r.d)} · ${Math.round(r.gain)} m gain · ${fmtTime(r.min)} · ${r.diff}</span></div><button class="go" data-load="${k}">Open</button><button class="go danger" data-del="${k}">✕</button></div>`).join('') : '<p class="note">No saved routes yet. Build one with Edit Route, then use ••• › Save route.</p>';
    body.querySelectorAll('[data-load]').forEach(b => b.onclick = () => { const r = list[+b.dataset.load]; state.wps = r.wps; recompute(); openPanel('map'); map.fitBounds(bbox(state.route.coords), { padding: { top: 140, bottom: 320, left: 40, right: 70 } }); });
    body.querySelectorAll('[data-del]').forEach(b => b.onclick = async () => { if (await ask('Delete this saved route?', { ok: 'Delete' })) { list.splice(+b.dataset.del, 1); LS.set('tm.routes', list); openPanel('saved'); } });
  } else {
    $('#pnTitle').textContent = 'More';
    body.innerHTML = `<h3>Legend</h3>${legendHTML()}
      <h3>Home</h3><p class="note">${state.home ? 'Home is set on this phone. Long-press anywhere on the map to move it.' : 'Long-press on the map at your home to set it. It is stored only on this phone and shows the walk to the nearest trail entry.'}</p>${state.home ? '<button class="go" id="clrHome">Clear Home</button>' : ''}
      <h3>How numbers are worked out</h3><p class="note">Distance is measured along the route. Elevation gain is sampled from the AWS Terrain Tiles DEM at every path node (climbs under 2 m are ignored as noise). Est. time = distance at ${WALK_KMH} km/h + 1 min per 10 m of climb. Difficulty: Easy under 4 km and 60 m gain, Moderate under 10 km and 180 m, otherwise Hard.</p>
      <h3>Sources</h3><p class="note">Trails © OpenStreetMap contributors (ODbL), downloaded ${META.built || ''}. Trail colours, posts and trailheads: City of Barrie, Ardagh Bluffs Trails map (Nov 27 2014). Trail posts and trailheads are placed from that map and snapped to the nearest trail, so treat them as approximate (± 20 m). Imagery © Esri, Maxar, Earthstar Geographics. Terrain: Mapzen / AWS Terrain Tiles. Map engine: MapLibre GL JS.</p>`;
    const ch = $('#clrHome'); if (ch) ch.onclick = () => { clearHome(); openPanel('more'); };
  }
}
let META = {};
const esc = s => String(s).replace(/[&<>"]/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]));
function showTrail(cls) {
  const fs = TRAILS.features.filter(f => f.properties.cls === cls);
  map.getSource('hl').setData(fc(fs)); openPanel('map'); map.fitBounds(bbox(fs.flatMap(f => f.geometry.coordinates)), { padding: { top: 150, bottom: 320, left: 40, right: 70 }, pitch: 55 });
  setTimeout(() => map.getSource('hl').setData(fc([])), 6000);
}
function filterPanel() {
  $('#panel').classList.remove('hidden'); $('#pnTitle').textContent = 'Show on map';
  const vis = LS.get('tm.filter', {});
  const items = [['ring', 'Ardagh Ring Trail'], ['west', 'West Creek Trail'], ['central', 'Central Creek Trail'], ['east', 'East Creek Trail'], ['minor', 'Minor trails (dotted)'], ['other', 'Other paths (OSM)'], ['posts', 'Trail posts'], ['junction', 'Junction dots']];
  $('#pnBody').innerHTML = items.map(([k, t]) => `<label class="card"><input type="checkbox" data-f="${k}" ${vis[k] === false ? '' : 'checked'}><div class="meta"><b>${t}</b></div></label>`).join('');
  $('#pnBody').querySelectorAll('[data-f]').forEach(i => i.onchange = () => { vis[i.dataset.f] = i.checked; LS.set('tm.filter', vis); applyFilter(); });
}
function applyFilter() {
  const v = LS.get('tm.filter', {}); const on = k => v[k] !== false;
  const cls = ['ring', 'west', 'central', 'east', 'emms'].filter(on);
  map.setFilter('main', ['all', ['in', ['get', 'cls'], ['literal', cls]], ['!', ['get', 'minor']]]);
  map.setFilter('main-case', ['all', ['in', ['get', 'cls'], ['literal', cls]], ['!', ['get', 'minor']]]);
  map.setFilter('minor', ['all', ['in', ['get', 'cls'], ['literal', on('minor') ? cls : []]], ['get', 'minor']]);
  map.setLayoutProperty('other', 'visibility', on('other') ? 'visible' : 'none');
  map.setLayoutProperty('post', 'visibility', on('posts') ? 'visible' : 'none');
  map.setLayoutProperty('junction', 'visibility', on('junction') ? 'visible' : 'none');
}
function gpx(r) {
  const pts = r.coords.map(c => `<trkpt lat="${c[1]}" lon="${c[0]}"><ele>${c[2]}</ele></trkpt>`).join('');
  const blob = new Blob([`<?xml version="1.0"?><gpx version="1.1" creator="Ardagh Trails" xmlns="http://www.topografix.com/GPX/1/1"><trk><name>Ardagh route</name><trkseg>${pts}</trkseg></trk></gpx>`], { type: 'application/gpx+xml' });
  const a = document.createElement('a'); a.href = URL.createObjectURL(blob); a.download = 'ardagh-route.gpx'; a.click();
}

// ---------- UI wiring ----------
function wire() {
  $('#btnEdit').onclick = () => setEditing(!state.editing);
  $('#grab').onclick = () => $('#sheet').classList.toggle('min');
  $('#btnStart').onclick = toggleNav;
  $('#btnMore').onclick = e => { e.stopPropagation(); $('#moreMenu').classList.toggle('hidden'); };
  $('#moreMenu').onclick = async e => {
    const a = e.target.dataset.a; if (!a) return; $('#moreMenu').classList.add('hidden');
    if (a === 'undo') { state.wps.pop(); recompute(); }
    if (a === 'loop' && state.wps.length > 1) { state.wps.push({ i: state.wps[0].i }); recompute(); }
    if (a === 'reverse') { state.wps.reverse(); recompute(); }
    if (a === 'clear' && state.wps.length && await ask('Clear this route?', { ok: 'Clear' })) { state.wps = []; recompute(); }
    if (a === 'save') { if (!state.route) return toast('Build a route first.'); const name = await ask('Name this route', { input: 'My Ardagh loop', ok: 'Save' }); if (name) { const l = LS.get('tm.routes', []); l.unshift({ name, wps: state.wps, d: state.route.d, gain: state.route.gain, min: state.route.min, diff: state.route.diff, at: Date.now() }); LS.set('tm.routes', l); toast('Saved.'); } }
    if (a === 'gpx') { if (!state.route) return toast('Build a route first.'); gpx(state.route); }
  };
  document.addEventListener('click', e => { if (!e.target.closest('#moreMenu,#btnMore')) $('#moreMenu').classList.add('hidden'); if (!e.target.closest('#layersPop,#btnLayers')) $('#layersPop').classList.add('hidden'); });
  $('#btnNorth').onclick = () => map.easeTo({ bearing: 0, duration: 500 });
  $('#btnLayers').onclick = () => $('#layersPop').classList.toggle('hidden');
  document.querySelectorAll('[name=base]').forEach(r => r.onchange = () => { const sat = r.value === 'sat' && r.checked; map.setLayoutProperty('sat', 'visibility', sat ? 'visible' : 'none'); map.setPaintProperty('hill', 'hillshade-exaggeration', sat ? .45 : .8); });
  $('#optLabels').onchange = e => map.setLayoutProperty('ref', 'visibility', e.target.checked ? 'visible' : 'none');
  $('#optHill').onchange = e => map.setLayoutProperty('hill', 'visibility', e.target.checked ? 'visible' : 'none');
  $('#btn3d').onclick = () => { state.three = !state.three; $('#btn3d').classList.toggle('on', state.three); if (state.three) { map.setTerrain({ source: 'dem', exaggeration: 1.5 }); map.easeTo({ pitch: 58, duration: 600 }); } else { map.setTerrain(null); map.easeTo({ pitch: 0, duration: 600 }); } };
  $('#btnLocate').onclick = () => { startGPS(); enableCompass(); if (!state.fix) { setFollow(true); toast('Finding you…'); } else setFollow(!state.follow); };
  $('#gpsPill').onclick = () => { startGPS(); enableCompass(); if (state.fix) map.easeTo({ center: state.fix.slice(0, 2), zoom: Math.max(map.getZoom(), 16) }); };
  $('#btnFilter').onclick = filterPanel;
  $('#owlCard').onclick = () => { $('#panel').classList.remove('hidden'); $('#pnTitle').textContent = 'Barred Owl'; $('#pnBody').innerHTML = '<img src="icons/owl.jpg" style="width:100%;border-radius:16px" alt="Barred Owl"><p class="note">The Barred Owl is the bird pictured on the City of Barrie sign at the Ardagh Bluffs trailhead (123 Emms Drive). Photo taken from that sign.</p>'; };
  $('#pnClose').onclick = () => openPanel('map');
  document.querySelectorAll('#tabs button').forEach(b => b.onclick = () => openPanel(b.dataset.tab));
}
wire();
fetch('data/meta.json').then(r => r.json()).then(m => META = m).catch(() => { });
init().then(() => { map.once('idle', () => { try { applyFilter(); } catch { } }); startGPS(); });
if ('serviceWorker' in navigator && location.protocol === 'https:') navigator.serviceWorker.register('sw.js');
