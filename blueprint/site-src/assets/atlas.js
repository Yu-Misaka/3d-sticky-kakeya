'use strict';
// The proof atlas. atlas-view.json carries the cards, the Graphviz layouts of
// every view, the comparison record of every drawn arrow and the witnesses.
(() => {
const loading = document.getElementById('loading');
fetch('atlas-view.json').then(response => {
  if (!response.ok) throw new Error(`the atlas data did not load (${response.status})`);
  return response.json();
}).then(start).catch(error => {
  loading.classList.add('error');
  loading.innerHTML = `The atlas could not start: ${String(error.message || error).replace(/[<&]/g, '')}. Every card is also on <a href="atlas-cards.html">one page</a>.`;
  console.error(error);
});

function start(D) {
const $ = (s, r = document) => r.querySelector(s);
const $$ = (s, r = document) => Array.from(r.querySelectorAll(s));
const esc = s => String(s ?? '').replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
const LAYOUTS = D.layouts;
const BRANCHES = D.views;
const nodes = new Map(D.nodes.map(n => [n.id, n]));
const groups = new Map(D.groups.map(g => [g.id, g]));
const reduceMotion = matchMedia('(prefers-reduced-motion: reduce)').matches;
const narrow = () => matchMedia('(max-width: 860px)').matches;
const FRAME_SHORT_NAMES = { multilinear: 'Multilinear', cinematic: 'Cinematic', radial: 'Radial', incidence: 'Furstenberg', projection: 'Projections', extension: 'Scalar extension' };
const VIEW_SHORT_NAMES = { overview: 'Core proof DAG', scales: 'Wolff infrastructure', plane: 'Plane map', grains: 'Grains', regularity: 'C2 regularity',
  slope: 'Nonsingular slope', projection: 'Twisted projection', cinematic: 'Cinematic', bootstrap: 'Radial bootstrap', reductions: 'Strip reduction', external: 'External', all: 'Whole proof' };
const frameShort = id => FRAME_SHORT_NAMES[id] || (groups.get(id)?.title || id).split(' · ')[0];
const viewShort = id => VIEW_SHORT_NAMES[id] || BRANCHES.find(v => v.id === id)?.title || id;
const DIFFS = ['agree', 'lean-only', 'detail', 'expert-route', 'expert-unknown'];
const DIFF = {
  'agree': { name: 'Agree', title: 'Lean and roadmap agree', text: 'Lean has a path, and the roadmap connects the two nodes, directly or through other roadmap nodes.' },
  'lean-only': { name: 'Lean only', title: 'Lean only', text: 'Lean has a path between two roadmap nodes that the roadmap does not connect. These are the first arrows to review.' },
  'detail': { name: 'Lean detail', title: 'Lean detail', text: 'Lean has a path, and one end is a Lean version that the roadmap does not show.' },
  'expert-route': { name: 'Different route', title: 'Roadmap only · different Lean route', text: 'Both Lean versions are used, but the proof connects them another way.' },
  'expert-unknown': { name: 'Not comparable', title: 'Roadmap only · not comparable', text: 'A node has no Lean match, a version lies outside the root, or two cards share one declaration.' },
};
const ROLE = { proof: 'Lean proof', interface: 'Proposition interface', definition: 'Definition / data', constructor: 'Constructor', axiom: 'Axiom' };
const ROLE_NOTE = {
  interface: 'This declaration defines a proposition. Referencing it does not construct a proof of it.',
  constructor: 'This constructor requires its fields as arguments; its existence does not supply those arguments.',
  proof: 'The proof establishes its own Lean type, including every hypothesis shown there. The correspondence Remark records differences from the expert statement.',
};
const ICON = {
  back: '<svg class="icon" viewBox="0 0 16 16"><path d="M10 3.5 5.5 8l4.5 4.5"/></svg>',
  fwd: '<svg class="icon" viewBox="0 0 16 16"><path d="M6 3.5 10.5 8 6 12.5"/></svg>',
  link: '<svg class="icon" viewBox="0 0 16 16"><path d="M6.8 9.2a3 3 0 0 0 4.2 0l2-2a3 3 0 0 0-4.2-4.2l-.8.8M9.2 6.8a3 3 0 0 0-4.2 0l-2 2a3 3 0 0 0 4.2 4.2l.8-.8"/></svg>',
  hide: '<svg class="icon" viewBox="0 0 16 16"><path d="M3 3.5h10M3 8h6M3 12.5h10M11 6l2 2-2 2"/></svg>',
  chev: '<svg class="icon chev" viewBox="0 0 16 16"><path d="M6 3.5 10.5 8 6 12.5"/></svg>',
};

/* ---------- small renderers ---------- */
function statusParts(s) { if (!s || s === 'unmatched') return { role: null, used: false }; const i = s.indexOf('-'); return { used: s.slice(0, i) === 'used', role: s.slice(i + 1) }; }
function markShape(status, x, y, r = 4.2) {
  const { role, used } = statusParts(status);
  if (!role) return '';
  const c = used ? 'mk used' : 'mk off';
  if (role === 'proof') return `<circle class="${c}" cx="${x}" cy="${y}" r="${r}"/>`;
  if (role === 'interface') { const q = r + .9; return `<path class="${c}" d="M${x} ${y - q}L${x + q} ${y}L${x} ${y + q}L${x - q} ${y}Z"/>`; }
  if (role === 'definition') { const q = r - .5; return `<rect class="${c}" x="${x - q}" y="${y - q}" width="${2 * q}" height="${2 * q}"/>`; }
  const q = r + .6; return `<path class="${c}" d="M${x} ${y - q}L${x + q} ${y + q * .8}L${x - q} ${y + q * .8}Z"/>`;
}
function markIcon(status) {
  if (status === 'group') return '<svg class="mark" width="14" height="14" viewBox="0 0 14 14" aria-hidden="true"><rect class="mk off" x="4" y="1.5" width="8.5" height="8" rx="1.5"/><rect class="mk off" x="1.5" y="4.5" width="8.5" height="8" rx="1.5"/></svg>';
  const inner = status === 'unmatched' ? '<rect class="mk-none" x="1.5" y="1.5" width="11" height="11" rx="2.5"/>' : markShape(status, 7, 7, 4.1);
  return `<svg class="mark" width="14" height="14" viewBox="0 0 14 14" aria-hidden="true">${inner}</svg>`;
}
const swatch = diff => `<svg class="sw" width="28" height="8" viewBox="0 0 28 8" aria-hidden="true"><line class="ln d-${diff}" x1="1" y1="4" x2="27" y2="4"/></svg>`;
const statusLabel = s => D.status[s] || s;
const verStatus = v => (v.reached ? 'used-' : 'unused-') + v.role;
// Witness steps can be private helpers, which have no doc-gen4 page: they link to their source.
function sourceOf(name) {
  const where = D.sources[name]; if (!where) return null;
  const module = D.modules[where[0]], file = module.replace(/\./g, '/') + '.lean' + (where[1] ? '#L' + where[1] : '');
  return module.startsWith('Mathlib.') ? `https://github.com/leanprover-community/mathlib4/blob/${D.mathlib_revision}/${file}` : `${D.repository}/blob/${D.revision}/${file}`;
}
const pathOf = i => (i == null ? [] : D.paths[i].map(([from, to, kind]) => ({ from, to, kind })));
function splitName(name) { const i = name.lastIndexOf('.'); return i < 0 ? ['', name] : [name.slice(0, i + 1), name.slice(i + 1)]; }
function nameOf(key) { if (key.startsWith('group-')) return groups.get(key.slice(6))?.title.split(' · ')[0] || key; const n = nodes.get(key); return n ? n.full_heading || n.heading.join(' ') : key; }
function subOf(key) { if (key.startsWith('group-')) return 'Folded External frame'; const n = nodes.get(key); return n ? (n.expert ? n.title : n.summary.join(' ') || splitName(n.primary)[1]) : ''; }
function membersOf(g) { return D.nodes.filter(n => n.external === g); }

/* ---------- state ---------- */
const state = { layoutId: null, L: null, wholeVariant: 'all', selected: null, hover: null, peek: null,
  hidden: new Set(), history: [], hpos: -1, nodeEls: new Map(), edgeEls: [] };
const hiddenDefaults = id => id.startsWith('all') ? new Set(['expert-unknown']) : new Set();

/* ---------- canvas ---------- */
const wrap = $('#canvas-wrap'), svg = $('#canvas'), world = $('#world');
const L_CL = $('#l-clusters'), L_ED = $('#l-edges'), L_ND = $('#l-nodes');
let cam = { x: 0, y: 0, k: 1 }, camAnim = 0;
$('#markers').innerHTML = DIFFS.map(d => `<marker id="ah-${d}" viewBox="0 0 10 10" refX="9.2" refY="5" markerWidth="${d === 'lean-only' ? 3.4 : 4.6}" markerHeight="${d === 'lean-only' ? 3.4 : 4.6}" orient="auto"><path d="M0 1.2 10 5 0 8.8 2.2 5Z" style="fill: var(--e-${{ 'agree': 'agree', 'lean-only': 'lean', 'detail': 'detail', 'expert-route': 'route', 'expert-unknown': 'unknown' }[d]})"/></marker>`).join('');

function applyCam() {
  world.setAttribute('transform', `translate(${cam.x.toFixed(2)} ${cam.y.toFixed(2)}) scale(${cam.k.toFixed(5)})`);
  svg.style.setProperty('--zs', Math.min(4, Math.max(1, .85 / cam.k)).toFixed(3));
  svg.classList.toggle('lod-low', cam.k < .72);
  svg.classList.toggle('lod-tiny', cam.k < .3);
  $('#zoom-level').textContent = Math.round(cam.k * 100) + '%';
  let g = 24 * cam.k; while (g < 14) g *= 2; while (g > 40) g /= 2;
  wrap.style.backgroundSize = `${g}px ${g}px`;
  wrap.style.backgroundPosition = `${cam.x.toFixed(1)}px ${cam.y.toFixed(1)}px`;
  drawMini();
}
const clampK = k => Math.max(.04, Math.min(2.5, k));
function viewport() {
  const w = wrap.clientWidth; let h = wrap.clientHeight;
  if (narrow()) h -= sheetCover();
  return { w, h: Math.max(140, h) };
}
function sheetCover() {
  // The bottom sheet's resting height, known before its transition ends.
  if (!narrow()) return 0;
  const s = $('#inspector').dataset.sheet;
  return s === 'full' ? innerHeight - 64 : s === 'half' ? innerHeight * .56 : 168;
}
function animateTo(t, ms = 380) {
  cancelAnimationFrame(camAnim);
  if (reduceMotion || ms <= 0) { cam = { ...t }; applyCam(); return; }
  const s = { ...cam }, t0 = performance.now();
  const step = now => {
    const p = Math.min(1, (now - t0) / ms), e = 1 - Math.pow(1 - p, 3);
    cam = { x: s.x + (t.x - s.x) * e, y: s.y + (t.y - s.y) * e, k: s.k * Math.pow(t.k / s.k, e) };
    applyCam(); if (p < 1) camAnim = requestAnimationFrame(step);
  };
  camAnim = requestAnimationFrame(step);
}
function overlayTop() { const o = $('.ov-top').getBoundingClientRect(), w = wrap.getBoundingClientRect(); return Math.max(56, o.bottom - w.top + 14); }
function camFor(b, { maxK = 1, pad = 56, k = null } = {}) {
  const v = viewport();
  const top = overlayTop(); // keep clear of the title overlay
  const kk = k ?? Math.max(.04, Math.min(maxK, (v.w - 2 * pad) / b.w, (v.h - top - pad) / b.h));
  return { k: kk, x: (v.w - b.w * kk) / 2 - b.x * kk, y: top + (v.h - top - b.h * kk) / 2 - b.y * kk };
}
function initialCam() {
  const L = state.L, v = viewport(), top = overlayTop();
  if (state.layoutId.startsWith('all')) { fitAll(0); return; }
  const inner = L.clusters.filter(c => c.id !== 'external');
  if (inner.length > 1) { zoomToCluster(inner[0].id, 0); return; }
  const fit = camFor({ x: 0, y: 0, w: L.w, h: L.h }, { maxK: 1 });
  if (fit.k >= .74) { animateTo(fit, 0); return; }
  const k = .78; animateTo({ k, x: (v.w - L.w * k) / 2, y: top }, 0);
}
function fitAll(ms = 380) { const L = state.L; animateTo(camFor({ x: 0, y: 0, w: L.w, h: L.h }, { maxK: 1 }), ms); }
function boxOf(key, L = state.L) { const b = L.nodes[key]; return b && { x: b[0], y: b[1], w: b[2], h: b[3] }; }
function centreOn(key, { k = null, ms = 380, ifHidden = false } = {}) {
  const b = boxOf(key); if (!b) return;
  if (ifHidden) {
    const v = viewport(), sx = b.x * cam.k + cam.x, sy = b.y * cam.k + cam.y;
    if (sx > 24 && sy > 80 && sx + b.w * cam.k < v.w - 24 && sy + b.h * cam.k < v.h - 24 && cam.k > .42) return;
  }
  const kk = clampK(k ?? Math.max(cam.k, .78));
  const v = viewport(), top = overlayTop() - 20;
  animateTo({ k: kk, x: v.w / 2 - (b.x + b.w / 2) * kk, y: top + (v.h - top) / 2 - (b.y + b.h / 2) * kk }, ms);
}
function zoomAt(k, px, py) { k = clampK(k); const wx = (px - cam.x) / cam.k, wy = (py - cam.y) / cam.k; cam = { k, x: px - wx * k, y: py - wy * k }; applyCam(); }
function zoomBy(f) { const v = viewport(); cancelAnimationFrame(camAnim); const k = clampK(cam.k * f), px = v.w / 2, py = v.h / 2, wx = (px - cam.x) / cam.k, wy = (py - cam.y) / cam.k; animateTo({ k, x: px - wx * k, y: py - wy * k }, 200); }

function nodeSVG(key, [x, y, w, h]) {
  if (key.startsWith('group-')) {
    const g = groups.get(key.slice(6)), n = membersOf(key.slice(6)).length, title = g.title.split(' · ')[0];
    return `<g class="node group g-external" data-node="${key}" tabindex="0" role="button" aria-label="Open the folded frame ${esc(title)}" style="transform: translate(${x}px, ${y}px)"><title>${esc(g.title)}: folded External frame with ${n} Lean nodes. Click to open it.</title>
      <rect class="stack" x="7" y="-6" width="${w - 7}" height="${h}" rx="8"/><rect class="box" x="0" y="0" width="${w - 7}" height="${h}" rx="8"/>
      <text class="hd" x="12" y="26">${esc(title)}</text><text class="sm" x="12" y="44">${n} Lean nodes</text><text class="open" x="${w - 19}" y="${h - 12}" text-anchor="end">Open ↗</text></g>`;
  }
  const n = nodes.get(key);
  let t = `<g class="hg" style="--dy: ${((h - 17 * n.heading.length) / 2 - 8).toFixed(1)}px">`;
  n.heading.forEach((line, i) => { t += `<text class="hd" x="10" y="${21.5 + i * 17}">${esc(line)}</text>`; });
  t += '</g>';
  const sy = 8 + 17 * n.heading.length;
  n.summary.forEach((line, i) => { t += `<text class="sm" x="10" y="${sy + 12.5 + i * 15.5}">${esc(line)}</text>`; });
  const tip = `${n.id} · ${n.paper}: ${n.title}. ${statusLabel(n.status)}.`;
  return `<g class="node g-${n.group}${n.status === 'unmatched' ? ' unmatched' : ''}" data-node="${key}" tabindex="0" role="button" aria-label="${esc(n.heading.join(' ') + ': ' + n.title)}" style="transform: translate(${x}px, ${y}px)"><title>${esc(tip)}</title><rect class="box" width="${w}" height="${h}" rx="6"/>${t}${markShape(n.status, w - 11, 11)}</g>`;
}
function edgeSVG(e, i) {
  const many = e.members && e.members.length > 1;
  const tip = `${D.diff_titles[e.diff]}: ${nameOf(e.from)} → ${nameOf(e.to)}${many ? ` (${e.members.length} folded connections)` : ''}`;
  return `<g class="edge d-${e.diff}" data-i="${i}"><title>${esc(tip)}</title><path class="hit" d="${e.d}"/><path class="line" d="${e.d}" marker-end="url(#ah-${e.diff})"/></g>`;
}
function clusterSVG(c) {
  const outer = c.id === 'external';
  const full = outer ? 'External inputs · opened in Lean' : (groups.get(c.id)?.title || c.id);
  const title = full.length * 8.4 + 32 < c.w ? full : frameShort(c.id);
  return `<g class="cluster${outer ? ' outer' : ''}" data-cluster="${c.id}"><rect x="${c.x}" y="${c.y}" width="${c.w}" height="${c.h}" rx="${outer ? 18 : 12}"/><text x="${c.x + 16}" y="${c.y + (outer ? 26 : 22)}">${esc(title)}</text></g>`;
}

function draw(id, transition = null) {
  const prevL = state.L, prevCam = { ...cam };
  const L = LAYOUTS[id];
  const viewChanged = !prevL || (id.startsWith('all') !== state.layoutId.startsWith('all')) || (!id.startsWith('all') && id !== state.layoutId);
  state.L = L; state.layoutId = id; state.hover = null; state.peek = null;
  if (id.startsWith('all')) state.wholeVariant = id;
  if (viewChanged) state.hidden = hiddenDefaults(id);
  L_CL.innerHTML = L.clusters.map(clusterSVG).join('');
  L_ED.innerHTML = L.edges.map(edgeSVG).join('');
  L_ND.innerHTML = Object.entries(L.nodes).map(([k, b]) => nodeSVG(k, b)).join('');
  state.nodeEls = new Map($$('.node', L_ND).map(el => [el.dataset.node, el]));
  state.edgeEls = $$('.edge', L_ED);
  if (transition && prevL && !reduceMotion) runTransition(prevL, L, transition, prevCam);
  for (const d of DIFFS) svg.classList.toggle('hide-' + d, state.hidden.has(d));
  updateChrome();
  setupMini();
  paint();
}

function runTransition(prevL, L, { mode, group }, prevCam) {
  const ctr = b => b && { x: b[0] + b[2] / 2, y: b[1] + b[3] / 2 };
  const cctr = c => c && { x: c.x + c.w / 2, y: c.y + c.h / 2 };
  const oldA = mode === 'open' ? ctr(prevL.nodes['group-' + group]) : cctr(prevL.clusters.find(c => c.id === group));
  const newA = mode === 'open' ? cctr(L.clusters.find(c => c.id === group)) : ctr(L.nodes['group-' + group]);
  if (oldA && newA) { cam = { k: prevCam.k, x: prevCam.x + (oldA.x - newA.x) * prevCam.k, y: prevCam.y + (oldA.y - newA.y) * prevCam.k }; applyCam(); }
  const dx = (prevCam.x - cam.x) / cam.k, dy = (prevCam.y - cam.y) / cam.k;
  const members = new Set(membersOf(group).map(n => n.id));
  let centroid = null;
  if (mode === 'fold') {
    const pts = [...members].map(k => prevL.nodes[k]).filter(Boolean);
    if (pts.length) centroid = [pts.reduce((s, b) => s + b[0] + b[2] / 2, 0) / pts.length, pts.reduce((s, b) => s + b[1] + b[3] / 2, 0) / pts.length];
  }
  world.classList.add('no-anim');
  L_ED.style.opacity = 0; L_CL.style.opacity = 0;
  for (const [k, el] of state.nodeEls) {
    const b = L.nodes[k]; let from = prevL.nodes[k];
    if (!from && mode === 'open' && members.has(k)) { const g = prevL.nodes['group-' + group]; from = [g[0] + g[2] / 2 - b[2] / 2, g[1] + g[3] / 2 - b[3] / 2]; el.style.opacity = .2; }
    if (!from && mode === 'fold' && k === 'group-' + group && centroid) from = [centroid[0] - b[2] / 2, centroid[1] - b[3] / 2];
    if (from) el.style.transform = `translate(${from[0] + dx}px, ${from[1] + dy}px)`; else el.style.opacity = 0;
  }
  world.getBoundingClientRect();
  requestAnimationFrame(() => {
    world.classList.remove('no-anim');
    for (const [k, el] of state.nodeEls) { const b = L.nodes[k]; el.style.transform = `translate(${b[0]}px, ${b[1]}px)`; el.style.opacity = ''; }
    setTimeout(() => { L_ED.style.opacity = ''; L_CL.style.opacity = ''; }, 430);
  });
}

function owner(id, L = state.L) {
  if (!L || !id) return null;
  if (L.nodes[id]) return id;
  const ext = nodes.get(id)?.external;
  return ext && L.nodes['group-' + ext] ? 'group-' + ext : null;
}
const sameEdge = (e, s) => e.from === s.from && e.to === s.to && e.kind === s.kind;
function paint() {
  const L = state.L, sel = state.selected;
  const selNode = sel?.type === 'node' ? owner(sel.id) : sel?.type === 'group' ? owner('group-' + sel.id) : null;
  const focus = state.hover || selNode;
  const selEdge = sel?.type === 'edge' ? sel : null;
  const hl = new Set();
  state.edgeEls.forEach((el, i) => {
    const e = L.edges[i];
    let on = false;
    if (focus) on = !state.hidden.has(e.diff) && (e.from === focus || e.to === focus);
    else if (selEdge) on = sameEdge(e, selEdge);
    el.classList.toggle('hl', on);
    el.classList.toggle('peek', state.peek?.edge === i);
    if (on) { hl.add(e.from); hl.add(e.to); }
  });
  for (const [k, el] of state.nodeEls) {
    el.classList.toggle('sel', k === selNode);
    el.classList.toggle('focus', k === focus);
    el.classList.toggle('hl', hl.has(k) && k !== focus);
    el.classList.toggle('peek', state.peek?.node === k);
  }
  svg.classList.toggle('focusing', Boolean(focus || selEdge));
  drawMini();
}

/* view chrome: rail, title, frames, legend */
function viewIdOf(layoutId) { return layoutId.startsWith('all') ? 'all' : layoutId; }
function viewMeta(layoutId) {
  if (layoutId.startsWith('all')) return { title: 'Whole proof', description: `Every expert node and every reached, linked Lean version (${D.nodes.length} nodes). External frames fold into single nodes; open one to see its members.` };
  return BRANCHES.find(v => v.id === layoutId);
}
function updateChrome() {
  const id = state.layoutId, v = viewIdOf(id), meta = viewMeta(id);
  $$('.vbtn').forEach(b => b.setAttribute('aria-current', String(b.dataset.view === v)));
  $('#view-select').value = v;
  $('#view-title').textContent = meta.title;
  $('#view-desc').textContent = meta.description;
  const frames = $('#frames');
  if (id.startsWith('all')) {
    const opts = [['all', 'All folded'], ...D.groups.map(g => g.id).filter(g => LAYOUTS['all-' + g]).map(g => ['all-' + g, frameShort(g)]), ['all-full', 'All open']];
    frames.innerHTML = '<span>Frames</span>' + opts.map(([k, t]) => `<button class="seg" data-variant="${k}" aria-pressed="${k === id}">${t}</button>`).join('');
    frames.hidden = false;
  } else if (state.L.clusters.length > 1) {
    frames.innerHTML = '<span>Go to frame</span>' + state.L.clusters.filter(c => c.id !== 'external').map(c => `<button class="seg" data-frame="${c.id}">${esc(frameShort(c.id))}</button>`).join('');
    frames.hidden = false;
  } else frames.hidden = true;
  const counts = Object.fromEntries(DIFFS.map(d => [d, 0]));
  for (const e of state.L.edges) counts[e.diff]++;
  $('#lg-list').innerHTML = DIFFS.map(d => `<li><button class="lg-item" role="switch" aria-checked="${!state.hidden.has(d)}" data-diff="${d}" title="${esc(D.diff_titles[d] + '. ' + DIFF[d].text)}">${swatch(d)}<span class="lbl">${DIFF[d].name}</span><span class="cnt">${counts[d]}</span></button></li>`).join('');
  $('#lg-nodes').innerHTML = `<span>${markIcon('used-proof')}proof</span><span>${markIcon('used-interface')}interface</span><span>${markIcon('used-definition')}data</span><span>${markIcon('unused-proof')}not used</span><span>${markIcon('unmatched')}no Lean</span>`;
}

/* minimap */
const mini = $('#minimap'); let miniOn = false, miniScale = 1, miniOff = [0, 0], miniQueued = false;
const cssVar = name => getComputedStyle(document.documentElement).getPropertyValue(name).trim();
function setupMini() {
  const L = state.L; miniOn = Object.keys(L.nodes).length > 40 && !narrow();
  mini.hidden = !miniOn; wrap.classList.toggle('has-mini', miniOn);
  if (!miniOn) return;
  const W = 210, H = Math.round(Math.min(150, Math.max(70, W * L.h / L.w))), dpr = window.devicePixelRatio || 1;
  mini.style.width = W + 'px'; mini.style.height = H + 'px'; mini.width = W * dpr; mini.height = H * dpr;
  miniScale = Math.min((W - 12) / L.w, (H - 12) / L.h); miniOff = [(W - L.w * miniScale) / 2, (H - L.h * miniScale) / 2];
  drawMini();
}
function drawMini() {
  if (!miniOn || miniQueued) return; miniQueued = true;
  requestAnimationFrame(() => {
    miniQueued = false; if (!miniOn) return;
    const ctx = mini.getContext('2d'), dpr = window.devicePixelRatio || 1, s = miniScale, [ox, oy] = miniOff;
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0); ctx.clearRect(0, 0, mini.width, mini.height);
    ctx.fillStyle = cssVar('--surface'); ctx.fillRect(0, 0, mini.width / dpr, mini.height / dpr);
    ctx.strokeStyle = cssVar('--frame-line'); ctx.lineWidth = 1;
    for (const c of state.L.clusters) ctx.strokeRect(ox + c.x * s, oy + c.y * s, c.w * s, c.h * s);
    const base = cssVar('--line-2'), hot = cssVar('--accent'), warm = cssVar('--ink-2');
    for (const [k, b] of Object.entries(state.L.nodes)) {
      const el = state.nodeEls.get(k);
      ctx.fillStyle = el?.classList.contains('sel') ? hot : el?.classList.contains('hl') ? warm : base;
      ctx.fillRect(ox + b[0] * s, oy + b[1] * s, Math.max(1.5, b[2] * s), Math.max(1.5, b[3] * s));
    }
    const v = viewport();
    ctx.strokeStyle = hot; ctx.lineWidth = 1.5;
    ctx.strokeRect(ox + (-cam.x / cam.k) * s, oy + (-cam.y / cam.k) * s, (v.w / cam.k) * s, (v.h / cam.k) * s);
  });
}
function miniJump(e) {
  const r = mini.getBoundingClientRect(), wx = (e.clientX - r.left - miniOff[0]) / miniScale, wy = (e.clientY - r.top - miniOff[1]) / miniScale, v = viewport();
  cancelAnimationFrame(camAnim); cam = { k: cam.k, x: v.w / 2 - wx * cam.k, y: v.h / 2 - wy * cam.k }; applyCam();
}
let miniDrag = false;
mini.addEventListener('pointerdown', e => { e.stopPropagation(); miniDrag = true; mini.setPointerCapture(e.pointerId); miniJump(e); });
mini.addEventListener('pointermove', e => { if (miniDrag) miniJump(e); });
mini.addEventListener('pointerup', () => { miniDrag = false; });

/* gestures */
const ptrs = new Map(); let drag = null, pinch = null, moved = 0, suppressClick = false;
const dist = (a, b) => Math.hypot(a.x - b.x, a.y - b.y), mid = (a, b) => ({ x: (a.x + b.x) / 2, y: (a.y + b.y) / 2 });
wrap.addEventListener('pointerdown', e => {
  if (e.target.closest('.ov')) return;
  if (e.pointerType === 'mouse' && e.button !== 0) return;
  cancelAnimationFrame(camAnim); suppressClick = false;
  ptrs.set(e.pointerId, { x: e.clientX, y: e.clientY });
  if (ptrs.size === 1) { drag = { x: e.clientX, y: e.clientY, cx: cam.x, cy: cam.y }; moved = 0; }
  else if (ptrs.size === 2) { const [a, b] = [...ptrs.values()]; pinch = { d: dist(a, b) || 1, m: mid(a, b), cam: { ...cam } }; drag = null; }
});
window.addEventListener('pointermove', e => {
  if (!ptrs.has(e.pointerId)) return;
  ptrs.set(e.pointerId, { x: e.clientX, y: e.clientY });
  if (pinch && ptrs.size === 2) {
    const [a, b] = [...ptrs.values()], r = wrap.getBoundingClientRect(), m = mid(a, b), k = clampK(pinch.cam.k * dist(a, b) / pinch.d);
    const wx = (pinch.m.x - r.left - pinch.cam.x) / pinch.cam.k, wy = (pinch.m.y - r.top - pinch.cam.y) / pinch.cam.k;
    cam = { k, x: m.x - r.left - wx * k, y: m.y - r.top - wy * k }; applyCam(); moved = 99; return;
  }
  if (drag) {
    const dx = e.clientX - drag.x, dy = e.clientY - drag.y;
    moved = Math.max(moved, Math.abs(dx) + Math.abs(dy));
    if (moved > 4) { wrap.classList.add('dragging'); cam.x = drag.cx + dx; cam.y = drag.cy + dy; applyCam(); }
  }
});
const endPtr = e => {
  if (!ptrs.delete(e.pointerId)) return;
  if (ptrs.size < 2) pinch = null;
  if (ptrs.size === 1) { const [p] = [...ptrs.values()]; drag = { x: p.x, y: p.y, cx: cam.x, cy: cam.y }; }
  if (ptrs.size === 0) { drag = null; wrap.classList.remove('dragging'); suppressClick = moved > 4; }
};
window.addEventListener('pointerup', endPtr); window.addEventListener('pointercancel', endPtr);
wrap.addEventListener('wheel', e => {
  if (e.target.closest('.ov')) return;
  e.preventDefault(); cancelAnimationFrame(camAnim);
  const r = wrap.getBoundingClientRect(), unit = e.deltaMode === 1 ? 16 : e.deltaMode === 2 ? r.height : 1;
  if (e.ctrlKey || e.metaKey) zoomAt(cam.k * Math.exp(-Math.max(-60, Math.min(60, e.deltaY * unit)) * .0085), e.clientX - r.left, e.clientY - r.top);
  else { const sx = e.shiftKey && !e.deltaX ? e.deltaY : e.deltaX, sy = e.shiftKey && !e.deltaX ? 0 : e.deltaY; cam.x -= sx * unit; cam.y -= sy * unit; applyCam(); }
}, { passive: false });
let gestureK = 1;
wrap.addEventListener('gesturestart', e => { e.preventDefault(); gestureK = cam.k; });
wrap.addEventListener('gesturechange', e => { e.preventDefault(); const r = wrap.getBoundingClientRect(); zoomAt(gestureK * e.scale, e.clientX - r.left, e.clientY - r.top); });

svg.addEventListener('click', e => {
  if (suppressClick) { suppressClick = false; return; }
  const n = e.target.closest('.node');
  if (n) { activateNode(n.dataset.node); return; }
  const ed = e.target.closest('.edge');
  if (ed) { const x = state.L.edges[+ed.dataset.i]; select({ type: 'edge', from: x.from, to: x.to, kind: x.kind, diff: x.diff, p: x.p, members: x.members }); return; }
  const c = e.target.closest('.cluster text');
  if (c) { zoomToCluster(c.parentNode.dataset.cluster); return; }
  if (state.selected) select(null);
});
svg.addEventListener('dblclick', e => {
  const n = e.target.closest('.node');
  const r = wrap.getBoundingClientRect();
  if (n) centreOn(n.dataset.node, { k: Math.max(1, cam.k) });
  else { const k = clampK(cam.k * 1.8), px = e.clientX - r.left, py = e.clientY - r.top, wx = (px - cam.x) / cam.k, wy = (py - cam.y) / cam.k; animateTo({ k, x: px - wx * k, y: py - wy * k }, 260); }
});
svg.addEventListener('pointerover', e => {
  if (e.pointerType !== 'mouse' || drag && moved > 4) return;
  const n = e.target.closest('.node');
  if (n && n.dataset.node !== state.hover) { state.hover = n.dataset.node; paint(); }
});
svg.addEventListener('pointerout', e => {
  const n = e.target.closest('.node');
  if (n && !n.contains(e.relatedTarget) && state.hover) { state.hover = null; paint(); }
});
function activateNode(key) {
  if (key.startsWith('group-')) {
    const g = key.slice(6);
    if (state.layoutId.startsWith('all') && LAYOUTS['all-' + g]) { draw('all-' + g, { mode: 'open', group: g }); select({ type: 'group', id: g }); zoomToCluster(g, 650); }
    else select({ type: 'group', id: g });
    return;
  }
  select({ type: 'node', id: key });
}
function zoomToCluster(id, ms = 380) {
  const c = state.L.clusters.find(c => c.id === id); if (!c) return;
  const fit = camFor({ x: c.x, y: c.y, w: c.w, h: c.h }, { maxK: 1, pad: 40 });
  if (fit.k >= .6) { animateTo(fit, ms); return; }
  // Too wide to read when fitted: start at its left edge at a readable scale.
  const k = .7, v = viewport(), top = overlayTop();
  animateTo({ k, x: 32 - c.x * k, y: top + Math.max(0, (v.h - top - c.h * k) / 2) - c.y * k }, ms);
}

/* switching views */
function bestLayout(id) {
  const has = lid => Boolean(LAYOUTS[lid]?.nodes[id]);
  if (has(state.layoutId)) return state.layoutId;
  const ext = nodes.get(id)?.external;
  if (state.layoutId.startsWith('all')) return ext && LAYOUTS['all-' + ext] ? 'all-' + ext : 'all-full';
  const v = BRANCHES.find(v => has(v.id));
  if (v) return v.id;
  if (ext && LAYOUTS['all-' + ext]) return 'all-' + ext;
  return has('all') ? 'all' : 'all-full';
}
function showView(viewId, { node = null } = {}) {
  const layout = viewId === 'all' ? state.wholeVariant : viewId;
  const sameWhole = layout.startsWith('all') && state.layoutId?.startsWith('all');
  const prev = state.layoutId;
  let moving = false;
  if (layout !== prev) {
    const ext = node && nodes.get(node)?.external;
    moving = Boolean(sameWhole && ext && layout === 'all-' + ext);
    draw(layout, moving ? { mode: 'open', group: ext } : null);
  }
  const sel = state.selected;
  if (sel?.type === 'edge' && !state.L.edges.some(e => sameEdge(e, sel))) { state.selected = null; paint(); }
  else if (sel?.type === 'group' && !state.L.nodes['group-' + sel.id] && !state.L.clusters.some(c => c.id === sel.id)) { state.selected = null; paint(); }
  const focus = node || (state.selected?.type === 'node' ? state.selected.id : state.selected?.type === 'edge' ? state.selected.to : null);
  const o = focus && owner(focus);
  if (layout === prev && o) centreOn(o, { ifHidden: !node });
  else if (moving && o) centreOn(o, { k: Math.max(cam.k, .78), ms: 620 });
  else if (o && (layout.startsWith('all') || node)) centreOn(o, { k: layout.startsWith('all') ? .78 : Math.max(.78, Math.min(1, camFor({ x: 0, y: 0, w: state.L.w, h: state.L.h }).k)), ms: 0 });
  else initialCam();
  renderInspector();
}
function goNode(id, { push = true } = {}) {
  const target = bestLayout(id);
  select({ type: 'node', id }, { push, centre: false });
  showView(viewIdOf(target) === 'all' ? (state.wholeVariant = target, 'all') : target, { node: id });
}

/* ---------- selection, history, inspector ---------- */
const insp = $('#inspector'), body = $('#insp-body');
function keyOf(s) { return s ? (s.type === 'edge' ? `e:${s.from}>${s.to}>${s.kind}` : `${s.type}:${s.id}`) : ''; }
function select(sel, { push = true, centre = false } = {}) {
  state.selected = sel; state.peek = null;
  if (sel && push && keyOf(state.history[state.hpos]) !== keyOf(sel)) { state.history = state.history.slice(0, state.hpos + 1); state.history.push(sel); state.hpos = state.history.length - 1; }
  history.replaceState(null, '', sel?.type === 'node' ? '#node-' + encodeURIComponent(sel.id) : location.pathname + location.search);
  if (sel) { $('#atlas').classList.remove('insp-off'); if (narrow() && insp.dataset.sheet === 'peek') setSheet('half'); }
  else if (narrow()) setSheet('peek');
  renderInspector(); paint();
  if ((centre || narrow()) && sel?.type === 'node' && owner(sel.id)) centreOn(owner(sel.id), { ifHidden: true });
}
function stepHistory(d) {
  const i = state.hpos + d; if (i < 0 || i >= state.history.length) return;
  state.hpos = i; const s = state.history[i];
  if (s.type === 'node') goNode(s.id, { push: false });
  else select(s, { push: false });
}
function navBar() {
  const n = state.history.length;
  return `<div class="insp-nav"><button class="ibtn" data-hist="-1" ${state.hpos <= 0 ? 'disabled' : ''} aria-label="Previous selection" title="Previous ( [ )">${ICON.back}</button><button class="ibtn" data-hist="1" ${state.hpos >= n - 1 ? 'disabled' : ''} aria-label="Next selection" title="Next ( ] )">${ICON.fwd}</button><span class="crumb">${n ? `${state.hpos + 1} / ${n}` : ''}</span><span class="grow"></span>${state.selected?.type === 'node' ? `<button class="ibtn" data-copy-link="${esc(state.selected.id)}" title="Copy a link to this node">${ICON.link}<span>Link</span></button>` : ''}<button class="ibtn" data-insp="hide" aria-label="Hide the panel" title="Hide the panel">${ICON.hide}</button></div>`;
}
function renderInspector() {
  const s = state.selected;
  if (window.MathJax?.typesetClear) try { MathJax.typesetClear([body]); } catch (_) { /* not ready */ }
  if (!s) body.innerHTML = viewSummary();
  else if (s.type === 'node') body.innerHTML = nodeCard(s.id);
  else if (s.type === 'group') body.innerHTML = groupCard(s.id);
  else body.innerHTML = edgeCard(s);
  body.scrollTop = 0;
  typeset(body);
}
function connections(key) {
  const L = state.L, o = owner(key), dep = [], use = [];
  if (!o) return null;
  L.edges.forEach((e, i) => { if (e.to === o) dep.push([e, i, e.from]); if (e.from === o) use.push([e, i, e.to]); });
  return { dep, use };
}
function connList(items) {
  if (!items.length) return '<p class="empty">None in this view.</p>';
  let h = '';
  for (const d of DIFFS) {
    const m = items.filter(([e]) => e.diff === d); if (!m.length) continue;
    h += `<div class="cg"><p class="cg-h">${swatch(d)}${DIFF[d].name}<span>· ${m.length}</span></p><ul>` + m.map(([e, i, other]) => {
      const many = e.members && e.members.length > 1;
      return `<li class="${state.hidden.has(d) ? 'filtered' : ''}"><button class="rel" data-sel-node="${esc(other)}" data-peek-node="${esc(other)}" data-peek-edge="${i}"><span class="rel-h">${esc(nameOf(other))}</span><span class="rel-t">${esc(subOf(other))}</span></button><button class="wit" data-sel-edge="${i}" data-peek-edge="${i}">${many ? e.members.length + ' links' : 'evidence'}</button></li>`;
    }).join('') + '</ul></div>';
  }
  return h;
}
function connSection(key) {
  const c = connections(key);
  if (!c) return '';
  const where = viewMeta(state.layoutId).title;
  return `<section class="sec"><div class="conn-dir"><h3 class="sec-h">Depends on <span class="n">${c.dep.length}</span><span class="src">in ${esc(where)}</span></h3>${connList(c.dep)}</div>
    <div class="conn-dir"><h3 class="sec-h">Used by <span class="n">${c.use.length}</span></h3>${connList(c.use)}</div></section>`;
}
function chain(path) {
  if (!path?.length) return '';
  const li = name => { const [ns, nm] = splitName(name), href = sourceOf(name); return `<li class="decl"><a ${href ? `href="${esc(href)}" target="_blank" rel="noopener"` : ''} title="${esc(name)}"><span class="ns">${esc(ns)}</span><span class="nm">${esc(nm)}</span></a></li>`; };
  let h = '<ol class="chain">' + li(path[0].from);
  for (const s of path) h += `<li class="ref"><span>${esc(s.kind)}</span></li>` + li(s.to);
  return h + '</ol>';
}
function nodeCard(id) {
  const n = nodes.get(id);
  if (!n) return viewSummary();
  const views = [...BRANCHES.filter(v => LAYOUTS[v.id].nodes[id]), ...(owner(id, LAYOUTS.all) || LAYOUTS['all-full'].nodes[id] ? [{ id: 'all', title: 'Whole proof' }] : [])];
  const cur = viewIdOf(state.layoutId);
  const st = n.statements.map(s => `<section class="sec"><h3 class="sec-h">Statement <span class="src">${esc(s.heading)}</span></h3><div class="prose">${s.html}</div>
      <a class="textlink" href="${esc(s.url)}">Read it in the manuscript →</a></section>`).join('');
  const rl = n.remark_links.map(r => `<a href="${esc(r.url)}">${esc(r.label)}</a>`).join(' · ');
  const vers = n.versions.length ? `<section class="sec"><h3 class="sec-h">Lean versions <span class="n">${n.versions.length}</span></h3>` + n.versions.map(v => {
    const [ns, nm] = splitName(v.name);
    return `<details class="ver"><summary>${markIcon(verStatus(v))}<span class="vname"><code>${esc(nm)}</code><span class="vmeta">${ROLE[v.role] || v.role} · ${v.reached ? 'used by the root' : 'outside the root'}${v.name === n.primary ? ' · graph anchor' : ''}</span></span>${ICON.chev}</summary>
      <div class="ver-body"><p class="full">${esc(ns)}<b>${esc(nm)}</b> · ${esc(v.kind)}</p>${ROLE_NOTE[v.role] ? `<p class="note">${ROLE_NOTE[v.role]}</p>` : ''}
      <pre class="type"><code>${esc(nm)} : ${esc(v.type || '')}${v.definition ? '\n:= ' + esc(v.definition) : ''}</code></pre>
      <p class="links"><a href="${esc(v.doc)}" target="_blank" rel="noopener">Lean documentation ↗</a><a href="${esc(v.src)}" target="_blank" rel="noopener">Source ↗</a></p>
      ${v.p != null ? `<details class="reach"><summary>${ICON.chev}Reached from the root through ${D.paths[v.p].length} references</summary>${chain(pathOf(v.p))}</details>` : ''}</div></details>`;
  }).join('') + '</section>' : `<section class="sec"><h3 class="sec-h">Lean versions</h3><p class="empty">No independently identified Lean declaration is assigned to this operation. Its roadmap connections remain dashed or dotted.</p></section>`;
  return `${navBar()}<header>
    <p class="eyebrow"><span class="bdot g-${n.group}"></span>${esc(D.branches[n.group] || n.group)}${n.origin ? ' · ' + esc(n.origin) : ''}</p>
    <h2 class="ttl" id="insp-title" tabindex="-1">${esc(n.expert ? n.paper : n.full_heading)}</h2>
    <p class="subttl">${esc(n.expert ? n.title : (n.summary.join(' ') || n.title))}</p>
    <div class="facts"><span class="pill">${markIcon(n.status)}${esc(statusLabel(n.status))}</span><button class="chip mono" data-copy="${esc(n.id)}" title="Copy the node ID">${esc(n.id)}</button></div>
    ${n.source ? `<p class="source">Expert source: ${esc(n.source)}</p>` : ''}
  </header>
  ${connSection(id)}
  ${views.length ? `<div class="appears"><span>Appears in</span>${views.map(v => `<button class="chip${v.id === cur ? ' on' : ''}" data-goto-view="${v.id}" data-node="${esc(id)}">${esc(viewShort(v.id))}</button>`).join('')}</div>` : ''}
  ${st}
  ${n.remark ? `<aside class="remark"><h3 class="sec-h">Correspondence remark</h3><p>${esc(n.remark)}</p>${rl ? `<p class="rlinks">Related remarks: ${rl}</p>` : ''}</aside>` : ''}
  ${vers}
  ${n.expert && n.expert_html ? `<details class="expert"><summary>${ICON.chev}The expert’s original formulation</summary><div class="prose">${n.expert_html}</div><p class="note">Source material for comparison. The expert’s Lean blocks were pseudocode; only the declarations above were audited.</p></details>` : ''}`;
}
function groupCard(g) {
  const G = groups.get(g), ms = membersOf(g), folded = Boolean(state.L.nodes['group-' + g]);
  const canOpen = state.layoutId.startsWith('all') && LAYOUTS['all-' + g];
  return `${navBar()}<header><p class="eyebrow"><span class="bdot g-external"></span>External input</p>
    <h2 class="ttl" id="insp-title" tabindex="-1">${esc(G.title)}</h2>
    <p class="subttl">${ms.length} reached project declarations, grouped by their reviewed module boundary.</p>
    <div class="facts">${folded && canOpen ? `<button class="chip on" data-variant="all-${g}">Open this frame</button>` : ''}${!folded && state.layoutId === 'all-' + g ? '<button class="chip" data-variant="all">Fold it again</button>' : ''}</div></header>
    ${folded ? connSection('group-' + g) : ''}
    <section class="sec"><h3 class="sec-h">Members <span class="n">${ms.length}</span></h3><ul class="vlist">${ms.map(n => `<li><button data-sel-node="${esc(n.id)}">${markIcon(n.status)}<span><b>${esc(n.full_heading)}</b> <span class="t">${esc(n.summary.join(' '))}</span></span></button></li>`).join('')}</ul></section>
    <p class="tip">An arrow to a folded frame stands for its members’ connections, which share its class.</p>`;
}
function edgeCard(s) {
  const many = s.members && (s.members.length > 1 || s.members[0][0] !== s.from || s.members[0][1] !== s.to);
  const info = D.connections[`${s.from}>${s.to}>${s.kind}`];
  const end = k => `<button class="link" data-sel-node="${esc(k)}">${esc(nameOf(k))}</button>`;
  const notes = notes => notes?.length ? `<section class="sec"><h3 class="sec-h">Roadmap note</h3>${notes.map(t => `<p class="reason">${esc(t.replace(/^[^:]*→[^:]*:\s*/, ''))}</p>`).join('')}</section>` : '';
  let evidence = '';
  if (many) {
    evidence = `<section class="sec"><h3 class="sec-h">Folded connections <span class="n">${s.members.length}</span></h3>` + s.members.map(([f, t, k, p]) => {
      const m = D.connections[`${f}>${t}>${k}`];
      return `<div class="member"><div class="member-h"><button class="rel" data-sel-node="${esc(f)}"><span class="rel-h">${esc(nameOf(f))}</span></button>→<button class="rel" data-sel-node="${esc(t)}"><span class="rel-h">${esc(nameOf(t))}</span></button></div>
        ${p != null ? `<details class="reach"><summary>${ICON.chev}Kernel witness · ${D.paths[p].length} references</summary>${chain(pathOf(p))}</details>` : m?.reason ? `<p class="reason">${esc(m.reason)}</p>` : ''}</div>`;
    }).join('') + '</section>';
  } else if (s.kind === 'actual' && s.p != null) {
    evidence = `<section class="sec"><h3 class="sec-h">Kernel witness <span class="n">${D.paths[s.p].length}</span><span class="src">references</span></h3>${chain(pathOf(s.p))}
      <p class="tip">The chain reads from the consumer down to its prerequisite; the drawn arrow points the other way. Every step is a type, value or structural reference in a compiled declaration.</p></section>`;
  } else if (info?.reason) {
    evidence = `<section class="sec"><h3 class="sec-h">Why Lean has no such path</h3><p class="reason">${esc(info.reason)}</p></section>`;
  }
  return `${navBar()}<header><p class="eyebrow">Arrow · ${esc(viewMeta(state.layoutId).title)}</p>
    <h2 class="ttl edge-ttl" id="insp-title" tabindex="-1">${end(s.from)}<span class="arr">→</span>${end(s.to)}</h2>
    <div class="facts"><span class="pill">${swatch(s.diff)}${esc(D.diff_titles[s.diff])}</span></div>
    <p class="explain">${esc(DIFF[s.diff].text)}</p></header>
    ${evidence}${many ? '' : notes(info?.notes)}
    ${info?.audit ? `<p class="tip"><a href="${esc(info.audit)}">Find this arrow on the evidence page →</a></p>` : ''}`;
}
function viewSummary() {
  const L = state.L, meta = viewMeta(state.layoutId);
  const idx = BRANCHES.findIndex(v => v.id === state.layoutId);
  const list = Object.entries(L.nodes).sort((a, b) => a[1][1] - b[1][1] || a[1][0] - b[1][0]);
  return `${navBar()}<header><p class="eyebrow">${idx >= 0 ? `Branch ${idx + 1} of ${BRANCHES.length}` : 'Complete graph'}</p><h2 class="ttl" id="insp-title" tabindex="-1">${esc(meta.title)}</h2><p class="subttl">${esc(meta.description)}</p></header>
    <section class="sec"><h3 class="sec-h">Nodes in this view <span class="n">${list.length}</span><span class="src">conclusions first</span></h3><ul class="vlist">${list.map(([k]) => {
      const n = nodes.get(k);
      return `<li><button data-sel-node="${esc(k)}">${n ? markIcon(n.status) : markIcon('group')}<span><b>${esc(nameOf(k))}</b> <span class="t">${esc(subOf(k))}</span></span></button></li>`;
    }).join('')}</ul></section><p class="tip">Select a node or an arrow to see its statement and evidence. Press / to search every node.</p>`;
}
body.addEventListener('scroll', () => $('.insp-nav', body)?.classList.toggle('stuck', body.scrollTop > 4));
body.addEventListener('pointerover', e => {
  const t = e.target.closest('[data-peek-node], [data-peek-edge]');
  const peek = t ? { node: t.dataset.peekNode ? owner(t.dataset.peekNode) : null, edge: t.dataset.peekEdge != null ? +t.dataset.peekEdge : null } : null;
  if (JSON.stringify(peek) !== JSON.stringify(state.peek)) { state.peek = peek; paint(); }
});
body.addEventListener('pointerleave', () => { if (state.peek) { state.peek = null; paint(); } });

/* resizable panel: drag its left edge, arrow keys on the handle, double-click to reset */
const resizer = $('#insp-resize'), WIDTH_KEY = 'atlas-panel-width';
function panelBounds() { return [300, Math.max(300, Math.min(innerWidth * .62, innerWidth - wrap.getBoundingClientRect().left - 520))]; }
function setPanelWidth(px, save = true) {
  const [min, max] = panelBounds(), width = Math.round(Math.max(min, Math.min(max, px)));
  document.documentElement.style.setProperty('--insp-w', width + 'px');
  resizer.setAttribute('aria-valuenow', String(width));
  if (save) try { localStorage.setItem(WIDTH_KEY, String(width)); } catch (_) { /* storage may be unavailable */ }
}
function resetPanelWidth() {
  document.documentElement.style.removeProperty('--insp-w');
  try { localStorage.removeItem(WIDTH_KEY); } catch (_) { /* storage may be unavailable */ }
}
try { const saved = Number(localStorage.getItem(WIDTH_KEY)); if (saved) setPanelWidth(saved, false); } catch (_) { /* storage may be unavailable */ }
resizer.addEventListener('pointerdown', e => {
  if (e.button !== 0) return;
  e.preventDefault();
  resizer.setPointerCapture(e.pointerId);
  const startX = e.clientX, startWidth = insp.getBoundingClientRect().width;
  document.body.classList.add('resizing');
  const move = ev => setPanelWidth(startWidth + startX - ev.clientX, false);
  const end = () => {
    resizer.removeEventListener('pointermove', move);
    resizer.removeEventListener('pointerup', end);
    resizer.removeEventListener('pointercancel', end);
    document.body.classList.remove('resizing');
    setPanelWidth(insp.getBoundingClientRect().width);
  };
  resizer.addEventListener('pointermove', move);
  resizer.addEventListener('pointerup', end);
  resizer.addEventListener('pointercancel', end);
});
resizer.addEventListener('dblclick', resetPanelWidth);
resizer.addEventListener('keydown', e => {
  if (e.key !== 'ArrowLeft' && e.key !== 'ArrowRight') return;
  e.preventDefault();
  setPanelWidth(insp.getBoundingClientRect().width + (e.key === 'ArrowLeft' ? 32 : -32));
});
window.addEventListener('resize', () => { if (document.documentElement.style.getPropertyValue('--insp-w')) setPanelWidth(insp.getBoundingClientRect().width, false); });

function setSheet(s) { insp.dataset.sheet = s; requestAnimationFrame(() => document.documentElement.style.setProperty('--sheet-cover', sheetCover() + 'px')); }
$('#sheet-toggle').addEventListener('click', () => setSheet({ peek: 'half', half: 'full', full: 'peek' }[insp.dataset.sheet] || 'half'));

/* ---------- search palette ---------- */
const pal = $('#palette'), palIn = $('#pal-input'), palList = $('#pal-list');
const HAY = D.nodes.map(n => ({ n, id: n.id.toLowerCase(), head: (n.full_heading + ' ' + n.paper).toLowerCase(), title: (n.title + ' ' + n.summary.join(' ')).toLowerCase(), lean: n.versions.map(v => v.name).join(' ').toLowerCase() }));
let palHits = [], palActive = 0;
function searchNodes(q) {
  const toks = q.toLowerCase().split(/\s+/).filter(Boolean);
  if (!toks.length) return HAY.filter(h => h.n.expert).slice(0, 40).map(h => h.n);
  const out = [];
  for (const h of HAY) {
    let score = 0, ok = true;
    for (const t of toks) {
      const s = (h.id === t ? 60 : h.id.includes(t) ? 25 : 0) + (h.head.includes(t) ? 20 : 0) + (h.title.includes(t) ? 9 : 0) + (h.lean.includes(t) ? 4 : 0);
      if (!s) { ok = false; break; } score += s;
    }
    if (ok) out.push([score + (h.n.expert ? 12 : 0), h.n]);
  }
  return out.sort((a, b) => b[0] - a[0]).slice(0, 50).map(x => x[1]);
}
function renderPal() {
  palHits = searchNodes(palIn.value); palActive = Math.min(palActive, Math.max(0, palHits.length - 1));
  const q = palIn.value.trim().toLowerCase();
  palList.innerHTML = palHits.length ? palHits.map((n, i) => {
    const leanHit = q && !n.title.toLowerCase().includes(q) && n.versions.find(v => v.name.toLowerCase().includes(q));
    return `<li class="opt" role="option" id="opt-${i}" data-i="${i}" aria-selected="${i === palActive}">${markIcon(n.status)}<span><span class="h">${esc(n.full_heading)}</span> <span class="t">${esc(n.expert ? n.title : n.summary.join(' '))}</span>${leanHit ? `<span class="lean">${esc(leanHit.name)}</span>` : ''}</span><span class="r">${esc(n.id.startsWith('lean-') ? 'Lean version' : n.id)}</span></li>`;
  }).join('') : '<li class="empty" style="padding:10px">No node matches. Try a paper number such as 7.6, an ID such as W2L7_6, or part of a Lean name.</li>';
  palIn.setAttribute('aria-activedescendant', palHits.length ? 'opt-' + palActive : '');
}
function openPalette() { if (pal.open) return; palIn.value = ''; palActive = 0; renderPal(); pal.showModal(); palIn.focus(); }
function choosePal(i) { const n = palHits[i]; if (!n) return; pal.close(); goNode(n.id); }
palIn.addEventListener('input', () => { palActive = 0; renderPal(); });
palIn.addEventListener('keydown', e => {
  if (e.key === 'ArrowDown' || e.key === 'ArrowUp') { e.preventDefault(); palActive = (palActive + (e.key === 'ArrowDown' ? 1 : -1) + palHits.length) % Math.max(1, palHits.length); renderPal(); $('#opt-' + palActive)?.scrollIntoView({ block: 'nearest' }); }
  if (e.key === 'Enter') { e.preventDefault(); choosePal(palActive); }
});
palList.addEventListener('click', e => { const o = e.target.closest('.opt'); if (o) choosePal(+o.dataset.i); });
pal.addEventListener('click', e => { if (e.target === pal) pal.close(); });

/* ---------- MathJax ---------- */
let mathReady = false; const mathQueue = new Set();
// MathJax 3 does not break inline formulas. One wider than its text column scrolls on its own line.
function fitWideMath(root = body) {
  for (const prose of root.querySelectorAll('.prose')) {
    const edge = prose.getBoundingClientRect().right + 0.5;
    for (const math of prose.querySelectorAll('mjx-container:not([display="true"])')) {
      math.classList.remove('mjx-wide');
      if (math.getBoundingClientRect().right > edge) math.classList.add('mjx-wide');
    }
  }
}
function typeset(el) { if (mathReady) MathJax.typesetPromise([el]).then(() => fitWideMath(el)).catch(() => {}); else mathQueue.add(el); }
function mathIsReady() { mathReady = true; const els = [...mathQueue].filter(e => e.isConnected); mathQueue.clear(); if (els.length) MathJax.typesetPromise(els).then(() => els.forEach(fitWideMath)).catch(() => {}); }
let fitQueued = false;
new ResizeObserver(() => { if (fitQueued) return; fitQueued = true; requestAnimationFrame(() => { fitQueued = false; fitWideMath(); }); }).observe(body);
// MathJax may have started before the atlas data arrived; then its ready hook has already run.
window.atlasMathReady = mathIsReady;
if (typeof window.MathJax?.typesetPromise === 'function') MathJax.startup.promise.then(mathIsReady);

/* ---------- global events ---------- */
document.addEventListener('click', e => {
  const t = e.target;
  if (t.closest('[data-open-palette]')) { openPalette(); return; }
  const v = t.closest('[data-view]');
  if (v) { showView(v.dataset.view); return; }
  const gv = t.closest('[data-goto-view]');
  if (gv) { const id = gv.dataset.gotoView; if (id === 'all') state.wholeVariant = bestLayoutWhole(gv.dataset.node); showView(id, { node: gv.dataset.node }); return; }
  const variant = t.closest('[data-variant]');
  if (variant) {
    const next = variant.dataset.variant, prev = state.layoutId;
    if (next === prev) return;
    const g = next.startsWith('all-') && next !== 'all-full' ? next.slice(4) : null, pg = prev.startsWith('all-') && prev !== 'all-full' ? prev.slice(4) : null;
    draw(next, g && prev === 'all' ? { mode: 'open', group: g } : pg && next === 'all' ? { mode: 'fold', group: pg } : null);
    if (g && prev === 'all') zoomToCluster(g, 650);
    else if (pg && next === 'all') centreOn('group-' + pg, { k: Math.max(cam.k, .62), ms: 650 });
    else if (g) zoomToCluster(g, 0);
    else { const o = state.selected?.type === 'node' && owner(state.selected.id); if (o) centreOn(o, { ms: 0 }); else fitAll(0); }
    renderInspector(); return;
  }
  const fr = t.closest('[data-frame]');
  if (fr) { zoomToCluster(fr.dataset.frame); return; }
  const z = t.closest('[data-zoom]');
  if (z) { const a = z.dataset.zoom; if (a === 'in') zoomBy(1.3); else if (a === 'out') zoomBy(1 / 1.3); else fitAll(); return; }
  const sn = t.closest('[data-sel-node]');
  if (sn) { const k = sn.dataset.selNode; if (k.startsWith('group-')) select({ type: 'group', id: k.slice(6) }); else if (state.L.nodes[k]) select({ type: 'node', id: k }, { centre: true }); else goNode(k); return; }
  const se = t.closest('[data-sel-edge]');
  if (se) { const x = state.L.edges[+se.dataset.selEdge]; select({ type: 'edge', from: x.from, to: x.to, kind: x.kind, diff: x.diff, p: x.p, members: x.members }); return; }
  const hs = t.closest('[data-hist]');
  if (hs) { stepHistory(+hs.dataset.hist); return; }
  const ih = t.closest('[data-insp]');
  if (ih) { $('#atlas').classList.toggle('insp-off', ih.dataset.insp === 'hide'); setupMini(); return; }
  const cp = t.closest('[data-copy], [data-copy-link]');
  if (cp) {
    const text = cp.dataset.copy ?? location.origin + location.pathname + '#node-' + cp.dataset.copyLink;
    const done = () => { const old = cp.innerHTML; cp.textContent = 'Copied'; setTimeout(() => { cp.innerHTML = old; }, 1100); };
    Promise.resolve(navigator.clipboard?.writeText(text)).then(done, () => { cp.title = text; });
    return;
  }
  const lg = t.closest('.lg-item');
  if (lg) { const d = lg.dataset.diff; state.hidden.has(d) ? state.hidden.delete(d) : state.hidden.add(d); svg.classList.toggle('hide-' + d, state.hidden.has(d)); lg.setAttribute('aria-checked', String(!state.hidden.has(d))); paint(); if (state.selected?.type === 'node') renderInspector(); return; }
});
function bestLayoutWhole(id) { const ext = nodes.get(id)?.external; if (owner(id, LAYOUTS[state.wholeVariant])) return state.wholeVariant; return ext && LAYOUTS['all-' + ext] ? 'all-' + ext : 'all'; }
$('#view-select').addEventListener('change', e => showView(e.target.value));
$('#lg-list').addEventListener('pointerover', e => { const it = e.target.closest('.lg-item'); if (it && !state.hidden.has(it.dataset.diff)) svg.dataset.spot = it.dataset.diff; });
$('#lg-list').addEventListener('pointerleave', () => { delete svg.dataset.spot; });
$('#lg-min').addEventListener('click', e => { const l = $('#legend'); l.classList.toggle('min'); const min = l.classList.contains('min'); e.target.textContent = min ? 'Show' : 'Hide'; e.target.setAttribute('aria-expanded', String(!min)); });
document.addEventListener('keydown', e => {
  const typing = e.target.closest('input, textarea, select, [contenteditable]');
  if ((e.key === 'k' || e.key === 'K') && (e.metaKey || e.ctrlKey)) { e.preventDefault(); openPalette(); return; }
  if (e.key === '/' && !typing && !pal.open) { e.preventDefault(); openPalette(); return; }
  if (typing || pal.open) return;
  const node = e.target.closest?.('.node');
  if (node && (e.key === 'Enter' || e.key === ' ')) { e.preventDefault(); activateNode(node.dataset.node); return; }
  if (e.key === 'Escape') { if (state.selected) select(null); return; }
  if (e.key === '+' || e.key === '=') zoomBy(1.3);
  else if (e.key === '-' || e.key === '_') zoomBy(1 / 1.3);
  else if (e.key === '0') fitAll();
  else if (e.key === '[') stepHistory(-1);
  else if (e.key === ']') stepHistory(1);
  else if (e.key.startsWith('Arrow') && !node && !e.target.closest('button, a')) {
    e.preventDefault(); const s = 80; cam.x += e.key === 'ArrowLeft' ? s : e.key === 'ArrowRight' ? -s : 0; cam.y += e.key === 'ArrowUp' ? s : e.key === 'ArrowDown' ? -s : 0; applyCam();
  }
});
svg.addEventListener('focusin', e => { const n = e.target.closest('.node'); if (n) centreOn(n.dataset.node, { ifHidden: true, ms: 200 }); });
new ResizeObserver(() => { if (state.L) { setupMini(); drawMini(); } }).observe(wrap);
matchMedia('(prefers-color-scheme: dark)').addEventListener?.('change', drawMini);

/* ---------- boot ---------- */
draw('overview');
if (narrow()) { setSheet('peek'); $('#legend').classList.add('min'); $('#lg-min').textContent = 'Show'; $('#lg-min').setAttribute('aria-expanded', 'false'); }
loading.hidden = true;
function readHash() {
  let h = '';
  try { h = decodeURIComponent(location.hash.slice(1)); } catch (_) { return; }
  if (h.startsWith('node-') && nodes.has(h.slice(5))) goNode(h.slice(5));
  else if (h === 'search') { history.replaceState(null, '', location.pathname + location.search); openPalette(); }
}
renderInspector();
requestAnimationFrame(() => { if (!state.selected) initialCam(); setupMini(); readHash(); });
window.addEventListener('hashchange', readHash);
}
})();
