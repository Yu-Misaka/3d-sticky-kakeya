'use strict';

(() => {
  const rows = Array.from(document.querySelectorAll('.index-row'));
  const byId = new Map(rows.map(row => [row.id.slice(5), row]));
  const search = document.getElementById('search');
  const group = document.getElementById('group-filter');
  const status = document.getElementById('status-filter');
  const dialog = document.getElementById('unified-map');
  const stage = document.getElementById('map-stage');
  const panel = document.getElementById('details');
  const panelTitle = document.getElementById('details-title');
  const panelBody = document.getElementById('details-body');
  const variants = new Set((dialog.dataset.variants || '').split(' ').filter(Boolean));
  const diffTitles = new Map(Array.from(document.querySelectorAll('[data-filters="page"] input[data-diff]'),
    input => [input.dataset.diff, input.parentElement.textContent.trim()]));
  const scales = new WeakMap();
  const svgCache = new Map();
  let selected = null;
  let hovering = null;
  let activeView = document.querySelector('.viewbtn')?.dataset.view;
  let variant = null;
  let returnFocus = null;

  const externalOf = key => byId.get(key)?.dataset.external || null;
  const groupTitle = name => document.getElementById('card-group-' + name)?.content.querySelector('h3')?.textContent || name;

  function nameOf(key) {
    if (key.startsWith('group-')) return groupTitle(key.slice(6));
    const row = byId.get(key);
    return row ? row.querySelector('.index-heading').textContent : key;
  }

  function filterRows() {
    const query = search.value.trim().toLowerCase();
    let count = 0;
    for (const row of rows) {
      row.hidden = Boolean((query && !row.dataset.search.includes(query)) ||
        (group.value && group.value !== row.dataset.group) ||
        (status.value && status.value !== row.dataset.status));
      if (!row.hidden) count += 1;
    }
    document.getElementById('card-count').textContent = `${count} of ${rows.length} nodes`;
    document.getElementById('no-results').hidden = count !== 0;
  }

  function resetFilters() {
    search.value = group.value = status.value = '';
    filterRows();
  }

  const scopeOf = element => (element.closest('dialog') ? 'map' : 'page');
  const activeSvg = scope => (scope === 'map' ? stage.querySelector('.depgraph')
    : document.querySelector(`#view-${CSS.escape(activeView)} .depgraph`));

  function graphNode(svg, key) {
    // Inside a folded frame, a member is represented by the frame's node.
    const nodes = Array.from(svg.querySelectorAll('.graphnode'));
    const own = nodes.find(node => node.dataset.node === key);
    const external = externalOf(key);
    return own || (external && nodes.find(node => node.dataset.node === 'group-' + external)) || null;
  }

  function paintGraph(svg, key) {
    // A selection in another branch should not fade this entire view.
    key = key && graphNode(svg, key)?.dataset.node;
    const inputs = new Set();
    const outputs = new Set();
    for (const edge of svg.querySelectorAll('.depedge')) {
      const incoming = Boolean(key && !edge.hasAttribute('hidden') && edge.dataset.to === key);
      const outgoing = Boolean(key && !edge.hasAttribute('hidden') && edge.dataset.from === key);
      if (incoming) inputs.add(edge.dataset.from);
      if (outgoing) outputs.add(edge.dataset.to);
      edge.classList.toggle('incoming', incoming);
      edge.classList.toggle('outgoing', outgoing);
      edge.classList.toggle('dim', Boolean(key && !incoming && !outgoing));
    }
    for (const node of svg.querySelectorAll('.graphnode')) {
      const id = node.dataset.node;
      node.classList.toggle('focused', id === key);
      node.classList.toggle('related-input', inputs.has(id) && id !== key);
      node.classList.toggle('related-output', outputs.has(id) && id !== key);
      node.classList.toggle('distant', Boolean(key && id !== key && !inputs.has(id) && !outputs.has(id)));
    }
    return {inputs, outputs, selected: Boolean(key)};
  }

  function trace(key) {
    let current = null;
    for (const svg of document.querySelectorAll('.depgraph')) {
      const counts = paintGraph(svg, key);
      if (svg === activeSvg(dialog.open ? 'map' : 'page')) current = counts;
    }
    const message = document.querySelector('.graphstatus');
    if (!key || !current?.selected) {
      message.textContent = 'Select a node to read its card. Select an arrow to open its witness in a new tab.';
    } else {
      message.textContent = `${key} · ${current.inputs.size} visible prerequisites · ${current.outputs.size} visible consumers.`;
    }
  }

  function applyFilters(scope) {
    const shown = new Set(Array.from(document.querySelectorAll(`[data-filters="${scope}"] input[data-diff]`))
      .filter(input => input.checked).map(input => input.dataset.diff));
    const svgs = scope === 'map' ? [stage] : Array.from(document.querySelectorAll('.graphview'));
    for (const root of svgs) {
      for (const edge of root.querySelectorAll('.depedge')) edge.toggleAttribute('hidden', !shown.has(edge.dataset.diff));
    }
    const svg = activeSvg(scope);
    for (const count of document.querySelectorAll(`[data-filters="${scope}"] [data-count]`)) {
      const n = svg ? svg.querySelectorAll(`.depedge[data-diff="${count.dataset.count}"]`).length : 0;
      count.textContent = `(${n})`;
    }
    trace(hovering || selected);
  }

  function typeset(element) {
    const mathjax = window.MathJax;
    // Before MathJax has loaded, its first page pass also covers the panel.
    if (mathjax?.typesetPromise) {
      mathjax.startup.promise.then(() => mathjax.typesetPromise([element])).catch(() => {});
    }
  }

  function relationList(key) {
    const svg = activeSvg(dialog.open ? 'map' : 'page');
    const owner = svg && graphNode(svg, key)?.dataset.node;
    const lists = {prerequisites: [], consumers: []};
    if (!owner) return null;
    for (const edge of svg.querySelectorAll('.depedge')) {
      if (edge.dataset.to === owner) lists.prerequisites.push([edge, edge.dataset.from]);
      if (edge.dataset.from === owner) lists.consumers.push([edge, edge.dataset.to]);
    }
    const section = document.createElement('section');
    section.className = 'relations';
    for (const [heading, items] of [['Prerequisites', lists.prerequisites], ['Consumers', lists.consumers]]) {
      const title = document.createElement('h4');
      title.textContent = `${heading} in this graph · ${items.length}`;
      section.append(title);
      for (const [diff, label] of diffTitles) {
        const matching = items.filter(([edge]) => edge.dataset.diff === diff);
        if (!matching.length) continue;
        const group = document.createElement('div');
        group.className = 'relation-group';
        const caption = document.createElement('p');
        caption.className = 'relation-class';
        caption.innerHTML = `<span class="swatch diff-${diff}" aria-hidden="true"></span>`;
        caption.append(label);
        const list = document.createElement('ul');
        list.className = 'relation-list';
        for (const [edge, other] of matching) {
          const item = document.createElement('li');
          const button = document.createElement('button');
          button.className = 'relation';
          button.dataset.selectNode = other;
          button.textContent = nameOf(other);
          item.append(button);
          if (edge.dataset.members) {
            const note = document.createElement('span');
            note.className = 'mini muted';
            note.textContent = ` · ${edge.dataset.members.split(' ').length} folded connections`;
            item.append(note);
          } else {
            const witness = document.createElement('a');
            witness.href = edge.dataset.audit;
            witness.target = '_blank';
            witness.rel = 'noopener';
            witness.className = 'mini';
            witness.textContent = 'witness ↗';
            item.append(' ', witness);
          }
          if (edge.hasAttribute('hidden')) item.classList.add('filtered');
          list.append(item);
        }
        group.append(caption, list);
        section.append(group);
      }
    }
    return section;
  }

  function fillRelations() {
    if (panel.hidden || !selected) return;
    const slot = panelBody.querySelector('[data-relations]');
    if (slot) slot.replaceChildren(...[relationList(selected)].filter(Boolean));
  }

  let cardPage = null;

  function loadCards() {
    // Every card is stored once, in atlas-cards.html, and read on first use.
    cardPage ||= fetch('atlas-cards.html').then(response => {
      if (!response.ok) throw new Error(`Cannot load the node cards (${response.status})`);
      return response.text();
    }).then(text => new DOMParser().parseFromString(text, 'text/html'));
    return cardPage;
  }

  async function cardContent(key) {
    const template = document.getElementById('card-' + key);
    if (template) return template.content.cloneNode(true);
    const card = (await loadCards()).getElementById('node-' + key);
    if (!card) throw new Error(`No card for ${key}`);
    const content = document.createDocumentFragment();
    for (const child of card.childNodes) content.append(document.importNode(child, true));
    content.querySelector('.card-links')?.remove();
    const relations = document.createElement('div');
    relations.className = 'card-relations';
    relations.dataset.relations = '';
    const actions = document.createElement('div');
    actions.className = 'jump';
    actions.innerHTML = '<button data-focus-node></button><a target="_blank" rel="noopener">Compare recorded connections</a>';
    actions.firstChild.dataset.focusNode = key;
    actions.firstChild.textContent = 'Locate in unified graph';
    actions.lastChild.href = 'atlas-audit.html#expert-connections';
    content.append(relations, actions);
    return content;
  }

  async function openPanel(key) {
    if (panel.hidden) returnFocus = document.activeElement;
    panelTitle.textContent = nameOf(key);
    panel.hidden = false;
    document.body.classList.add('panel-open');
    let content;
    try {
      content = await cardContent(key);
    } catch (error) {
      content = document.createElement('p');
      content.className = 'muted';
      content.textContent = error.message + '. Open atlas-cards.html to read every card.';
    }
    if (selected !== key) return;
    window.MathJax?.typesetClear?.([panelBody]);
    panelBody.replaceChildren(content);
    fillRelations();
    typeset(panelBody);
    panelBody.scrollTop = 0;
    panelTitle.focus({preventScroll: true});
  }

  function closePanel() {
    if (panel.hidden) return;
    panel.hidden = true;
    document.body.classList.remove('panel-open');
    selected = hovering = null;
    trace(null);
    history.replaceState(null, '', location.pathname + location.search);
    if (returnFocus?.isConnected) returnFocus.focus({preventScroll: true});
    returnFocus = null;
  }

  function centre(container, element) {
    if (!element) return;
    const rect = element.getBoundingClientRect();
    const parent = container.getBoundingClientRect();
    // On narrow screens the panel is a bottom sheet over part of the graph.
    const sheet = !panel.hidden && matchMedia('(max-width: 1000px)').matches ? panel.offsetHeight : 0;
    const top = Math.max(parent.top, 0);
    const bottom = Math.max(top + 40, Math.min(parent.bottom, innerHeight - sheet));
    container.scrollLeft += rect.left - parent.left + rect.width / 2 - parent.width / 2;
    container.scrollTop += rect.top - top + rect.height / 2 - (bottom - top) / 2;
  }

  function keepInside(container, element) {
    // The panel narrows the graph; a selection near its edge is panned into view.
    if (!element) return;
    const rect = element.getBoundingClientRect();
    const box = container.getBoundingClientRect();
    if (rect.left < box.left || rect.right > box.right || rect.top < box.top || rect.bottom > box.bottom) {
      centre(container, element);
    }
  }

  function keepUncovered(container, element) {
    // On narrow screens the panel is a bottom sheet; never leave the selection under it.
    if (!element || panel.hidden || !matchMedia('(max-width: 1000px)').matches) return;
    const limit = innerHeight - panel.offsetHeight - 12;
    if (element.getBoundingClientRect().bottom <= limit) return;
    centre(container, element);
    const bottom = element.getBoundingClientRect().bottom;
    if (bottom > limit) window.scrollBy(0, bottom - limit);
  }

  async function selectNode(key, origin = 'graph') {
    if (!byId.has(key) && !document.getElementById('card-' + key)) return;
    selected = key;
    hovering = null;
    history.replaceState(null, '', '#node-' + encodeURIComponent(key));
    if (dialog.open) {
      const external = externalOf(key);
      if (!stage.querySelector(`.graphnode[data-node="${CSS.escape(key)}"]`) && external && variants.has('expand-' + external)) {
        await loadVariant('expand-' + external);
      }
      openPanel(key);
      trace(key);
      const element = graphNode(stage.querySelector('.depgraph'), key);
      if (origin !== 'graph') centre(stage, element);
      else keepInside(stage, element);
      keepUncovered(stage, element);
      return;
    }
    if (key.startsWith('group-')) { openMap(key); return; }
    const contains = view => Boolean(document.querySelector(`#view-${CSS.escape(view)} .graphnode[data-node="${CSS.escape(key)}"]`));
    if (!contains(activeView)) {
      const other = Array.from(document.querySelectorAll('.viewbtn')).map(button => button.dataset.view).find(contains);
      if (!other) { openMap(key); return; }
      switchView(other);
    }
    openPanel(key);
    trace(key);
    if (origin === 'index' || origin === 'hash') document.querySelector('.graphs').scrollIntoView({block: 'start'});
    const container = document.querySelector(`#view-${CSS.escape(activeView)} .diagram-scroll`);
    const element = graphNode(container, key);
    if (origin !== 'graph') centre(container, element);
    else keepInside(container, element);
    keepUncovered(container, element);
  }

  async function openGroup(name) {
    if (variants.has('expand-' + name)) await loadVariant('expand-' + name);
    selected = 'group-' + name;
    openPanel('group-' + name);
    trace(null);
    centre(stage, stage.querySelector(`[data-external-group="${CSS.escape(name)}"]`));
  }

  function zoom(container, scale, centrePoint = null) {
    const svg = container.querySelector('.depgraph');
    if (!svg || !container.clientWidth) return;
    const box = svg.viewBox.baseVal;
    const oldScale = scales.get(container) || svg.getBoundingClientRect().width / box.width;
    const next = Math.max(0.005, Math.min(4, scale));
    const anchor = centrePoint || {x: container.clientWidth / 2, y: container.clientHeight / 2};
    const left = (container.scrollLeft + anchor.x) / oldScale;
    const top = (container.scrollTop + anchor.y) / oldScale;
    svg.style.width = `${box.width * next}px`;
    scales.set(container, next);
    container.scrollLeft = left * next - anchor.x;
    container.scrollTop = top * next - anchor.y;
    const region = container.closest('.graphview') || dialog;
    region.querySelector('output').textContent = Math.round(next * 100) + '%';
  }

  function fit(container) {
    const svg = container.querySelector('.depgraph');
    container.style.height = '';
    if (svg) zoom(container, (container.clientWidth - 4) / svg.viewBox.baseVal.width, {x: 0, y: 0});
  }

  function focusExternal(key) {
    const view = document.getElementById('view-external');
    const container = view.querySelector('.diagram-scroll');
    const frame = container.querySelector(`[data-external-group="${CSS.escape(key)}"]`);
    if (!frame) return;
    closePanel();
    const bounds = frame.getBBox();
    const scale = Math.max(0.75, Math.min(1, (container.clientWidth - 36) / bounds.width));
    container.style.height = `${Math.max(220, bounds.height * scale + 32)}px`;
    zoom(container, scale, {x: 0, y: 0});
    const rect = frame.getBoundingClientRect();
    const parent = container.getBoundingClientRect();
    container.scrollLeft += rect.left - parent.left - 16;
    container.scrollTop += rect.top - parent.top - 16;
    for (const button of view.querySelectorAll('button[data-external-group]')) {
      const active = button.dataset.externalGroup === key;
      button.classList.toggle('active', active);
      button.setAttribute('aria-pressed', String(active));
    }
  }

  function initContainer(container) {
    if (container.dataset.initialized) return;
    container.dataset.initialized = 'true';
    let drag = null;
    container.addEventListener('pointerdown', event => {
      if (event.button !== 0 || event.target.closest('.graphnode, .depedge, a')) return;
      drag = {x: event.clientX, y: event.clientY, left: container.scrollLeft, top: container.scrollTop};
      container.setPointerCapture(event.pointerId);
    });
    container.addEventListener('pointermove', event => {
      if (!drag) return;
      const dx = event.clientX - drag.x;
      const dy = event.clientY - drag.y;
      if (Math.abs(dx) + Math.abs(dy) > 4) container.classList.add('dragging');
      container.scrollLeft = drag.left - dx;
      container.scrollTop = drag.top - dy;
    });
    const endDrag = () => { drag = null; container.classList.remove('dragging'); };
    container.addEventListener('pointerup', endDrag);
    container.addEventListener('pointercancel', endDrag);
    container.addEventListener('lostpointercapture', endDrag);
    container.addEventListener('wheel', event => {
      if (!event.ctrlKey && container !== stage) return;
      event.preventDefault();
      const rect = container.getBoundingClientRect();
      const svg = container.querySelector('.depgraph');
      if (!svg) return;
      const scale = scales.get(container) || svg.getBoundingClientRect().width / svg.viewBox.baseVal.width;
      zoom(container, scale * Math.exp(-event.deltaY * 0.002), {x: event.clientX - rect.left, y: event.clientY - rect.top});
    }, {passive: false});
  }

  function switchView(key, scroll = false) {
    const view = document.getElementById('view-' + key);
    if (!view) return;
    activeView = key;
    for (const other of document.querySelectorAll('.graphview')) other.hidden = other !== view;
    for (const button of document.querySelectorAll('.viewbtn')) {
      const active = button.dataset.view === key;
      button.classList.toggle('active', active);
      button.setAttribute('aria-pressed', String(active));
    }
    const container = view.querySelector('.diagram-scroll');
    if (!scales.has(container)) {
      const svg = container.querySelector('.depgraph');
      const fitScale = (container.clientWidth - 4) / svg.viewBox.baseVal.width;
      zoom(container, Math.max(0.9, fitScale), {x: 0, y: 0});
      container.scrollLeft = Math.max(0, (svg.getBoundingClientRect().width - container.clientWidth) / 2);
      if (key === 'external') {
        const firstGroup = view.querySelector('button[data-external-group]');
        if (firstGroup) focusExternal(firstGroup.dataset.externalGroup);
      }
    }
    applyFilters('page');
    fillRelations();
    if (scroll) document.querySelector('.graphs').scrollIntoView({behavior: 'auto', block: 'start'});
  }

  async function loadVariant(id) {
    if (!variants.has(id)) id = 'collapsed';
    if (variant === id && stage.querySelector('svg')) return;
    if (!svgCache.has(id)) {
      const response = await fetch(`atlas-unified-${id}.svg`);
      if (!response.ok) throw new Error(`Cannot load the unified graph (${response.status})`);
      svgCache.set(id, await response.text());
    }
    const parsed = new DOMParser().parseFromString(svgCache.get(id), 'image/svg+xml').documentElement;
    const previous = scales.get(stage) || 1;
    stage.replaceChildren(document.importNode(parsed, true));
    scales.delete(stage);
    variant = id;
    zoom(stage, previous, {x: 0, y: 0});
    const open = id === 'full' ? 'All External frames open'
      : id === 'collapsed' ? 'All External frames folded' : 'Open frame: ' + groupTitle(id.slice(7));
    document.getElementById('variant-status').textContent = open;
    applyFilters('map');
    fillRelations();
  }

  async function openMap(key = null) {
    key = key || selected || dialog.dataset.rootNode;
    if (!dialog.open) {
      dialog.append(panel);
      dialog.showModal();
    }
    initContainer(stage);
    const external = key && externalOf(key);
    const wanted = key?.startsWith('group-') ? 'expand-' + key.slice(6)
      : external && variants.has('expand-' + external) ? (variant === 'full' ? 'full' : 'expand-' + external)
        : (variant || 'collapsed');
    try {
      await loadVariant(wanted);
    } catch (error) {
      document.getElementById('variant-status').textContent = error.message;
      return;
    }
    if (key?.startsWith('group-')) { openGroup(key.slice(6)); return; }
    if (key) await selectNode(key, 'map');
  }

  dialog.addEventListener('close', () => {
    document.body.append(panel);
    fillRelations();
    trace(selected);
  });
  dialog.addEventListener('cancel', event => {
    if (!panel.hidden) { event.preventDefault(); closePanel(); }
  });

  document.addEventListener('click', event => {
    if (event.ctrlKey || event.metaKey || event.shiftKey || event.altKey) return;
    const node = event.target.closest('.graphnode');
    if (node) {
      event.preventDefault();
      if (node.classList.contains('groupnode')) openGroup(node.dataset.group);
      else selectNode(node.dataset.node);
      return;
    }
    const edge = event.target.closest('.depedge');
    if (edge) {
      event.preventDefault();
      // A folded arrow stands for several connections: open the frame to show them.
      const folded = edge.dataset.members && [edge.dataset.from, edge.dataset.to].find(end => end.startsWith('group-'));
      if (folded) openGroup(folded.slice(6));
      else window.open(edge.dataset.audit, '_blank', 'noopener');
      return;
    }
    const choose = event.target.closest('[data-select-node]');
    if (choose) { event.preventDefault(); selectNode(choose.dataset.selectNode, choose.closest('#node-index') ? 'index' : 'panel'); return; }
    const view = event.target.closest('.viewbtn');
    if (view) { switchView(view.dataset.view, true); return; }
    const externalGroup = event.target.closest('button[data-external-group]');
    if (externalGroup) { focusExternal(externalGroup.dataset.externalGroup); return; }
    if (event.target.closest('[data-open-map]')) { openMap(); return; }
    const locate = event.target.closest('[data-focus-node]');
    if (locate) { openMap(locate.dataset.focusNode); return; }
    const choice = event.target.closest('[data-variant]');
    if (choice) { loadVariant(choice.dataset.variant).then(() => trace(selected)); return; }
    if (event.target.closest('#details-close')) { closePanel(); return; }
    const action = event.target.closest('[data-action]');
    if (action) {
      const region = action.closest('.graphview') || dialog;
      const container = region.querySelector('.diagram-scroll');
      const current = scales.get(container) || 1;
      if (action.dataset.action === 'fit') fit(container);
      if (action.dataset.action === 'readable') zoom(container, 1);
      if (action.dataset.action === 'in') zoom(container, current * 1.25);
      if (action.dataset.action === 'out') zoom(container, current / 1.25);
      if (action.dataset.action === 'clear') closePanel();
    }
  });

  document.addEventListener('keydown', event => {
    if (event.key === 'Escape' && !dialog.open && !panel.hidden) { closePanel(); return; }
    if (!['Enter', ' '].includes(event.key)) return;
    const node = event.target.closest('.graphnode');
    const edge = event.target.closest('.depedge');
    if (node || edge) {
      event.preventDefault();
      event.target.dispatchEvent(new MouseEvent('click', {bubbles: true}));
    }
  });
  document.addEventListener('pointerover', event => {
    const node = event.target.closest('.graphnode');
    if (node && node.dataset.node !== hovering) { hovering = node.dataset.node; trace(hovering); }
  });
  document.addEventListener('pointerout', event => {
    const node = event.target.closest('.graphnode');
    if (node && !node.contains(event.relatedTarget)) { hovering = null; trace(selected); }
  });
  document.getElementById('close-map').addEventListener('click', () => dialog.close());
  document.getElementById('reset-filters').addEventListener('click', resetFilters);
  search.addEventListener('input', filterRows);
  group.addEventListener('change', filterRows);
  status.addEventListener('change', filterRows);
  for (const input of document.querySelectorAll('[data-filters] input[data-diff]')) {
    input.addEventListener('change', () => { applyFilters(scopeOf(input)); fillRelations(); });
  }
  document.querySelectorAll('.diagram-scroll').forEach(initContainer);
  filterRows();
  switchView(activeView);
  const readHash = () => {
    if (location.hash.startsWith('#node-')) {
      try { selectNode(decodeURIComponent(location.hash.slice(6)), 'hash'); } catch (_) { /* Ignore malformed links. */ }
    }
  };
  window.addEventListener('hashchange', readHash);
  readHash();
})();
