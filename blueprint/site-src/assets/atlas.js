'use strict';

(() => {
  const cards = Array.from(document.querySelectorAll('.nodecard'));
  const byId = new Map(cards.map(card => [card.id.slice(5), card]));
  const search = document.getElementById('search');
  const group = document.getElementById('group-filter');
  const status = document.getElementById('status-filter');
  const dialog = document.getElementById('unified-map');
  const stage = document.getElementById('map-stage');
  const actualToggle = document.getElementById('show-actual');
  const expertToggle = document.getElementById('show-expert');
  const scales = new WeakMap();
  let selected = null;
  let hovering = null;
  let activeView = 'overview';

  function filterCards() {
    const query = search.value.trim().toLowerCase();
    let count = 0;
    for (const card of cards) {
      card.hidden = Boolean((query && !card.dataset.search.includes(query)) ||
        (group.value && group.value !== card.dataset.group) ||
        (status.value && status.value !== card.dataset.status));
      if (!card.hidden) count += 1;
    }
    document.getElementById('card-count').textContent = `${count} of ${cards.length} node cards`;
    document.getElementById('no-results').hidden = count !== 0;
  }

  function resetFilters() {
    search.value = group.value = status.value = '';
    filterCards();
  }

  function paintGraph(svg, key) {
    // A selection in another branch should not fade this entire view.
    const graphNodes = Array.from(svg.querySelectorAll('.graphnode'));
    if (key && !graphNodes.some(node => node.dataset.node === key)) key = null;
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
    for (const node of graphNodes) {
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
      if (svg.dataset.view === activeView) current = counts;
    }
    const message = document.querySelector('.graphstatus');
    if (!key || !current?.selected) {
      message.textContent = 'Select a node to read its card. Select an arrow to inspect its witness.';
    } else if (current) {
      message.textContent = `${key} · ${current.inputs.size} visible prerequisites · ${current.outputs.size} visible consumers. Edge styles retain their evidence meaning.`;
    }
  }

  function selectNode(key, scroll = true) {
    const card = byId.get(key);
    if (!card) return;
    selected = key;
    hovering = null;
    for (const other of cards) other.classList.toggle('selected', other === card);
    if (card.hidden) resetFilters();
    trace(key);
    if (scroll) {
      if (dialog.open) dialog.close();
      history.replaceState(null, '', '#node-' + encodeURIComponent(key));
      card.setAttribute('tabindex', '-1');
      card.focus({preventScroll: true});
      card.scrollIntoView({behavior: 'auto', block: 'start'});
    }
  }

  function clearSelection() {
    selected = hovering = null;
    cards.forEach(card => card.classList.remove('selected'));
    trace(null);
  }

  function zoom(container, scale, centre = null) {
    const svg = container.querySelector('.depgraph');
    if (!svg || !container.clientWidth) return;
    const box = svg.viewBox.baseVal;
    const oldScale = scales.get(container) || svg.getBoundingClientRect().width / box.width;
    const next = Math.max(0.005, Math.min(4, scale));
    const anchor = centre || {x: container.clientWidth / 2, y: container.clientHeight / 2};
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
    clearSelection();
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
    trace(selected);
    if (scroll) document.querySelector('.graphs').scrollIntoView({behavior: 'auto', block: 'start'});
  }

  function applyEdgeFilters() {
    for (const edge of document.querySelectorAll('.depedge')) {
      const show = edge.dataset.kind === 'actual' ? actualToggle.checked : expertToggle.checked;
      edge.toggleAttribute('hidden', !show);
    }
    trace(hovering || selected);
  }

  function openMap(key = null) {
    key = key || selected || dialog.dataset.rootNode;
    if (!stage.querySelector('svg')) {
      const copy = document.getElementById('graph-all').cloneNode(true);
      for (const element of [copy, ...copy.querySelectorAll('[id]')]) element.id = 'dialog-' + element.id;
      stage.append(copy);
      initContainer(stage);
    }
    if (!dialog.open) dialog.showModal();
    if (!scales.has(stage)) zoom(stage, 1, {x: 0, y: 0});
    applyEdgeFilters();
    if (key) {
      selectNode(key, false);
      const node = Array.from(stage.querySelectorAll('.graphnode')).find(item => item.dataset.node === key);
      if (node) {
        const rect = node.getBoundingClientRect();
        const parent = stage.getBoundingClientRect();
        stage.scrollLeft += rect.left - parent.left + rect.width / 2 - parent.width / 2;
        stage.scrollTop += rect.top - parent.top + rect.height / 2 - parent.height / 2;
        node.focus({preventScroll: true});
      }
    }
  }

  document.addEventListener('click', event => {
    if (event.ctrlKey || event.metaKey || event.shiftKey || event.altKey) return;
    const graphNode = event.target.closest('.graphnode');
    if (graphNode) { event.preventDefault(); selectNode(graphNode.dataset.node); return; }
    const edge = event.target.closest('.depedge');
    if (edge) { event.preventDefault(); location.assign(edge.dataset.audit); return; }
    const view = event.target.closest('.viewbtn');
    if (view) { switchView(view.dataset.view, true); return; }
    const externalGroup = event.target.closest('button[data-external-group]');
    if (externalGroup) { focusExternal(externalGroup.dataset.externalGroup); return; }
    if (event.target.closest('[data-open-map]')) { openMap(); return; }
    const locate = event.target.closest('[data-focus-node]');
    if (locate) { openMap(locate.dataset.focusNode); return; }
    const action = event.target.closest('[data-action]');
    if (action) {
      const region = action.closest('.graphview') || dialog;
      const container = region.querySelector('.diagram-scroll');
      const current = scales.get(container) || 1;
      if (action.dataset.action === 'fit') fit(container);
      if (action.dataset.action === 'readable') zoom(container, 1);
      if (action.dataset.action === 'in') zoom(container, current * 1.25);
      if (action.dataset.action === 'out') zoom(container, current / 1.25);
      if (action.dataset.action === 'clear') clearSelection();
    }
  });

  document.addEventListener('keydown', event => {
    if (!['Enter', ' '].includes(event.key)) return;
    const node = event.target.closest('.graphnode');
    const edge = event.target.closest('.depedge');
    if (node) { event.preventDefault(); selectNode(node.dataset.node); }
    else if (edge) { event.preventDefault(); location.assign(edge.dataset.audit); }
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
  search.addEventListener('input', filterCards);
  group.addEventListener('change', filterCards);
  status.addEventListener('change', filterCards);
  actualToggle.addEventListener('change', applyEdgeFilters);
  expertToggle.addEventListener('change', applyEdgeFilters);
  document.querySelectorAll('.diagram-scroll').forEach(initContainer);
  filterCards();
  switchView(activeView);
  const readHash = () => {
    if (location.hash.startsWith('#node-')) {
      try { selectNode(decodeURIComponent(location.hash.slice(6))); } catch (_) { /* Ignore malformed links. */ }
    }
  };
  window.addEventListener('hashchange', readHash);
  readHash();
})();
