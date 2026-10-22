"""Build prototype data from a built blueprint site: layouts via dot -Tjson, cards, a chapter.

Run after build.py, then assemble.py:
    python3 blueprint/prototype/prep.py blueprint/build/redesign/data
    python -I blueprint/prototype/assemble.py
prep.py needs BeautifulSoup and assemble.py needs markdown-it-py; neither is a site build dependency.
"""
import json, re, subprocess, sys, textwrap
from pathlib import Path
from bs4 import BeautifulSoup

BP = Path(__file__).resolve().parents[1]
OUT = Path(sys.argv[1])
sys.path.insert(0, str(BP / 'scripts'))
from atlas_render import node_heading, plain, PALETTE, STATUS, edge_id
from atlas import collapse_view, collapsible_groups, declaration_role

atlas = json.loads((BP / 'site/blueprint/atlas-dependencies.json').read_text())
nodes = {n['id']: n for n in atlas['nodes']}
groups = {g['id']: g for g in atlas['external_groups']}

W = 216            # node width in px (= pt for Graphviz)
HEAD, SUMM = 23, 30  # wrap widths in characters


def label_lines(n):
    h, s = node_heading(n)
    h, s = plain(h).strip().rstrip(':'), plain(s).strip()
    hl = textwrap.wrap(h, HEAD, break_long_words=False) or [n['id']]
    if len(hl) > 2:
        hl = hl[:2]
        hl[1] = hl[1][:HEAD - 1].rstrip(' ,;') + '…'
    sl = textwrap.wrap(s, SUMM, break_long_words=False)
    if len(sl) > 2:
        sl = sl[:2]
        sl[1] = sl[1][:SUMM - 1].rstrip() + '…'
    return hl, sl


def size(key):
    if key.startswith('group-'):
        return W + 24, 70
    hl, sl = label_lines(nodes[key])
    return W, round(16 + 17 * len(hl) + 15.5 * len(sl), 1)


def layout(view):
    q = json.dumps
    dot = ['digraph G {', 'graph [rankdir=BT, nodesep=0.28, ranksep=0.55, newrank=true, compound=true, pad=0.2];',
           'node [shape=box, fixedsize=true, label=""];', 'edge [arrowhead=none];']
    folded = {'group-' + g for g in view.get('collapsed', [])}
    ext = [k for k in view['nodes'] if k in folded or (k in nodes and nodes[k]['external_group'])]
    for k in view['nodes']:
        if k not in ext:
            w, h = size(k); dot.append(f'{q(k)} [width={w/72:.3f}, height={h/72:.3f}];')
    if ext:
        dot.append('subgraph cluster_external { graph [margin=18, label=" ", fontsize=22];')
        for k in ext:
            if k in folded:
                w, h = size(k); dot.append(f'{q(k)} [width={w/72:.3f}, height={h/72:.3f}];')
        for g in atlas['external_groups']:
            mem = [k for k in ext if k not in folded and nodes[k]['external_group'] == g['id']]
            if not mem: continue
            dot.append(f'subgraph cluster_{g["id"]} {{ graph [margin=12, label=" ", fontsize=18];')
            for k in mem:
                w, h = size(k); dot.append(f'{q(k)} [width={w/72:.3f}, height={h/72:.3f}];')
            dot.append('}')
        dot.append('}')
    for i, e in enumerate(view['edges']):
        extra = ', weight=0.3' if e['kind'] != 'actual' else ''
        dot.append(f'{q(e["from"])} -> {q(e["to"])} [id="e{i}"{extra}];')
    dot.append('}')
    res = json.loads(subprocess.run(['dot', '-Tjson'], input='\n'.join(dot), capture_output=True, text=True, check=True).stdout)
    x0, y0, x1, y1 = map(float, res['bb'].split(','))
    flip = lambda x, y: (round(x - x0), round(y1 - y))
    pos, clusters = {}, []
    for o in res.get('objects', []):
        if o['name'].startswith('cluster_'):
            a, b, c, d = map(float, o['bb'].split(','))
            (ax, ay), (cx, cy) = flip(a, d), flip(c, b)
            clusters.append({'id': o['name'][8:], 'x': ax, 'y': ay, 'w': cx - ax, 'h': cy - ay})
        elif 'pos' in o:
            x, y = map(float, o['pos'].split(','))
            fx, fy = flip(x, y)
            w, h = float(o['width']) * 72, float(o['height']) * 72
            pos[o['name']] = [round(fx - w / 2), round(fy - h / 2), round(w, 1), round(h, 1)]
    paths = {}
    for e in res.get('edges', []):
        pts = [tuple(map(float, p.split(','))) for p in e['pos'].split(' ') if not p.startswith(('e,', 's,'))]
        pts = [flip(*p) for p in pts]
        d = f'M{pts[0][0]},{pts[0][1]}' + ''.join(
            f'C{pts[i][0]},{pts[i][1]} {pts[i+1][0]},{pts[i+1][1]} {pts[i+2][0]},{pts[i+2][1]}' for i in range(1, len(pts) - 2, 3))
        paths[int(e['id'][1:])] = d
    edges = []
    for i, e in enumerate(view['edges']):
        rec = {'from': e['from'], 'to': e['to'], 'kind': e['kind'], 'diff': e['diff'], 'd': paths[i]}
        if e.get('members'): rec['members'] = [[m['from'], m['to'], m['kind']] for m in e['members']]
        edges.append(rec)
    return {'id': view['id'], 'w': round(x1 - x0), 'h': round(y1 - y0), 'nodes': pos, 'edges': edges,
            'clusters': clusters, 'collapsed': view.get('collapsed', [])}


views = [v for v in atlas['views'] if v['id'] != 'all']
unified = atlas['views'][-1]
gs = collapsible_groups(unified, nodes)
variants = [collapse_view(unified, nodes, gs, 'all', 'Whole proof')]
variants += [collapse_view(unified, nodes, [o for o in gs if o != g], 'all-' + g, 'Whole proof') for g in gs]
variants.append({**unified, 'id': 'all-full', 'collapsed': []})
layouts = {v['id']: layout(v) for v in views + variants}

# Connections, deduplicated across every view; the unified graph has the complete set.
edge_info = {}
for v in atlas['views']:
    for e in v['edges']:
        k = (e['from'], e['to'], e['kind'])
        edge_info.setdefault(k, {'from': e['from'], 'to': e['to'], 'kind': e['kind'], 'diff': e['diff'], 'path': e.get('path', []),
                                 'classification': e.get('classification'), 'reason': e.get('reason'),
                                 'expert_kind': e.get('expert_kind'), 'expert_note': e.get('expert_note'), 'audit': edge_id(e)})

# Cards: reviewed manuscript statements and remark links from the generated card page.
soup = BeautifulSoup((BP / 'site/blueprint/atlas-cards.html').read_text(), 'html.parser')
cards = {}
for art in soup.select('article.nodecard'):
    key = art['id'][5:]
    sts = []
    for sec in art.select('section.mathematical-statement'):
        h = sec.find('h4'); link = sec.select_one('.statement-link a')
        heading = h.get_text(' ', strip=True).removeprefix('Reviewed manuscript · ') if h else ''
        if h: h.decompose()
        url = link['href'] if link else None
        if link: link.parent.decompose()
        for tag in sec.find_all(id=True): del tag['id']
        sts.append({'heading': heading, 'url': url, 'html': sec.decode_contents().strip()})
    exp = art.select_one('details.expert-formulation')
    expert_html = ''
    if exp:
        exp.find('summary').decompose(); [p.decompose() for p in exp.select('p.mini')]
        expert_html = exp.decode_contents().strip()
    remark_links = [{'label': a.get_text(strip=True), 'url': a['href']} for a in art.select('.remark-links a')]
    cards[key] = {'statements': sts, 'expert_html': expert_html, 'remark_links': remark_links}

out_nodes = []
for n in atlas['nodes']:
    hl, sl = label_lines(n)
    vs = []
    for v in n['versions']:
        vs.append({'name': v['name'], 'kind': v['kind'], 'role': declaration_role(v), 'reached': v['reached'],
                   'module': v['module'], 'line': v.get('line'), 'type': v.get('expanded_type') or v.get('type'),
                   'definition': v.get('definition'), 'path': v.get('path', [])})
    out_nodes.append({'id': n['id'], 'group': n['group'], 'expert': n['expert'], 'origin': n.get('origin'),
                      'paper': n['paper'], 'title': n['title'], 'source': n.get('source'),
                      'heading': hl, 'summary': sl, 'full_heading': plain(node_heading(n)[0]).strip().rstrip(':'), 'status': n['status'], 'primary': n['primary'],
                      'external': n['external_group'], 'remark': n['remark'], 'labels': n['labels'],
                      'versions': vs, **cards.get(n['id'], {})})

data = {'root': atlas['root'], 'root_node': atlas['root_node'], 'counts': atlas['counts'],
        'revision': atlas['provenance']['revision'],
        'views': [{'id': v['id'], 'title': v['title'], 'description': v['description'], 'count': len(v['nodes'])} for v in views],
        'groups': [{'id': g['id'], 'title': g['title']} for g in atlas['external_groups']],
        'palette': {k: v[0] for k, v in PALETTE.items()}, 'status': STATUS,
        'nodes': out_nodes, 'edges': list(edge_info.values())}
OUT.mkdir(parents=True, exist_ok=True)
(OUT / 'atlas.json').write_text(json.dumps(data, ensure_ascii=False, separators=(',', ':')))
(OUT / 'layouts.json').write_text(json.dumps(layouts, ensure_ascii=False, separators=(',', ':')))

# One manuscript chapter, as plasTeX renders it, for the reskin demonstration.
ch = BeautifulSoup((BP / 'site/blueprint/chap-sticky.html').read_text(), 'html.parser')
main = ch.select_one('.main-text')
# Keep the manuscript's Lean links and completion marks as data; drop the theme's icon popups.
for head in main.select('[class$="_thmheading"]'):
    extras = head.select_one('.thm_header_extras')
    hidden = head.select_one('.thm_header_hidden_extras')
    decls = [a.get_text(strip=True) for a in head.select('a.lean_decl')]
    wrapper = head.parent
    wrapper['data-decls'] = ' '.join(decls)
    if extras and '✓' in extras.get_text():
        wrapper['data-leanok'] = ''
    for tag in (extras, hidden):
        if tag: tag.decompose()
toc = [{'href': a['href'], 'ref': a.select_one('.toc_ref').get_text(strip=True) if a.select_one('.toc_ref') else '',
        'title': a.select_one('.toc_entry').get_text(' ', strip=True) if a.select_one('.toc_entry') else a.get_text(' ', strip=True)}
       for a in ch.select('nav.toc > ul.sub-toc-0 > li > a') if 'dep_graph' not in a['href']]
(OUT / 'chapter.json').write_text(json.dumps({'html': main.decode_contents(), 'toc': toc}, ensure_ascii=False))
for f in OUT.iterdir(): print(f.name, f.stat().st_size)
print({k: (v['w'], v['h'], len(v['nodes'])) for k, v in layouts.items()})
