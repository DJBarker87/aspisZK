#!/bin/bash
# PCXB_compose1.sh: per-module tables (annotated definitions, arithmetic class, group, candidates) for every emitted module in scope.
cd /Users/dominic/ZK/.worktrees/pc-prov-p6c/evidence/prov-p6c-20261109
python3 -I -B - <<'PY'
import sys, json, re, collections
sys.path.insert(0, '.')
import PCXB_lib as L
pco = L.J('prov-p0-20261109/PCO_PARTITION.json')['modules']
em = json.load(open(L.SCR + '/emods_decl.json'))
sb = L.J('prov-p6c-20261109/PCXB_SPLITB_HITS.json')['modules']
hits = json.load(open(L.SCR + '/emod_hits.json')); roots = json.load(open(L.SCR + '/roots.json'))
closed_names = collections.defaultdict(set); closed_rows = collections.defaultdict(lambda: collections.defaultdict(set))
for r, h in hits.items():
    for m, ns in h.items():
        closed_names[m] |= set(ns)
        for row in roots[r]: closed_rows[m][row] |= set(ns)
scope = sorted(set(sb) | {m for m, v in pco.items() if v['relied']})
out = {}
for m in scope:
    v = em[m]; cl = {}
    texts = {}
    for s in v['candidates']:
        t = L.blob_text(s); texts[s] = t
    ann = set(); cls = {}
    for s, t in texts.items():
        nsm = re.search(r'(?m)^namespace (\S+)', t); nsp = nsm.group(1) if nsm else ''
        for seg in L.PCOP.segments(t):
            hm = re.search(r'\b(?:def|abbrev|structure|inductive|opaque|axiom|theorem|instance)\s+(\S+)', seg['head'])
            if hm: ann.add((nsp + '.' if nsp else '') + hm.group(1))
        for n, k, b in L.decl_segments(t):
            c = L.arith_class(b)
            cls[n] = c if n not in cls or cls[n] == c else 'DIFFERS_BETWEEN_CANDIDATES'
    out[m] = dict(annotated=sorted(ann), arith=cls, n_candidates=len(texts),
                  splitB_names=sb.get(m, []), closed_names=sorted(closed_names.get(m, [])))
json.dump(out, open(L.SCR + '/compose1.json', 'w'))
json.dump({m: {r: sorted(ns) for r, ns in d.items()} for m, d in closed_rows.items()}, open(L.SCR + '/closed_rows.json', 'w'))
print(len(out), 'modules', sum(len(v['annotated']) for v in out.values()), 'annotated names')
PY
