#!/usr/bin/env python3
"""PCO_shadow.py: find 'shadow candidates' of the emitted gate modules.
PRV chose a module's compiled source among committed files whose PATH names the module and whose imports equal the olean's.
The pilot found a counter-example (AspisR1WideToBytesSource.Funs: the compiled file is generated-adapted/Funs.lean, a path that
does not name the module). A shadow candidate is an emitted blob with the module's exact import set and the module's namespace, a
different sha256 from every path-named candidate, and declaring at least half of the module's strong names.
Usage: PCO_shadow.py SCRATCH OUT.json LOADED_scan.jsonl   (SCRATCH from PCO_partition.py; run from evidence/)"""
import json, re, sys, collections
sys.path.insert(0, 'prov-p0-20261109')
from PCO_partition import decls, batch_cat
S, OUT, SCAN = sys.argv[1:4]
idx = json.load(open(f'{S}/lean_index.json')); em = json.load(open(f'{S}/emods_decl.json')); cl = json.load(open(f'{S}/classified.json'))
scan = {}
for l in open(SCAN):
    r = json.loads(l); scan[r['module']] = r
em_blobs = {g: v for g, v in idx.items() if v['aeneas_header'] or v['rust_annotations']}
info = {}
for g, data in batch_cat(list(em_blobs)):
    t = data.decode('utf-8', 'replace'); m = re.search(r'(?m)^namespace (\S+)\s*$', t)
    try: names = {n for n, k in decls(t)}
    except AssertionError: names = set()
    info[g] = dict(ns=m.group(1) if m else None, names=names)
byimp = collections.defaultdict(list)
for g, v in em_blobs.items(): byimp[tuple(v['imports'])].append(g)
sha2gid = {}
for g, v in idx.items(): sha2gid.setdefault(v['sha256'], g)
res = {}
for m, v in em.items():
    if not cl[m]['relied']: continue
    cands = set(v['candidates']); oi = tuple(sorted(set(scan[m]['imports'])))
    ns = next((info[sha2gid[s]]['ns'] for s in cands if sha2gid[s] in info and info[sha2gid[s]]['ns']), None)
    if not ns: continue
    strong = set(v['strong_names']); sh = []
    for g in byimp.get(oi, []):
        s = idx[g]['sha256']
        if s in cands or info[g]['ns'] != ns: continue
        if strong and len(info[g]['names'] & strong) >= max(1, len(strong) // 2): sh.append(dict(sha256=s, path=idx[g]['paths'][0]))
    seen = {}
    for x in sh: seen.setdefault(x['sha256'], x)
    if seen: res[m] = dict(group=cl[m].get('kind'), shadows=list(seen.values()))
json.dump(res, open(OUT, 'w'), indent=1); print(len(res), 'modules with shadow candidates of', sum(1 for m in cl if cl[m]['relied']))
