#!/usr/bin/env python3
"""Group one variant's residual sites by (function, innermost workspace source line).
usage: group_sites.py <analysis dir> <role> <variant json> [rule]"""
import json, sys, re, collections
A, role, V = sys.argv[1:4]; rule = sys.argv[4] if len(sys.argv) > 4 else None
lines = json.load(open(f'{A}/lines-{role}.json'))
def src(addr, ws_only=False):
    fr = (lines.get(addr) or {}).get('frames') or []
    inner = fr[0][1] if fr else 'unmapped'
    ws = next((f[1] for f in fr if 'rust/library' not in f[1] and '.cargo' not in f[1]), 'unmapped')
    return inner.split('/library/')[-1], ws
for e in json.load(open(f'{A}/sites-per-variant.json')):
    if e['role'] != role or json.dumps(e['variant']) != V: continue
    g = collections.defaultdict(lambda: [0, 0, set()])
    for s in e['sites']:
        if not s['residual'] or (rule and s['rule'] != rule): continue
        inner, ws = src(s['addr'])
        k = (re.sub(r'17h[0-9a-f]{16}E', '', s['function'])[-70:], inner, ws)
        g[k][0] += s['residual']; g[k][1] += 1; g[k][2].add(s['rule'])
    tot = sum(v[0] for v in g.values()); print('total', tot)
    for k, v in sorted(g.items(), key=lambda kv: -kv[1][0])[:70]:
        print(v[0], v[1], sorted(v[2]), k)
