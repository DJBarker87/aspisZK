#!/usr/bin/env python3
"""Unique unclassified sites (deduplicated over variants) with source lines.
usage: list_unclassified.py <analysis dir> [role]"""
import json, sys, re, collections
A = sys.argv[1]; only = sys.argv[2] if len(sys.argv) > 2 else None
u = json.load(open(f'{A}/residuals.json'))['unclassified']
g = collections.defaultdict(list)
for x in u:
    if only and x['role'] != only: continue
    g[(x['role'], x['addr'], x['why'])].append(x)
lines = {r: json.load(open(f'{A}/lines-{r}.json')) for r in ['stage1', 'stage2', 'pool']}
for (role, addr, why), xs in sorted(g.items(), key=lambda kv: (kv[0][0], kv[0][2], kv[1][0]['function'])):
    fr = (lines[role].get(addr) or {}).get('frames') or []
    ws = [f[1] for f in fr if 'rust/library' not in f[1] and '.cargo' not in f[1]][:2]
    inner = fr[0][1].split('/library/')[-1] if fr else 'unmapped'
    extra = xs[0].get('callees') or xs[0].get('counts') or xs[0].get('other') or ''
    print(role, addr, len(xs), why[:40], re.sub(r'17h[0-9a-f]{16}E', '', xs[0]['function'])[-55:], inner, ws, str(extra)[:150])
