#!/usr/bin/env python3
"""Choose the traced runs from the measured variants: per settlement variant
(kind, split, mode, prefund) the run with the largest settlement CU (its w) plus
runs at other positions (lowest and highest pairs, and the largest stage-1), so
that every group has >= 4 traced runs; per stage-1 variant (kind, split) the run
with the largest stage-1 CU. Prints set:label picks for make_trace_plan.py."""
import json, sys, collections
rows = []
for f in sys.argv[1:]:
    sset = f.split('/')[-2]
    rows += [dict(json.loads(l), set=sset) for l in open(f) if json.loads(l).get('exit_status') == 0]
def grp(r):
    i = r['inputs']; mode = 'genesis' if i['zeroed_genesis_page'] else r['history_mode']
    return (r['kind'], i['split'], mode, bool(i['prefund_marker_lamports']))
g = collections.defaultdict(list)
for r in rows: g[grp(r)].append(r)
picks = []
for V, rs in sorted(g.items()):
    chosen = [max(rs, key=lambda r: r['settlement_cu'])]
    for cand in [max(rs, key=lambda r: r['stage1_cu']), min(rs, key=lambda r: r['pairs']), max(rs, key=lambda r: r['pairs']),
                 min(rs, key=lambda r: r['settlement_cu'])] + sorted(rs, key=lambda r: r['label']):
        if len(chosen) >= 4: break
        if cand['label'] not in {c['label'] for c in chosen}: chosen.append(cand)
    picks += chosen
s1 = collections.defaultdict(list)
for r in rows: s1[(r['kind'], r['inputs']['split'])].append(r)
for V, rs in s1.items():
    w = max(rs, key=lambda r: r['stage1_cu'])
    if w['label'] not in {p['label'] for p in picks}: picks.append(w)
print(' '.join(f"{p['set']}:{p['label']}" for p in picks))
print(len(picks), file=sys.stderr)
