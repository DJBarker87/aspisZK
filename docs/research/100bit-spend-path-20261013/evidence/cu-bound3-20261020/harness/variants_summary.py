#!/usr/bin/env python3
"""Step 1 summary: every discrete variant measured at its worst point.
usage: variants_summary.py out.json sweep.jsonl..."""
import json, sys, collections
rows = [json.loads(l) for f in sys.argv[2:] for l in open(f)]
rows = [r for r in rows if r['exit_status'] == 0 and r['outcome'] == 'accepted']
def mode(r): return 'genesis' if r['inputs']['zeroed_genesis_page'] else r['history_mode']
st = collections.defaultdict(list); se = collections.defaultdict(list)
for r in rows:
    st[(r['kind'], r['inputs']['split'])].append(r)
    se[(r['kind'], r['inputs']['split'], mode(r), bool(r['inputs']['prefund_marker_lamports']))].append(r)
def pos_table(rs, key):
    t = collections.defaultdict(list)
    for r in rs: t[r['pairs']].append(r[key])
    return {str(p): dict(n=len(v), max=max(v), min=min(v)) for p, v in sorted(t.items())}
out = dict(stage1=[], settlement=[])
for (k, s), rs in sorted(st.items()):
    w = max(rs, key=lambda r: r['stage1_cu'])
    out['stage1'].append(dict(kind=k, split=s, runs=len(rs), worst_label=w['label'], worst_pairs=w['pairs'], worst_stage1_cu=w['stage1_cu'],
                              min_stage1_cu=min(r['stage1_cu'] for r in rs), by_position=pos_table(rs, 'stage1_cu')))
for (k, s, m, p), rs in sorted(se.items()):
    w = max(rs, key=lambda r: r['settlement_cu'])
    po = sorted({r['settlement_cu'] - r['nested_stage2_cu'] for r in rs})
    out['settlement'].append(dict(kind=k, split=s, mode=m, prefund=p, runs=len(rs), worst_label=w['label'], worst_pairs=w['pairs'],
                                  worst_settlement_cu=w['settlement_cu'], worst_nested_stage2_cu=w['nested_stage2_cu'],
                                  min_settlement_cu=min(r['settlement_cu'] for r in rs), pool_only_values=po,
                                  by_position=pos_table(rs, 'settlement_cu')))
json.dump(out, open(sys.argv[1], 'w'), indent=1)
for x in out['stage1']: print('S1', x['kind'], x['split'], x['runs'], x['worst_stage1_cu'], x['worst_pairs'])
for x in out['settlement']: print('ST', x['kind'], x['split'], x['mode'], x['prefund'], x['runs'], x['worst_settlement_cu'], x['worst_pairs'], x['pool_only_values'][0], x['pool_only_values'][-1])
