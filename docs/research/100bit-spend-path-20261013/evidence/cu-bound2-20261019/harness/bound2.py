#!/usr/bin/env python3
"""Compose B per variant (PREREG-CU-UPPER-BOUND-2) and write the deliverables.
usage: bound2.py <analysis dir> <rules.json> <out dir> <variant sweep.jsonl>... -- <sweep.jsonl>...
B_stage1(kind, split)                 = CU_stage1(w) + residuals(stage1 role) + S-QSCAN-EXTRA
B_settlement(kind, split, mode, pre)  = CU_settlement(w) + residuals(stage2 role) + residuals(Pool role)
w = the measured worst run of the variant (it is traced; its CU is the measured CU)."""
import json, sys, re, collections
A, RULES, OUT = sys.argv[1:4]
rest = sys.argv[4:]; k = rest.index('--'); VAR, SWEEP = rest[:k], rest[k + 1:]
res = json.load(open(f'{A}/residuals.json')); spv = json.load(open(f'{A}/sites-per-variant.json')); rules = json.load(open(RULES))
assert not res['unclassified'], 'unclassified sites present'
s1 = json.load(open(f'{A}/stage1.json'))
fnames = s1['functions']
scan_f = [i for i, n in enumerate(fnames) if 'QueryScan4scan' in n]
scan_max = max(s1['inclusive_call_costs'][str(i)][1] for i in scan_f if str(i) in s1['inclusive_call_costs'])
inner = [l for l in s1['loops'] if 'QueryScan4scan' in l['function'] and l['header'] != '0x140820']
inner_extra = sum((max(l['max_trip_per_entry']) - 1) * l['W_iter'] for l in inner)
worst_block = scan_max + 8 * inner_extra
qscan_extra = 5 * max(0, worst_block - scan_max)
QSCAN = dict(id='S-QSCAN-EXTRA', tx='stage1', residual=qscan_extra,
             derivation=f'queries_from_pairs scans at most 8 blocks of 8 words (r0_transcript.rs:309-318, QUERY_MAX_DRAWS = 64 at :48); every run scans 3; '
                        f'the 5 further scan() calls are counted by the ELF site at the observed maximum inclusive scan cost {scan_max}; '
                        f'a scan call costs at most {scan_max} + 8 words x (contains loops at their caps: {inner_extra}) = {worst_block}; '
                        f'extra 5 x ({worst_block} - {scan_max}) = {qscan_extra}')
B = dict(stage1={}, settlement={})
for V, r in res['result']['stage1'].items():
    B['stage1'][V] = dict(worst=r['worst'], worst_cu=r['worst_cu'], residual_elf=r['residual_sum'], residual_qscan=qscan_extra,
                          B=r['worst_cu'] + r['residual_sum'] + qscan_extra, totals=r['totals'])
for V, r2 in res['result']['stage2'].items():
    rp = res['result']['pool'][V]
    assert r2['worst'] == rp['worst']
    B['settlement'][V] = dict(worst=r2['worst'], worst_cu=r2['worst_cu'], residual_stage2=r2['residual_sum'], residual_pool=rp['residual_sum'],
                              B=r2['worst_cu'] + r2['residual_sum'] + rp['residual_sum'], totals_stage2=r2['totals'], totals_pool=rp['totals'])
per_kind = {}
for kind in ['transfer', 'withdrawal']:
    b1 = max(v['B'] for V, v in B['stage1'].items() if json.loads(V)[0] == kind)
    b2 = max(v['B'] for V, v in B['settlement'].items() if json.loads(V)[0] == kind)
    per_kind[kind] = dict(B_stage1=b1, B_settlement=b2)
# sweep check: every swept value <= its variant's B
sweep = [json.loads(l) for f in SWEEP for l in open(f)]
viol = []; mx = collections.defaultdict(int); n = collections.Counter()
for r in sweep:
    if r.get('exit_status') != 0 or r.get('outcome') != 'accepted': continue
    i = r['inputs']; mode = 'genesis' if i['zeroed_genesis_page'] else r['history_mode']; pre = bool(i.get('prefund_marker_lamports'))
    v1 = json.dumps([r['kind'], i['split']]); v2 = json.dumps([r['kind'], i['split'], mode, pre])
    n[r['kind']] += 1
    for tx, V, cu in [('stage1', v1, r['stage1_cu']), ('settlement', v2, r['settlement_cu'])]:
        mx[(r['kind'], tx)] = max(mx[(r['kind'], tx)], cu)
        if cu > B[tx][V]['B']: viol.append(dict(label=r['label'], tx=tx, V=V, cu=cu, B=B[tx][V]['B']))
out = dict(method='PREREG-CU-UPPER-BOUND-2-20261019', B=B, source_sites=[QSCAN], per_kind=per_kind,
           sweep=dict(accepted_runs_per_kind=dict(n), max={f'{k}/{t}': v for (k, t), v in mx.items()}, violations=viol),
           verdict=('PASS' if all(v['B_stage1'] <= 1_300_000 and v['B_settlement'] <= 1_300_000 for v in per_kind.values()) and not viol else 'FAIL'))
json.dump(out, open(f'{OUT}/bound.json', 'w'), indent=1)
print(json.dumps(per_kind, indent=1)); print('sweep', dict(n), {f'{k}/{t}': v for (k, t), v in mx.items()}, 'violations', len(viol)); print('verdict', out['verdict'])
