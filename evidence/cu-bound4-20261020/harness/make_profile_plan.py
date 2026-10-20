#!/usr/bin/env python3
"""Step 6: replay measured variant runs (own proofs, --reuse) with the cu-profiling
verifier; phase logs give per-phase CU. usage: make_profile_plan.py <host dir>"""
import json, sys, collections
H = sys.argv[1]
plan = json.load(open(f'{H}/plan-variants.json'))
rows = [json.loads(l) for l in open(f'{H}/sweep/variants/sweep.jsonl')]
by = collections.defaultdict(list)
for r in rows: by[(r['kind'], r['inputs']['split'])].append(r)
picks = []
for k, rs in sorted(by.items()):
    rs = sorted(rs, key=lambda r: r['pairs'])
    for r in [rs[0], rs[len(rs) // 3], rs[2 * len(rs) // 3], rs[-1], max(rs, key=lambda r: r['stage1_cu']), max(rs, key=lambda r: r['settlement_cu'])]:
        if r['label'] not in [p['label'] for p in picks]: picks.append(r)
runs = []
for r in picks:
    run = next(x for x in plan['runs'] if x['label'] == r['label'])
    args = list(run['args'])
    if '--mask-entropy' in args:
        i = args.index('--mask-entropy'); del args[i:i + 2]
    task = f"{plan['out']}/runs/{r['label']}/task"
    if '--reuse' not in args:
        args += ['--reuse', f'{task}/r1-s2-proof.bin', f'{task}/r1-s2-public-asf8.bin']
    runs.append(dict(label=f'prof-{r["label"]}', kind=r['kind'], args=args))
out = dict(plan, verifier=f'{H}/artifacts/verifier-profiling/aspis_r1_cost_probe_program.so', out=f'{H}/sweep/profile', runs=runs)
out.pop('trace_dir', None)
open(f'{H}/plan-profile.json', 'w').write(json.dumps(out, indent=1)); print('profile', len(runs))
