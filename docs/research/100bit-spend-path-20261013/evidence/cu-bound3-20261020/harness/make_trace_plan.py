#!/usr/bin/env python3
"""Replay chosen accepted runs under the register-tracing driver with their own
proof (--reuse of the run's task sidecars), so the traced input is the measured
input exactly (traced CU must equal the measured CU; checked by check_trace_cu).
usage: make_trace_plan.py <host dir> <plan name> <sweep set>:<label> ..."""
import json, sys
H, name, picks = sys.argv[1], sys.argv[2], sys.argv[3:]
base = json.load(open(f'{H}/plan-control.json')); base.pop('runs'); base.pop('out')
runs = []
for pick in picks:
    sset, label = pick.split(':', 1)
    plan = json.load(open(f'{H}/plan-{sset}.json'))
    run = next(r for r in plan['runs'] if r['label'] == label)
    args = list(run['args']); i = args.index('--mask-entropy'); del args[i:i + 2]
    task = f"{plan['out']}/runs/{label}/task"
    args += ['--reuse', f'{task}/r1-s2-proof.bin', f'{task}/r1-s2-public-asf8.bin']
    runs.append(dict(label=f'trace-{label}', kind=run['kind'], args=args, source=f'{sset}:{label}'))
runs = list({r['label']: r for r in runs}.values())
plan = dict(base, driver=f'{H}/artifacts/pool_gate_trace', out=f'{H}/sweep/{name}', trace_dir=f'{H}/traces/{name}', runs=runs)
open(f'{H}/plan-{name}.json', 'w').write(json.dumps(plan, indent=1)); print(name, len(runs))
