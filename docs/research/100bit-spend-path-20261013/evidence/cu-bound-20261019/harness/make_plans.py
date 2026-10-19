#!/usr/bin/env python3
"""Emit the control, targeted and random sweep plans (deterministic from MASTER)."""
import json, random, sys
H = sys.argv[1]
MASTER = 0x20261019
A = f'{H}/artifacts'
base = dict(driver=f'{A}/pool_gate', pool=f'{A}/pool/aspis_pool.so',
            verifier=f'{A}/verifier/aspis_r1_cost_probe_program.so',
            registry='/home/dombarker/project-offloads/active-mask-basis-sbf-20261017/artifacts/aux-current/registry/aspis_registry.so')
FX = '/home/dombarker/project-offloads/aspis-r1-rollover-measurement-20261019/fixtures'
CAP = (1 << 20) - 1

control = dict(base, out=f'{H}/sweep/control', runs=[
    dict(label=f'control-{k}-{p}', kind=k,
         args=['--pairs', str(p), '--reuse', f'{FX}/{k}-{p}/r1-s2-proof.bin', f'{FX}/{k}-{p}/r1-s2-public-asf8.bin', '--tx-version', 'v1'])
    for k in ['transfer', 'withdrawal'] for p in [13, 255, 1023]])

def common(seed, pairs, split, extra=()):
    return ['--pairs', str(pairs), '--seed', str(seed), '--split', str(split), '--uniform-lane',
            '--mask-entropy', 'os', '--tx-version', 'v1', *extra]

targeted = []
for k in ['transfer', 'withdrawal']:
    for split in (10, 11):
        for name, pairs, extra in [('cap', CAP, ()), ('cap-1', CAP - 1, ()), ('genesis-zeroed', 0, ('--zeroed-genesis-page',)),
                                   ('zero-samepage', 0, ()), ('p1', 1, ()), ('p255', 255, ()), ('p256', 256, ()),
                                   ('p1023', 1023, ()), ('p511', 511, ()), ('p65535', 65535, ()), ('p524287', 524287, ())]:
            targeted.append(dict(label=f'target-{k}-s{split}-{name}', kind=k, args=common(1000 + len(targeted), pairs, split, extra)))
        for attempts in (12, 16):
            targeted.append(dict(label=f'target-{k}-s{split}-marker{attempts}', kind=k,
                                 args=common(5000 + len(targeted), 255, split, ('--min-marker-attempts', str(attempts)))))
targeted_plan = dict(base, out=f'{H}/sweep/targeted', runs=targeted)

rng = random.Random(MASTER)
runs = []
for k in ['transfer', 'withdrawal']:
    for i in range(300):
        u = rng.random()
        if u < 0.25: pairs = rng.randrange(0, CAP + 1)
        elif u < 0.50: pairs = 256 * rng.randrange(1, 4097) - 1
        elif u < 0.75: pairs = rng.randrange(0, 4096)
        elif u < 0.90: pairs = CAP - rng.randrange(0, 1024)
        else: pairs = rng.choice([0, 1, 255, 256, 1023, CAP])
        split = rng.choice([10, 11])
        runs.append(dict(label=f'rand-{k}-{i:03d}', kind=k, args=common(rng.getrandbits(63), pairs, split)))
rng.shuffle(runs)
random_plan = dict(base, out=f'{H}/sweep/random', runs=runs)
for name, plan in [('control', control), ('targeted', targeted_plan), ('random', random_plan)]:
    open(f'{H}/plan-{name}.json', 'w').write(json.dumps(plan, indent=1))
    print(name, len(plan['runs']))

# Traced runs (register-tracing driver; CU must equal the untraced driver on the same inputs).
trace_runs = [dict(label=f'trace-control-{k}-{p}', kind=k,
                   args=['--pairs', str(p), '--reuse', f'{FX}/{k}-{p}/r1-s2-proof.bin', f'{FX}/{k}-{p}/r1-s2-public-asf8.bin', '--tx-version', 'v1'])
              for k in ['transfer', 'withdrawal'] for p in [13, 255]]
for k in ['transfer', 'withdrawal']:
    for i, (pairs, split, extra) in enumerate([(CAP, 11, ()), (0, 10, ('--zeroed-genesis-page',)), (777, 11, ()), (300000, 10, ())]):
        trace_runs.append(dict(label=f'trace-seeded-{k}-{i}', kind=k, args=common(7000 + i, pairs, split, extra)))
trace_plan = dict(base, driver=f'{A}/pool_gate_trace', out=f'{H}/sweep/trace', trace_dir=f'{H}/traces', runs=trace_runs)
open(f'{H}/plan-trace.json', 'w').write(json.dumps(trace_plan, indent=1)); print('trace', len(trace_runs))

# Step-4 profiling runs (verifier built with cu-profiling; phase logs).
prof = [dict(label=f'prof-control-{k}-{p}', kind=k,
             args=['--pairs', str(p), '--reuse', f'{FX}/{k}-{p}/r1-s2-proof.bin', f'{FX}/{k}-{p}/r1-s2-public-asf8.bin', '--tx-version', 'v1'])
        for k in ['transfer', 'withdrawal'] for p in [13, 255, 1023]]
for k in ['transfer', 'withdrawal']:
    for i, (pairs, split, extra) in enumerate([(0, 10, ('--zeroed-genesis-page',)), (CAP, 10, ()), (255, 11, ()), (31337, 10, ()),
                                               (CAP, 11, ()), (4095, 10, ()), (256, 10, ()), (777777, 11, ())]):
        prof.append(dict(label=f'prof-seeded-{k}-{i}', kind=k, args=common(9000 + i, pairs, split, extra)))
prof_plan = dict(base, verifier=f'{A}/verifier-profiling/aspis_r1_cost_probe_program.so', out=f'{H}/sweep/profile', runs=prof)
open(f'{H}/plan-profile.json', 'w').write(json.dumps(prof_plan, indent=1)); print('profile', len(prof))
