#!/usr/bin/env python3
"""Plans for the second CU-bound method (PREREG-CU-UPPER-BOUND-2): controls,
step-1 variants, step-7 random sweep and targeted inputs. Deterministic from MASTER.
usage: make_plans2.py <host work dir>"""
import json, random, sys
H = sys.argv[1]
MASTER = 0x20261019_2
A = f'{H}/artifacts'
base = dict(driver=f'{A}/pool_gate', pool=f'{A}/pool/aspis_pool.so',
            verifier=f'{A}/verifier/aspis_r1_cost_probe_program.so',
            registry='/home/dombarker/project-offloads/active-mask-basis-sbf-20261017/artifacts/aux-current/registry/aspis_registry.so')
FX = '/home/dombarker/project-offloads/aspis-r1-rollover-measurement-20261019/fixtures'
CAP = (1 << 20) - 1
KINDS = ['transfer', 'withdrawal']
# Rent-exempt minimum is irrelevant here: any positive prefund selects the
# transfer+allocate+assign marker path; 1 lamport is the B1 mutation value.
PREFUND = '1'

def common(seed, pairs, split, extra=()):
    return ['--pairs', str(pairs), '--seed', str(seed), '--split', str(split), '--uniform-lane',
            '--mask-entropy', 'os', '--tx-version', 'v1', *extra]

plans = {}
plans['control'] = dict(base, out=f'{H}/sweep/control', runs=[
    dict(label=f'control-{k}-{p}', kind=k,
         args=['--pairs', str(p), '--reuse', f'{FX}/{k}-{p}/r1-s2-proof.bin', f'{FX}/{k}-{p}/r1-s2-public-asf8.bin', '--tx-version', 'v1'])
    for k in KINDS for p in [13, 255, 1023]])

# Step 1: discrete variants. Positions: 0 and 2^20-1 (prereg), the first method's most
# expensive traced positions (stage 1: 256, 0, 4095, 1023, 255, 777777, 2^20-1; nested
# stage 2: 0, 256, 31337, 13, 255), and bit-pattern extremes for the lane-position loops.
SAME = [0, 1, 13, 256, 1023 - 1, 4095 - 1, 31337, 65534, 1 << 19, 0x55555, 0xAAAAA, 777777, CAP - 1]
ROLL = [255, 511, 1023, 4095, 65535, 0x555FF, 0xAAAFF, 524287, CAP]
var = []; seed = 20000
for k in KINDS:
    for split in (10, 11):
        for mode, positions in [('genesis', [0]), ('same-page', SAME), ('rollover', ROLL)]:
            for pairs in positions:
                for pre in (False, True):
                    if pre and pairs not in (0, 1 << 19, 0xAAAAA, CAP - 1, 255, 0xAAAFF, CAP):
                        continue
                    extra = (('--zeroed-genesis-page',) if mode == 'genesis' else ()) + (('--prefund-marker', PREFUND) if pre else ())
                    for rep in range(2):
                        seed += 1
                        var.append(dict(label=f'var-{k}-s{split}-{mode}-p{pairs}-{"pre" if pre else "fresh"}-{rep}',
                                        kind=k, args=common(seed, pairs, split, extra)))
plans['variants'] = dict(base, out=f'{H}/sweep/variants', runs=var)
# Genesis has one position (0); two more witnesses per genesis group so every
# settlement group has >= 4 runs (R0 needs >= 3 traced runs per group).
extra = []; seed = 29000
for k in KINDS:
    for split in (10, 11):
        for pre in (False, True):
            for rep in (2, 3):
                seed += 1
                extra.append(dict(label=f'var-{k}-s{split}-genesis-p0-{"pre" if pre else "fresh"}-{rep}', kind=k,
                                  args=common(seed, 0, split, ('--zeroed-genesis-page',) + (('--prefund-marker', PREFUND) if pre else ()))))
plans['variants-extra'] = dict(base, out=f'{H}/sweep/variants-extra', runs=extra)

# Step 7 targeted inputs (in addition to the step-1 variant grid): the largest same-page
# trailing-ones positions (127 and 2^20-129 have 7 trailing ones, the most a same-page
# position can have) and prefunded markers at and above the rent-exempt minimum.
tg = []; seed = 31000
for k in KINDS:
    for split in (10, 11):
        for name, pairs, extra in [('p127', 127, ()), ('p1048447', (1 << 20) - 129, ()),
                                   ('rollover-prefund-rent', 255, ('--prefund-marker', '890880')),
                                   ('rollover-prefund-1e9', 255, ('--prefund-marker', '1000000000'))]:
            seed += 1
            tg.append(dict(label=f'target-{k}-s{split}-{name}', kind=k, args=common(seed, pairs, split, extra)))
plans['targeted'] = dict(base, out=f'{H}/sweep/targeted', runs=tg)

# Step 7: random sweep, >= 256 accepted per kind (300 planned per kind).
rng = random.Random(MASTER); runs = []
for k in KINDS:
    for i in range(300):
        u = rng.random()
        if u < 0.25: pairs = rng.randrange(0, CAP + 1)
        elif u < 0.50: pairs = 256 * rng.randrange(1, 4097) - 1          # rollover positions
        elif u < 0.70: pairs = rng.randrange(0, 4096)
        elif u < 0.85: pairs = CAP - rng.randrange(0, 1024)
        else: pairs = rng.choice([0, 1, 255, 256, 1023, 1 << 19, CAP])
        split = rng.choice([10, 11])
        extra = []
        if pairs == 0 and rng.random() < 0.5: extra.append('--zeroed-genesis-page')
        if rng.random() < 0.15: extra += ['--prefund-marker', str(rng.choice([1, 890880, 10**9]))]
        runs.append(dict(label=f'rand-{k}-{i:03d}', kind=k, args=common(rng.getrandbits(63), pairs, split, extra)))
rng.shuffle(runs)
plans['random'] = dict(base, out=f'{H}/sweep/random', runs=runs)

for name, plan in plans.items():
    open(f'{H}/plan-{name}.json', 'w').write(json.dumps(plan, indent=1))
    print(name, len(plan['runs']))
