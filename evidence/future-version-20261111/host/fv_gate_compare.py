#!/usr/bin/env python3
"""Read the result of fv_sampler_gate.sh <name> … and print one verdict per gate.

usage (on the host, in the workspace): python3 fv_gate_compare.py <name> [<head-label>]

Prints: the gate's done-file status; whether the two mutation verdict files are identical; the
replay compute of the changed build beside the head's (replays-v5/<head-label>-*.json if present);
for every worst-case scenario the compute of the head ELF and of the changed ELF, and whether the
fixture proof made by the tool BUILT IN THE CHANGED TREE has the same pinned and re-packed hashes
as the proof made by the tool built in the unchanged tree (worst/w1.json, w2.json, w3.json), which
is the prover byte-identity check. Exit status 1 if anything is not as required.
"""
import json, os, sys
W = os.path.expanduser('~/project-offloads/future-version-20261111')
name = sys.argv[1]
head = sys.argv[2] if len(sys.argv) > 2 else 'X1-rewrites'
bad = False
done = os.path.join(W, f'GATE_{name}.done')
status = open(done).read().split('\n')[0] if os.path.exists(done) else 'NOT FINISHED'
print('gate status:', status)
bad |= status != 'OK'
mut = os.path.join(W, f'MUTANTS_g-{name}.done')
if os.path.exists(mut):
    txt = open(mut).read()
    ident = 'IDENTICAL' in txt and 'DIFFERENT' not in txt
    print('mutation verdict files identical:', ident)
    bad |= not ident
else:
    print('mutation campaign: no result'); bad = True
for op in ('transfer', 'withdrawal'):
    p = os.path.join(W, 'replays-v5', f'{name}-{op}.json')
    if not os.path.exists(p):
        print('replay', op, 'missing'); bad = True; continue
    s = json.load(open(p))['summary']
    hp = os.path.join(W, 'replays-v5', f'{head}-{op}.json')
    hcu = json.load(open(hp))['summary']['one_tx_transaction_cu'] if os.path.exists(hp) else None
    ok = s['one_tx_final_state_equals_control'] and s['changed_certificate_rejected'] and s['pinned_format_buffer_rejected'] and s['rejected_runs_leave_state_unchanged_except_payer_fee'] and s['one_tx_error'] is None
    print(f'replay {op}: {s["one_tx_transaction_cu"]} (head {hcu}, difference {s["one_tx_transaction_cu"] - hcu if hcu else "?"}); all replay conditions hold: {ok}')
    bad |= not ok
base = {}
for w in ('w1', 'w2', 'w3'):
    p = os.path.join(W, 'worst', f'{w}.json')
    if os.path.exists(p):
        for r in json.load(open(p))['results']:
            base[r['scenario']] = (r['pinned_proof_sha256'], r['summed_proof_sha256'])
p = os.path.join(W, 'worst', f'gate-{name}.json')
if not os.path.exists(p):
    print('worst-case run: no result'); bad = True
else:
    for r in json.load(open(p))['results']:
        b = base.get(r['scenario'])
        same = (b == (r['pinned_proof_sha256'], r['summed_proof_sha256'])) if b else None
        cu = {e['elf']: {x['variant']: x['transaction_cu'] for x in e['runs'] if 'limit' not in x['variant']} for e in r['elfs']}
        errs = [x['error'] for e in r['elfs'] for x in e['runs'] if 'limit' not in x['variant'] and x['error']]
        labels = list(cu)
        diff = {v: cu[labels[-1]][v] - cu[labels[0]][v] for v in cu[labels[0]]} if len(labels) > 1 else {}
        print(f'{r["scenario"]}: prover output identical to the unchanged tree: {same}; {labels[-1]} minus {labels[0]}: {diff}; errors: {errs}')
        bad |= (same is not True) or bool(errs)
sys.exit(1 if bad else 0)
