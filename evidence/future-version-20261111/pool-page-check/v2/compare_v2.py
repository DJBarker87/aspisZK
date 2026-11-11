# v2 (slice equality) against the deployed Pool (old-*.json) and against form A as committed (new-*.json):
# same proof, same error, same post-state hash; positive runs settle as expected, under-limit runs fail
# unchanged, negative runs are rejected unchanged. Prints CU old / A / v2 and v2 - A per run.
# Usage: python3 -I compare_v2.py (in this directory; the v1 results are in the parent directory).
import json
ok_all = True; worst_delta = 0
for kind in ['pos', 'neg']:
    o = json.load(open(f'../old-{kind}.json')); a = json.load(open(f'../new-{kind}.json')); n = json.load(open(f'new2-{kind}.json'))
    print('==', kind, 'old', o['pool_elf_sha256'], 'A', a['pool_elf_sha256'], 'v2', n['pool_elf_sha256'])
    for ro, ra, rn in zip(o['results'], a['results'], n['results']):
        assert ro['scenario'] == ra['scenario'] == rn['scenario']
        for xo, xa, xn in zip(ro['elfs'][0]['runs'], ra['elfs'][0]['runs'], rn['elfs'][0]['runs']):
            same = all(r['summed_proof_sha256'] == rn['summed_proof_sha256'] for r in (ro, ra)) and xo['error'] == xa['error'] == xn['error'] and xo['post_state_sha256'] == xa['post_state_sha256'] == xn['post_state_sha256']
            if 'state' in xn:
                good = xo['state']['all'] and xn['state']['all'] and xn['error'] is None
            elif kind == 'pos':
                good = xn['error'] is not None and xo['unchanged_except_payer_fee'] and xn['unchanged_except_payer_fee']
            else:
                good = xo['rejected'] and xn['rejected'] and xo['unchanged_except_payer_fee'] and xn['unchanged_except_payer_fee']
            own = lambda x: x['pool_cu'] - x['verifier_cu'] if x.get('pool_cu') and x.get('verifier_cu') else x.get('pool_cu')
            delta = xn['transaction_cu'] - xa['transaction_cu']
            if 'state' in xn: worst_delta = max(worst_delta, delta)
            ok_all &= same and good
            print(f"{ro['scenario']:38s} {xo['variant']:30s} tx {xo['transaction_cu']:>9} / {xa['transaction_cu']:>9} / {xn['transaction_cu']:>9} (v2-A {delta:+d}) pool_own {own(xo)} / {own(xa)} / {own(xn)} error {xn['error']} same {same} expected {good}")
print('MAX_V2_MINUS_A_ON_SETTLING_RUNS', worst_delta)
print('ALL_RUNS_AGREE_AND_AS_EXPECTED', ok_all)
