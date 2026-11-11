# Old (deployed) Pool against the changed Pool in one_tx_worst runs: same proof, same error, same
# post-state hash for every run; positive runs settle as expected; negative runs are rejected and
# change nothing but the payer's fee. Usage: python3 -I compare.py (in this directory).
import json
ok_all = True
for kind in ['pos', 'neg']:
    o = json.load(open(f'old-{kind}.json')); n = json.load(open(f'new-{kind}.json'))
    print('==', kind, 'old pool', o['pool_elf_sha256'], 'new pool', n['pool_elf_sha256'])
    for ro, rn in zip(o['results'], n['results']):
        assert ro['scenario'] == rn['scenario']
        for xo, xn in zip(ro['elfs'][0]['runs'], rn['elfs'][0]['runs']):
            assert xo['variant'] == xn['variant']
            same = ro['summed_proof_sha256'] == rn['summed_proof_sha256'] and xo['error'] == xn['error'] and xo['post_state_sha256'] == xn['post_state_sha256']
            if 'state' in xo:
                good = xo['state']['all'] and xn['state']['all'] and xo['error'] is None
            elif kind == 'pos':
                good = xo['error'] is not None and xo['unchanged_except_payer_fee'] and xn['unchanged_except_payer_fee']
            else:
                good = xo['rejected'] and xn['rejected'] and xo['unchanged_except_payer_fee'] and xn['unchanged_except_payer_fee']
            own = lambda x: x['pool_cu'] - x['verifier_cu'] if x.get('pool_cu') and x.get('verifier_cu') else x.get('pool_cu')
            ok_all &= same and good
            print(f"{ro['scenario']:38s} {xo['variant']:30s} tx {xo['transaction_cu']:>9} -> {xn['transaction_cu']:>9} pool_own {own(xo)} -> {own(xn)} error {xn['error']} same {same} expected {good}")
print('ALL_RUNS_AGREE_AND_AS_EXPECTED', ok_all)
