# Final Pool for the freeze: deployed Pool (old-*.json) against the head's Pool (new-*.json), both with
# the head's verifier ELF (BASE2). Same proof, same error, same post-state hash for every run; positive
# runs settle as expected; under-limit runs fail unchanged; page-negative and account-negative runs are
# rejected unchanged; account-negative runs must agree (rejection is reported, not required). Prints CU per run. Usage: python3 -I compare_final.py (in this directory).
import json
ok_all = True
for kind in ['pos', 'neg', 'acc']:
    o = json.load(open(f'old-{kind}.json')); n = json.load(open(f'new-{kind}.json'))
    print('==', kind, 'old', o['pool_elf_sha256'], 'new', n['pool_elf_sha256'])
    for ro, rn in zip(o['results'], n['results']):
        assert ro['scenario'] == rn['scenario']
        for xo, xn in zip(ro['elfs'][0]['runs'], rn['elfs'][0]['runs']):
            same = ro['summed_proof_sha256'] == rn['summed_proof_sha256'] and xo['error'] == xn['error'] and xo['post_state_sha256'] == xn['post_state_sha256']
            if 'state' in xn:
                good = xo['state']['all'] and xn['state']['all'] and xn['error'] is None
            elif kind == 'pos':
                good = xn['error'] is not None and xo['unchanged_except_payer_fee'] and xn['unchanged_except_payer_fee']
            elif kind == 'neg':
                good = xo['rejected'] and xn['rejected'] and xo['unchanged_except_payer_fee'] and xn['unchanged_except_payer_fee']
            else:
                # Account corruptions: the pass condition is agreement (same outcome and post-state);
                # whether the corruption is rejected is reported, not required.
                good = xo['rejected'] == xn['rejected'] and (not xn['rejected'] or (xo['unchanged_except_payer_fee'] and xn['unchanged_except_payer_fee']))
                if not xn['rejected']:
                    print('   NOT REJECTED by either Pool:', rn['scenario'])
            own = lambda x: x['pool_cu'] - x['verifier_cu'] if x.get('pool_cu') and x.get('verifier_cu') else x.get('pool_cu')
            ok_all &= same and good
            print(f"{ro['scenario']:38s} {xo['variant']:30s} tx {xo['transaction_cu']:>9} -> {xn['transaction_cu']:>9} pool_own {own(xo)} -> {own(xn)} verifier {xo.get('verifier_cu')} error {xn['error']} same {same} expected {good}")
print('ALL_RUNS_AGREE_AND_AS_EXPECTED', ok_all)
