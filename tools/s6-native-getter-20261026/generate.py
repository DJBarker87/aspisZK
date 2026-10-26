#!/usr/bin/env python3
"""Emit loop-free safe constructors for every native statement data field."""
from pathlib import Path
import re
import subprocess

R = Path(__file__).resolve().parents[2]
REV = '4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
classes = {
 'pair_forest_terminal': ['PoolV1PairForestTerminalCommonV1'],
 'payment_relation': ['PoolV1PrivateTransferPublicV1', 'PoolV1WithdrawalPublicV1'],
 'pair_tree_profile': ['PoolV1PairLatePublicStatementV1', 'PoolV1PairLiveSnapshotV1'],
 'pair_terminal': ['PoolV1PairVerifiedAfterstateV1'],
}
constructors = []

def expression(t):
    t = t.strip()
    if t in ['u8', 'u32', 'u64']:
        return 'kani::any::<' + t + '>()'
    if t == 'M31':
        return 'aspis_core::field::M31(kani::any::<u32>())'
    if t == 'Digest':
        return '[' + ','.join(expression('M31') for _ in range(8)) + ']'
    if t.startswith('['):
        m = re.fullmatch(r'\[(.+);\s*(.+)\]', t)
        assert m
        count = {'32': 32, 'POOL_V1_PAIR_TREE_DEPTH': 20, 'super::POOL_V1_PAIR_TREE_DEPTH': 20}[m[2].strip()]
        return '[' + ','.join(expression(m[1]) for _ in range(count)) + ']'
    assert any(t in ns for ns in classes.values()), t
    return 'make_' + t + '()'

for module, names in classes.items():
    source = subprocess.check_output(['git', 'show', REV + ':crates/aspis-statement/src/pool_v1/' + module + '.rs'],cwd=R,text=True)
    for name in names:
        match = re.search(r'pub struct ' + name + r'\s*\{([^}]+)\}', source, re.S)
        assert match, name
        body = '\n'.join(line for line in match[1].splitlines() if not line.strip().startswith('//'))
        fields = re.findall(r'pub\s+(\w+):\s*([^\n]+?),\s*(?:\n|$)', body)
        assert fields and body.count('pub ') == len(fields), (name, body)
        full = 'aspis_statement::pool_v1::' + module + '::' + name
        constructors.append('    fn make_' + name + '()->' + full + ' {\n        ' + full + ' {\n' +
            '\n'.join('            ' + key + ': ' + expression(t) + ',' for key,t in fields) + '\n        }\n    }\n')
text = '''    // Every scalar is independent. Literal arrays cover all native array
    // coordinates; no canonicality or successful decoder premise is imposed.
'''+''.join(constructors)+'''
    fn arbitrary_statement()->Statement {
        if kani::any::<bool>() {
            Statement::PrivateTransfer { common: make_PoolV1PairForestTerminalCommonV1(), public: make_PoolV1PrivateTransferPublicV1() }
        } else {
            Statement::Withdrawal { common: make_PoolV1PairForestTerminalCommonV1(), public: make_PoolV1WithdrawalPublicV1() }
        }
    }
'''
p = Path(__file__).parent/'proofs.rs'
s = p.read_text()
start = s.index('    // BEGIN GENERATED CONSTRUCTORS')
end = s.index('    // END GENERATED CONSTRUCTORS', start)
s = s[:start]+'    // BEGIN GENERATED CONSTRUCTORS\n'+text+s[end:]
if '--check' in __import__('sys').argv:
    assert s == p.read_text()
else:
    p.write_text(s)
print('native constructor generation: PASS')
