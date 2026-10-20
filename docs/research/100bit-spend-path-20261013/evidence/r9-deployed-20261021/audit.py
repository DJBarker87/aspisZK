#!/usr/bin/env python3
"""Read-only packet audit; never compiles Lean or changes shared objects."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

here = Path(__file__).resolve().parent
packet = here.parent.parent
manifest = json.loads((here / 'manifest.json').read_text())
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
checks = []
for a in manifest['attempts']:
    if not a['final_current']:
        continue
    src = packet / 'lean' / (a['module'] + '.lean')
    assert a['exit'] == 0 and a['swaps'] == 0
    assert hashlib.sha256(src.read_bytes()).hexdigest() == a['source_sha256']
    assert a['axioms']
    for report in a['axioms']:
        names = re.search(r'\[([\s\S]*)\]', report)
        if names:
            assert {x.strip() for x in names[1].split(',')} <= allowed
    theorems = re.findall(r'^theorem (\w+)', src.read_text(), re.M)
    for theorem in theorems:
        assert any("." + theorem + "'" in report for report in a['axioms'])
    for imp in a['direct_imports']:
        assert hashlib.sha256(Path(imp['path']).read_bytes()).hexdigest() == imp['sha256']
    checks.append({'module': a['module'], 'attempt': a['attempt'], 'theorems': len(theorems)})
assert len(checks) == 3
root = packet.parents[2]
changes = subprocess.check_output(['git', 'diff', '--name-status', 'b5d8ab3c1', '--', str(packet)], text=True)
assert all(line.startswith('A\t') for line in changes.splitlines())
before = (here / 'before-statement.lean.txt').read_text()
after = (here / 'after-statement.lean.txt').read_text()
expected = before.replace('(Q : Nat) (deployedFailure : ℚ)', '(Q : Nat) (tx1 : Tx1) (poolTx2 : PoolTx2)').replace('deployedFailure', '(deployedFailureModel tx1 poolTx2)')
assert after == expected
assert 'h_R9_transport' in before and 'h_R9_transport' in after
result = {'status': 'pass', 'modules': checks, 'standard_axioms_only': True,
          'existing_tracked_sources_unchanged': True,
          'signature': 'probability specialization only; h_R9_transport retained',
          'requested_unconditional_transport': 'obstructed by checked P2-only countermodel'}
(here / 'audit.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
