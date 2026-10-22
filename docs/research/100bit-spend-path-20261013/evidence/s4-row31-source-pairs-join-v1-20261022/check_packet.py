#!/usr/bin/env python3
from pathlib import Path
import hashlib, json
root=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
src=root/'sources/S4LiteralRow31PairsJoinV1.lean'
pre=json.loads((root/'receipt/preflight.json').read_text())
rec=json.loads((root/'receipt/receipt.json').read_text())
find=json.loads((root/'findings.json').read_text())
assert sha(src)==pre['source_sha256']==rec['source_sha256']
base=(root/'receipt/BASE_LEAN_PATH.txt').read_text().strip()
assert sha(root/'receipt/BASE_LEAN_PATH.txt')==pre['base_profile_sha256']
cmd=json.loads((root/'receipt/command.json').read_text())
executed=next(a[len('LEAN_PATH='):] for a in cmd['argv'] if a.startswith('LEAN_PATH='))
assert (root/'receipt/LEAN_PATH.txt').read_text()==executed
assert executed.split(':')==pre['profile_roots']+base.split(':')
assert rec['exit_status']==0 and rec['process_swaps']==0
assert rec['object_sha256']==find['output_object_sha256']
assert rec['source_revision_at_launch']==pre['source_revision']
assert 'row31_success_list_eq_source_pairs' in src.read_text()
assert 'hstate' in src.read_text() and 'hdigest' in src.read_text()
assert find['challenge_value_type']=='List Nat'
assert find['axioms']==['propext','Classical.choice','Quot.sound']
assert not list(root.rglob('*.olean'))
for item in find['direct_imports'].values():
    p=Path(item['object'])
    assert p.is_file() and sha(p)==item['sha256']
print('S4 row31 source-pairs join packet: PASS')
