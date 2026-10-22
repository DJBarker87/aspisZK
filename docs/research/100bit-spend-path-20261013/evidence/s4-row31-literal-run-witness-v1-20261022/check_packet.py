#!/usr/bin/env python3
from pathlib import Path
import hashlib, json
root=Path(__file__).resolve().parent
sha=lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
src=root/'sources/R1LiteralQuerySampleRunWitness.lean'
pre=json.loads((root/'receipt/preflight.json').read_text())
rec=json.loads((root/'receipt/receipt.json').read_text())
assert sha(src)==pre['source_sha256']==rec['source_sha256']
assert sha(root/'receipt/LEAN_PATH.txt')==pre['profile_sha256']
assert rec['exit_status']==0 and rec['swaps']==0
assert rec['object_sha256']==pre['object_sha256']
assert rec['revision_at_launch']==pre['source_revision']
assert "valid_row31_success_decodes_with_run" in src.read_text()
assert "(row31PayloadQueryRun H P bytes).1 = .ok xs" in src.read_text()
assert "List Nat" in json.loads((root/'findings.json').read_text())['challenge_value_type']
assert not list(root.rglob('*.olean'))
for name,item in pre['direct_imports'].items():
    f=Path(item['path'])
    assert f.is_file() and sha(f)==item['sha256'],name
print('S4 row31 literal run witness packet: PASS')
