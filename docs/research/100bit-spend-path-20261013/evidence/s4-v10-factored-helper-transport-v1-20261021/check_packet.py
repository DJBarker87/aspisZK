#!/usr/bin/env python3
import hashlib, json, pathlib
root=pathlib.Path(__file__).resolve().parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
for line in (root/'SHA256SUMS').read_text().splitlines():
    digest, name=line.split('  ',1)
    assert sha(root/name)==digest, name
r=json.loads((root/'receipts/receipt.json').read_text())
assert r['schema']=='focused-lean-receipt-v1' and r['exit_status']==0 and r['swap_bytes']==0
source=(root/'sources/S4V10FactoredHelperTransportV1.lean').read_text()
assert 'theorem factored_helper_eq_fixed' in source
assert 'v10Tail_to_current' in source and 'head_value_eq_fixed' in source
assert (root/'receipts/compile.log').is_file()
assert not list(root.rglob('*.olean'))
print('PASS: packet hashes, theorem/source references, and no packaged binaries')
