#!/usr/bin/env python3
import hashlib,json
from pathlib import Path
root=Path(__file__).resolve().parent; m=json.loads((root/'manifest.json').read_text())
assert m['schema']=='focused-extractor-proof-packet-v1' and m['lean_exit_status']==0
assert m['packet']=='s9-combined-qm-to-current-v1-20261023'
assert not m['compiled_objects_included'] and not m['object_in_packet']
assert not list(root.rglob('*.olean')) and not list(root.rglob('*.ilean'))
for f in m['files']:
 p=root/f['path']; b=p.read_bytes(); assert len(b)==f['bytes'] and hashlib.sha256(b).hexdigest()==f['sha256'],f['path']
r=json.loads((root/'evidence/receipt.json').read_text())
assert r['exit_status']==0 and r['source_sha256']==m['source_sha256'] and r['object_sha256']==m['object_sha256']
assert hashlib.sha256((root/'sources/S9CombinedQMToCurrentV1.lean').read_bytes()).hexdigest()==m['source_sha256']
log=(root/'evidence/lean.log').read_text(); assert all(x in log for x in ['actual_qm_mul_to_current','combined_qm_mul_to_current'])
assert log.count('depends on axioms:')==2 and 'sorryAx' not in log
print('PASS: combined QM-to-current source-only packet, receipt, exact pins, and theorem audits')
