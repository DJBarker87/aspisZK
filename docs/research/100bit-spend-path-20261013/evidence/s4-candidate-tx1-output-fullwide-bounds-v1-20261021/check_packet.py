#!/usr/bin/env python3
import hashlib, json
from pathlib import Path
root=Path(__file__).resolve().parent
src=root/'sources/S4CandidateTx1OutputFullWideBoundsV1.lean'
r=json.loads((root/'receipts/receipt.json').read_text())
c=json.loads((root/'receipts/command.json').read_text())
assert r['exit_status']==0 and r['source_sha256_before']==r['source_sha256_after']
assert hashlib.sha256(src.read_bytes()).hexdigest()==r['source_sha256_before']
assert hashlib.sha256(Path(c['argv'][-1]).read_bytes()).hexdigest()==r['source_sha256_before']
assert c['launch_revision']==r['launch_revision']
assert r['object_sha256']
log=(root/'receipts/lean.log').read_text()
assert 'candidate_source_tx1_success_ten_fullwide_coordinate_bounds' in log
assert '[propext,' in log and 'Classical.choice' in log and 'Quot.sound' in log
pins=json.loads((root/'receipts/direct-import-pins.json').read_text())['imports']
assert len(pins)==2
for p in pins:
 assert hashlib.sha256(Path(p['selected_object']).read_bytes()).hexdigest()==p['object_sha256']
 assert hashlib.sha256(Path(p['source']).read_bytes()).hexdigest()==p['source_sha256']
assert not list(root.rglob('*.olean'))
print('PASS: source, receipt, theorem, direct imports, and source-only packet')
