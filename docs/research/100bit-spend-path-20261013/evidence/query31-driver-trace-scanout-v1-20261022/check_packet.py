#!/usr/bin/env python3
from pathlib import Path
import hashlib, json
root = Path(__file__).resolve().parent
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
m = json.loads((root / 'manifest.json').read_text())
r = json.loads((root / 'receipt/receipt.json').read_text())
s = root / 'sources/Query31DriverTraceScanOutV1.lean'
assert sha(s) == m['source_sha256'] == r['source_sha256']
assert r['exit_status'] == 0 and r['process_swap_bytes'] == '0' and r['watchdog_abort'] is None
assert m['receipt']['process_swaps'] == 0
assert r['object_sha256'] == m['object_sha256']
assert m['axioms'] == ['propext', 'Classical.choice', 'Quot.sound']
assert '[propext,' in (root / 'receipt/lean.log').read_text()
assert 'sorryAx' not in (root / 'receipt/lean.log').read_text()
assert not list(root.rglob('*.olean'))
for d in m['direct_imports']:
    p=Path(d['object_path'])
    assert p.is_file() and sha(p)==d['object_sha256'], d['module']
profile=(root/'receipt/LEAN_PATH.txt').read_text().splitlines()
assert profile[0].endswith('/s4-scanout-run-core-v1/objects')
assert profile[1].endswith('/d18-query-finish-accepted-bridge-v3/objects')
print('PASS')
