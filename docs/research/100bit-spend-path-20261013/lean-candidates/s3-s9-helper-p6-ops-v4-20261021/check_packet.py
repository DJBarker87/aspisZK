#!/usr/bin/env python3
import hashlib, json
from pathlib import Path
D = Path(__file__).resolve().parent
m = json.loads((D / 'manifest.json').read_text())
assert m['schema'] == 'focused-extractor-proof-packet-v1'
assert m['packet'] == D.name
for rel, expected in [(m['target_source'], m['target_source_sha256']),
                      (m['differential']['source'], m['differential']['source_sha256'])]:
    got = hashlib.sha256((D / rel).read_bytes()).hexdigest()
    assert got == expected, (rel, got, expected)
dep = m['direct_import_source_map']['Aeneas.Std.RangeIter']
assert hashlib.sha256((D / dep['source_path']).read_bytes()).hexdigest() == dep['source_sha256']
r = json.loads((D / 'evidence/attempt/receipt.json').read_text())
assert r['exit_status'] == 0 and r['source_sha256'] == m['target_source_sha256']
assert r['object_sha256'] == m['target_object_sha256']
assert r['scope_swap_peak_bytes'] == 0 and r['scope_memory_peak_bytes'] == m['result']['scope_memory_peak_bytes']
p = json.loads((D / 'evidence/attempt/preflight.json').read_text())
assert p['target'] == 'RangeFoldP6ModelV1' and p['source_sha256'] == m['target_source_sha256']
assert p['lean_sha256'] == m['compiler']['sha256']
assert p['limits']['memory.swap.max'] == '0'
for rel in m['receipts']:
    assert (D / rel).is_file(), rel
for pth in D.rglob('*'):
    if pth.is_file():
        assert pth.suffix not in {'.olean', '.ilean', '.ir', '.exe'}, pth
print('PASS focused P6 range-fold source/evidence packet')
