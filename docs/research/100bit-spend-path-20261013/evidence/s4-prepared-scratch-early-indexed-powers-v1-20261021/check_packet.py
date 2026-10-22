#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, sys
root = Path(__file__).resolve().parent
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
m = json.loads((root / 'manifest.json').read_text())
assert sha(root / m['source']) == m['source_sha256']
r = json.loads((root / m['compile_receipt']).read_text())
assert r['exit_status'] == 0 and r['source_sha256'] == m['source_sha256']
assert r['object_sha256'] == m['object_sha256']
assert r['process_swaps'] == 0
assert r['wall_seconds'] == 15.459
assert r['source_revision_at_launch'] == json.loads((root/'evidence/preflight.json').read_text())['source_revision']
assert m['direct_imports'] == json.loads((root/'evidence/preflight.json').read_text())['direct_imports']
ax = (root/'evidence/axioms.txt').read_text()
assert 'propext' in ax and 'Classical.choice' in ax and 'Quot.sound' in ax and 'sorryAx' not in ax
for p in root.rglob('*'):
    if p.is_file():
        assert p.suffix not in {'.olean','.ilean','.ir'}, f'compiled artifact in source-only packet: {p}'
for line in (root/'SHA256SUMS').read_text().splitlines():
    expected, rel = line.split('  ',1)
    assert sha(root/rel) == expected, rel
print('PASS: early indexed powers packet hashes, receipt, imports, axioms, and source-only inventory')
