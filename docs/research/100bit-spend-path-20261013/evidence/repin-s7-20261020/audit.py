#!/usr/bin/env python3
"""Read-only consistency check for the stopped S7 extraction packet."""
from pathlib import Path
import hashlib, json
B = Path(__file__).resolve().parent
ROOT = B.parents[4]
manifest = json.loads((B / 'manifest.json').read_text())
source = json.loads((B / 'source-check.json').read_text())
for row in source['files']:
    assert hashlib.sha256((ROOT / row['path']).read_bytes()).hexdigest() == row['sha256']
assert source['verifier_diff_from_freeze'] == ''
assert {Path(r['receipt']).parent.name: r['exit_status'] for r in manifest['attempts']} == {
    'extract-aeneas-current-owners': 2, 'extract-charon-current-owners': 0, 'extract-charon': 101}
for row in manifest['attempts']:
    receipt = json.loads((B / row['receipt']).read_text())
    for key in ['command', 'exit_status', 'wall_seconds', 'peak_rss_kib', 'swaps', 'limits']:
        assert row[key] == receipt[key]
    assert row['limits'] == {'memory.high': str(6 * 2**30), 'memory.max': str(8 * 2**30),
                             'memory.swap.max': '0', 'pids.max': '64'}
    assert row['swaps'] == 0
assert not manifest['new_theorems'] and not manifest['overflow_lemmas']
assert not manifest['generated_lean_files']
decls = json.loads((B / 'llbc-declarations.json').read_text())
assert len(decls) == 9
assert all(d['opacity'] == 'Transparent' and d['body_tag'] == ['Structured'] for d in decls)
error = (B / 'receipts/extract-aeneas-current-owners/stdout.log').read_text()
assert 'lines 257:4-264:5' in error and 'interp/InterpBorrows.ml, line 2731' in error
print('PASS: frozen source, capped receipts, declaration inventory, borrow stop, and no proof claim')
