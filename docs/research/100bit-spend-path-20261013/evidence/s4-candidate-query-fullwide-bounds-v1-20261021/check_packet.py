#!/usr/bin/env python3
import hashlib, json
from pathlib import Path
root = Path(__file__).resolve().parent
src = root/'sources/S4V10CandidateQueryFullWideBoundsV1.lean'
receipt = json.loads((root/'receipts/receipt.json').read_text())
command = json.loads((root/'receipts/command.json').read_text())
assert receipt['exit_status'] == 0
assert receipt['source_sha256_before'] == receipt['source_sha256_after']
assert hashlib.sha256(src.read_bytes()).hexdigest() == receipt['source_sha256_before']
assert hashlib.sha256(Path(command['argv'][-1]).read_bytes()).hexdigest() == receipt['source_sha256_before']
assert receipt['launch_revision'] == command['launch_revision']
assert receipt['object_sha256']
log=(root/'receipts/lean.log').read_text()
for name in ['current_wide_to_full_preserves_canonical','current_array_to_full_preserves_canonical','candidate_query_fullwide_coordinate_bounds']:
    assert name in src.read_text()
assert 'does not depend on any axioms' in log
assert '[propext,' in log and 'Classical.choice' in log and 'Quot.sound' in log
assert not list(root.rglob('*.olean'))
print('PASS: source, receipt, imports, axioms, and source-only packet checks')
