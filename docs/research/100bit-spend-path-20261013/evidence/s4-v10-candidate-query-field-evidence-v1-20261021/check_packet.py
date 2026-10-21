#!/usr/bin/env python3
import hashlib, json
from pathlib import Path
root = Path(__file__).resolve().parent
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
receipt = json.loads((root/'receipts/receipt.json').read_text())
command = json.loads((root/'receipts/command.json').read_text())
pins = json.loads((root/'receipts/direct-import-pins.json').read_text())
source = root/'sources/S4V10CandidateQueryFieldEvidenceV1.lean'
assert receipt['exit_status'] == 0
assert receipt['source_unchanged']
assert receipt['source_sha256_before'] == receipt['source_sha256_after'] == sha(source)
assert receipt['object_sha256'] and len(receipt['object_sha256']) == 64
assert command['source_sha256_at_launch'] == receipt['source_sha256_after']
assert command['launch_revision'] == receipt['launch_revision']
assert '-j1' in command['argv'] and '4400' in command['argv']
assert 'S4V10CallbackOutputFieldResultsV1' in source.read_text()
log = (root/'receipts/lean.log').read_text()
assert 'candidate_query_success_field_evidence' in log
body = source.read_text()
assert 'def CandidateQueryFieldEvidence' in body
assert '(concreteCandidateQueryOps rest).dots q g = .ok candidateValues' in body
assert 'currentArrayToFull currentValues = candidateValues' in body
assert "depends on axioms: [propext," in log and 'sorryAx' not in log
elapsed = (root/'receipts/time.log').read_text()
assert 'maximum resident set size' in elapsed and 'swaps' in elapsed
assert len(pins['imports']) == 3
for entry in pins['imports']:
    dep = root/'dependencies'/(entry['module']+'.lean')
    assert sha(dep) == entry['source_sha256']
    assert len(entry['selected_object_sha256']) == 64
assert not list(root.rglob('*.olean'))
for line in (root/'SHA256SUMS').read_text().splitlines():
    digest, rel = line.split('  ', 1)
    assert sha(root/rel) == digest, rel
print('packet checks passed')
