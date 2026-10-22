#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re
p=Path(__file__).parent
sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
manifest=json.loads((p/'receipt/receipt.json').read_text())
assert manifest['exit_status']==0 and manifest['watchdog_abort'] is None
assert manifest['process_swaps']==0
assert manifest['source_sha256']==sha(p/'sources/S4CandidateTenOriginalPortBatchesV1.lean')
assert manifest['object_sha256']=='398ca3442876f7ae751b5966b4e190b14728eb6b08e2f2b8f5b97c931b44e49c'
cmd=json.loads((p/'receipt/command.json').read_text())
assert cmd['argv'][-1].endswith('/S4CandidateTenOriginalPortBatchesV1.lean')
pre=json.loads((p/'receipt/preflight.json').read_text())
assert pre['closure_preflight']['missing']==[] and pre['closure_preflight']['modules']==7479
ax=(p/'receipt/axioms.txt').read_text()
assert 'sorryAx' not in ax and 'propext' in ax and 'Classical.choice' in ax and 'Quot.sound' in ax
assert 'S4CandidateLoopFieldTransportV1' in (p/'receipt/direct-import-pins.json').read_text()
assert 'S4OriginalPortAcceptedQueryV1' in (p/'receipt/direct-import-pins.json').read_text()
for q in (p/'receipt').glob('*.olean'): raise AssertionError(f'compiled object included: {q}')
for line in (p/'SHA256SUMS').read_text().splitlines():
    expected, rel = line.split('  ', 1)
    assert sha(p/rel)==expected, f'checksum mismatch: {rel}'
print('PASS')
