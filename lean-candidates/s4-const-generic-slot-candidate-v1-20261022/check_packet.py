#!/usr/bin/env python3
import hashlib, json, subprocess
from pathlib import Path
R=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
subprocess.run(['python3',str(R/'check_candidate.py')],check=True)
for line in (R/'SHA256SUMS').read_text().splitlines():
    digest, rel=line.split('  ',1)
    assert sha(R/rel)==digest, rel
m=json.loads((R/'manifest.json').read_text())
g=json.loads((R/'results/gate-result.json').read_text())
assert m['classification']=='isolated candidate-only performance experiment; not adopted'
assert g['candidate_artifact_sha256']==m['artifact']['candidate_elf_sha256']
assert len(g['six_fixture_rows'])==6 and g['all_six_outputs_match']
assert not g['item1_all_six_pass']
assert not any(p.suffix in {'.so','.elf','.o','.olean'} for p in R.rglob('*') if p.is_file())
assert m['artifact']['retained_outside_repository_packet']['sha256_verified']==g['candidate_artifact_sha256']
assert sum(not r['item1_pass'] for r in g['six_fixture_rows'])==6
assert all(r['stage1_checkpoint_tail_same'] and r['return_data_same'] for r in g['six_fixture_rows'])
assert json.loads((R/'results/native-evidence/receipt.json').read_text())['exit_status']==0
assert json.loads((R/'results/build-evidence/receipt.json').read_text())['exit_status']==0
print('PASS: candidate source, raw phase receipts, external retained artifact hash, six fixture outputs, strict B1 failure, no-binary inventory, and checksums agree')
