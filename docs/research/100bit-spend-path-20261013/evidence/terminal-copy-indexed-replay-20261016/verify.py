#!/usr/bin/env python3
import hashlib, json
from pathlib import Path
E=Path(__file__).resolve().parent
sums=E/'SHA256SUMS'
sha=lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
for line in sums.read_text().splitlines():
    expected, rel=line.split('  ',1)
    p=E/rel
    assert p.is_file(), f'missing {rel}'
    assert sha(p)==expected, f'hash mismatch {rel}'
assert not any(p.name.endswith('.key') or 'keypair' in p.name.lower() for p in E.rglob('*') if p.is_file()), 'private-key-like file included'
summary=json.loads((E/'summary.json').read_text())
assert len(summary['cases'])==4
assert summary['all_accepted'] and summary['all_equal_checkpoint_asr8_initial_images']
assert not summary['settlement_exercised'] and not summary['private_keys_copied']
report=json.loads((E/'source-manifest-git-comparison.json').read_text())
assert report['checks'][0]['files']==504 and report['checks'][0]['matched']==504 and not report['checks'][0]['mismatches']
assert report['checks'][1]['files']==508 and report['checks'][1]['matched']==505 and len(report['checks'][1]['mismatches'])==3
for c in summary['cases']:
    assert c['exit']==0 and c['stage2_delta']==0 and c['checkpoint_equal'] and c['asr8_equal'] and c['initial_images_equal']
print('evidence checks passed')
