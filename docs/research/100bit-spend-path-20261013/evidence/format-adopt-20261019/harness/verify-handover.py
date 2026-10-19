#!/usr/bin/env python3
"""Verify retained handover evidence against source and baseline evidence on host."""
import hashlib, json
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-r1-format-adopt-20261019')
sha=lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
source=json.loads((H/'source-hashes.json').read_text())
for f in source['files']:
    assert sha(H/'src'/f['path']) == f['sha256'], f['path']
codec=H/'receipts/gate-codec-1233/stdout.log'
assert sha(codec)=='3ef16b12a329dd6d74b472cd75e5554c1ef8d98c618de3117f87b6c50d73e321'
assert codec.read_text().splitlines()[-1]=='complete 1233'
audit=json.loads((H/'runs/counter-audit-eight-way.json').read_text())
base=json.loads(Path('/home/dombarker/project-offloads/codex-r1p-writer-migration-20261019/out/ordered-counter-new.json').read_text())
# HashMap output order is nondeterministic for the repeated-input summary.
for r in [audit, base]:
    r['hash_input_counts']['repeated_exact_inputs'].sort(key=lambda x: x['input_hex'])
for k in ['ordered_digest_calls','hash_input_counts','acceptance']:
    assert audit[k]==base[k],k
assert len(audit['ordered_digest_calls'])==583
adopt=json.loads((H/'runs/counter-adopted.json').read_text())
assert adopt['acceptance']['tx1'] and adopt['acceptance']['tx2']
assert adopt['fixture']['proof_len']==57607
fixtures=[]
for p in sorted((H/'runs/adopt').glob('*/task/r1-s2-proof.bin')):
    label=p.parent.parent.name
    pub=p.with_name('r1-s2-public-asf8.bin')
    saved=Path('/home/dombarker/project-offloads/aspis-r1-rollover-measurement-20261019/fixtures')/label/pub.name
    assert pub.read_bytes()==saved.read_bytes()
    assert p.stat().st_size==57607
    fixtures.append(dict(fixture=label,proof_sha256=sha(p),public_sha256=sha(pub),public_equal=True))
report=dict(source_revision=source['handover_revision'],source_hashes_matched=len(source['files']),
    codec=dict(outputs=1233,bytes=codec.stat().st_size,sha256=sha(codec),baseline_byte_identical=True),
    ordered_audit=dict(calls=583,baseline_ordered_calls_counts_checkpoint_equal=True),
    ordered_adopted=dict(calls=len(adopt['ordered_digest_calls']),counts=adopt['hash_input_counts'],
        note='Binary trees change commitment inputs/order; 583-call equality applies only to audit build.'),
    fixtures=fixtures)
(H/'handover-verification.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
