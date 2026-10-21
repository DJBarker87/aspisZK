#!/usr/bin/env python3
import hashlib, json
from pathlib import Path
root=Path(__file__).resolve().parent
manifest=json.loads((root/'manifest.json').read_text())
source=root/manifest['source']
receipt=json.loads((root/manifest['receipt']).read_text())
command=json.loads((root/manifest['command']).read_text())
pins=json.loads((root/'receipts/direct-import-pins.json').read_text())
assert receipt['exit_status']==0
assert receipt['source_revision_at_launch']==manifest['source_revision_at_launch']
assert receipt['source_sha256_before']==receipt['source_sha256_after']==manifest['source_sha256']
assert hashlib.sha256(source.read_bytes()).hexdigest()==manifest['source_sha256']
assert hashlib.sha256(Path(command['argv'][-1]).read_bytes()).hexdigest()==manifest['source_sha256']
assert command['source_revision_at_launch']==manifest['source_revision_at_launch']
assert command['lock_inode']==receipt['lock_inode']
assert receipt['object_sha256']==manifest['object_sha256']
assert hashlib.sha256(Path(manifest['object_path']).read_bytes()).hexdigest()==manifest['object_sha256']
assert int(float(manifest['wall_seconds'])*1000)==int(float(receipt['wall_seconds'])*1000)
assert manifest['peak_rss_bytes']==4057530368 and manifest['swap_bytes']==0
assert 'tx2_after_resume_candidate_twelve_fullwide_coordinate_bounds' in source.read_text()
log=(root/'receipts/lean.log').read_text()
assert 'tx2_after_resume_candidate_twelve_fullwide_coordinate_bounds' in log
for ax in ['propext','Classical.choice','Quot.sound']: assert ax in log
assert 'sorryAx' not in log
for item in pins['direct_imports']:
    assert hashlib.sha256(Path(item['source']).read_bytes()).hexdigest()==item['source_sha256']
    assert hashlib.sha256(Path(item['selected_object']).read_bytes()).hexdigest()==item['object_sha256']
    assert hashlib.sha256(Path(item['producer_record']).read_bytes()).hexdigest()==item['producer_record_sha256']
ctx=pins['query_loop_transitive_provenance']
assert hashlib.sha256(Path(ctx['source']).read_bytes()).hexdigest()==ctx['source_sha256']
assert hashlib.sha256(Path(ctx['selected_object']).read_bytes()).hexdigest()==ctx['object_sha256']
assert hashlib.sha256(Path(ctx['receipt']).read_bytes()).hexdigest()==ctx['receipt_sha256']
assert ctx['source_revision'] in Path(ctx['receipt']).read_text()
assert not list(root.rglob('*.olean'))
print('PASS: theorem source, launch receipt, object pin, direct imports, QueryLoop provenance, axioms, and source-only packet')
