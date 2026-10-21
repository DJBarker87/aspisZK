#!/usr/bin/env python3
from pathlib import Path
import hashlib, json
root=Path(__file__).resolve().parent
sha=lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((root/'manifest.json').read_text())
assert manifest['schema']=='focused-extractor-proof-packet-v1'
listed={row['path'] for row in manifest['files']}
actual={p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file() and p.name!='manifest.json'}
assert listed==actual, f"file inventory mismatch: missing={sorted(actual-listed)} extra={sorted(listed-actual)}"
for row in manifest['files']:
 p=root/row['path']
 assert p.stat().st_size==row['size_bytes'], f"size mismatch {row['path']}"
 assert sha(p)==row['sha256'], f"hash mismatch {row['path']}"
map_path=root/manifest['direct_import_source_map']
source_map=json.loads(map_path.read_text())
for module, owner in source_map['dependency_owner_snapshots'].items():
 sp=root/owner['source_copy']; rp=root/owner['producer_receipt_copy']
 assert sp.is_file() and sha(sp)==owner['source_sha256'], f"source mismatch: {module}"
 assert rp.is_file() and sha(rp)==owner['producer_receipt_sha256'], f"producer receipt mismatch: {module}"
 rec=json.loads(rp.read_text())
 assert rec['exit_status']==0, f"non-green producer: {module}"
 assert rec['source_sha256']==owner['source_sha256'], f"producer source pin mismatch: {module}"
 assert rec['object_sha256']==owner['object_sha256'], f"producer object pin mismatch: {module}"
 if owner.get('producer_manifest_copy'):
  mp=root/owner['producer_manifest_copy']
  assert mp.is_file() and sha(mp)==owner['producer_manifest_sha256'], f"producer manifest mismatch: {module}"
for module, entry in source_map['direct_imports'].items():
 sp=root/entry['source_file']
 assert sp.is_file() and sha(sp)==entry['source_sha256'], f"direct source mismatch: {module}"
receipt=json.loads((root/manifest['modules'][0]['receipt']).read_text())
module=manifest['modules'][0]
assert receipt['exit_status']==module['exit_status']==0
assert receipt['source_sha256']==module['source_sha256']
assert receipt['object_sha256']==module['object_sha256']
assert receipt['source_revision_at_launch']==module['source_revision']
assert receipt['process_swaps']==module['swap_bytes']==0
assert manifest['selected_closure']['uses_custom_axioms'] is False
assert manifest['selected_closure']['uses_sorry'] is False
assert manifest['selected_closure']['uses_native_decide'] is False
assert module['axioms']==['propext','Classical.choice','Quot.sound']
print('PASS: packet files, direct owners, producer receipts, and standard-only theorem pins')
