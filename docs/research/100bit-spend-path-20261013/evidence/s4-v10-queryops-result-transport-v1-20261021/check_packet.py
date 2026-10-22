from pathlib import Path
import hashlib,json,re,sys
p=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
manifest=json.loads((p/'manifest.json').read_text())
assert manifest['schema']=='focused-extractor-proof-packet-v1'
assert manifest['packet']==p.name
for module in manifest['modules']:
 src=p/module['source'];assert src.is_file() and sha(src.read_bytes())==module['source_sha256']
 assert module['exit_status']==0 and module['axioms']==['propext','Classical.choice','Quot.sound']
 rec=json.loads((p/module['receipt']).read_text());assert rec['exit_status']==0 and rec['source_sha256']==module['source_sha256']
 assert rec['object_sha256']==module['object_sha256']
 assert rec['launch_revision']==module['source_revision']
 pre=json.loads((p/module['preflight']).read_text());assert pre['source_sha256']==module['source_sha256'] and pre['launch_revision']==module['source_revision']
 log=(p/'evidence'/('lean-'+Path(module['receipt']).stem.removeprefix('receipt-')+'.log')).read_text()
 for theorem in ['fullArrayToV10_map','literal_dots_success_eq_current','successful_query_candidate_dots_transfers','successful_query_candidate_refines_old_model']:
  assert theorem in log
 assert 'sorryAx' not in log
for name,owner in manifest['direct_import_source_map'].items():
 src=p/owner['source'];assert src.is_file() and sha(src.read_bytes())==owner['source_sha256'],name
 assert sha(Path(owner['selected_object_original_path']).read_bytes())==owner['selected_object_sha256'],name
 prod=p.parent.parent/owner['producer_manifest'];assert prod.is_file() and sha(prod.read_bytes())==owner['producer_manifest_sha256'],name
for rel in manifest['evidence_files']:
 assert (p/rel).is_file(),rel
for entry in manifest['files']:
 f=p/entry['path'];assert f.is_file() and sha(f.read_bytes())==entry['sha256'] and f.stat().st_size==entry['size_bytes'],entry['path']
for line in (p/'SHA256SUMS').read_text().splitlines():
 digest, rel=line.split('  ',1);assert sha((p/rel).read_bytes())==digest,rel
# Source-only packet: no Lean objects, archives, or binary payloads.
for f in p.rglob('*'):
 if f.is_file():
  assert f.suffix not in {'.olean','.ilean','.a','.so','.dylib','.o'},str(f)
print('packet source/import/evidence hashes verified; no compiled objects')
