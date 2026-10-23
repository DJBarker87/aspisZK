#!/usr/bin/env python3
import hashlib, json, pathlib, sys
root = pathlib.Path(__file__).resolve().parent
m = json.loads((root / 'manifest.json').read_text())
assert m['schema'] == 'focused-extractor-proof-packet-v1'
assert m['lean_exit_status'] == 0 and not m['object_in_packet'] and not m['compiled_objects_included']
assert m['closure_summary']['resolved_modules'] == 5266 and m['closure_summary']['missing_modules'] == []
assert m['toolchain_and_resource_evidence']['memory_swap_max_bytes'] == 0
assert m['toolchain_and_resource_evidence']['aggregate_process_tree_rss'].startswith('not recorded')
assert m['object_sha256'] == '1150184198f80d75ac9df036155a7263a362e2ba64f4d83f9bf47d22c9709163'
files = sorted(p for p in root.rglob('*') if p.is_file() and p.name not in ('manifest.json',))
rows=[]
for p in files:
 rel=p.relative_to(root).as_posix(); data=p.read_bytes()
 rows.append({'path':rel,'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data)})
source = root/'sources/S9PairMixedInputCanonicalV1.lean'
assert hashlib.sha256(source.read_bytes()).hexdigest() == m['source_sha256']
log=(root/'evidence/lean.log').read_text()
for theorem in ('pair_read_current_canonical','pair_read_mixed_call_maps_to_source','pair_read_mixed_call_success_reflects_source'):
 assert theorem in log
assert 'sorryAx' not in log and 'admitAx' not in log
assert 'scope_swap_peak_bytes' in (root/'evidence/receipt.json').read_text()
m['files']=rows
(root/'manifest.json').write_text(json.dumps(m,indent=2)+'\n')
print('PASS',len(rows),'files')
