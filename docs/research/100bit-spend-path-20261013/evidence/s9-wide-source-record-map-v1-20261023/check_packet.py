from pathlib import Path
import hashlib, json
root=Path(__file__).resolve().parent
m=json.loads((root/'manifest.json').read_text())
assert m['schema']=='focused-extractor-proof-packet-v1'
assert m['compiled_objects_included'] is False
for f in m['files']:
 p=root/f['path']; assert p.is_file(), f['path']
 assert hashlib.sha256(p.read_bytes()).hexdigest()==f['sha256'], f['path']
assert not list(root.rglob('*.olean'))
receipt=json.loads((root/'run/receipt.json').read_text())
assert receipt['exit_status']==0 and receipt['process_swaps']==0
assert receipt['source_sha256']==hashlib.sha256((root/'sources/S9WideSourceRecordMapV1.lean').read_bytes()).hexdigest()
log=(root/'run/lean.log').read_text()
for name in ('wide_mul_by_r_maps_to_qcut','wide_mul_u_maps_to_qcut_formula'):
 assert f'AspisR1S9WideSourceRecordMapV1.{name}' in log
assert 'sorryAx' not in log
print('PASS')
