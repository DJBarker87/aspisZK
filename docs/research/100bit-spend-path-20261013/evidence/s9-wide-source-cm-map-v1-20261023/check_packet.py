from pathlib import Path
import hashlib, json
root=Path(__file__).resolve().parent
m=json.loads((root/'manifest.json').read_text())
assert m['schema']=='focused-extractor-proof-packet-v1' and m['compiled_objects_included'] is False
for f in m['files']:
 p=root/f['path']; assert p.is_file(), f['path']
 assert hashlib.sha256(p.read_bytes()).hexdigest()==f['sha256'], f['path']
assert not list(root.rglob('*.olean'))
r=json.loads((root/'run/receipt.json').read_text()); assert r['exit_status']==0 and r['process_swaps']==0
assert r['source_sha256']==hashlib.sha256((root/'sources/S9WideSourceCMMapV1.lean').read_bytes()).hexdigest()
log=(root/'run/lean.log').read_text()
for n in ('m31_reduce_u64_maps','cm_add_maps','cm_sub_maps','cm_mul_maps'):
 assert f'AspisR1S9WideSourceCMMapV1.{n}' in log
assert 'sorryAx' not in log
print('PASS')
