from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parent
m=json.loads((root/'manifest.json').read_text())
assert m['schema']=='focused-extractor-proof-packet-v1' and m['compiled_objects_included'] is False
for f in m['files']:
 p=root/f['path']; assert p.is_file(), f['path']
 assert hashlib.sha256(p.read_bytes()).hexdigest()==f['sha256'], f['path']
assert not list(root.rglob('*.olean')) and not list(root.rglob('*.ilean'))
r=json.loads((root/'run/receipt.json').read_text())
assert r['exit_status']==0 and r['process_swaps']==0
src=root/'sources/S9WideSourceQMCanonicalV1.lean'
assert r['source_sha256']==hashlib.sha256(src.read_bytes()).hexdigest()
log=(root/'run/lean.log').read_text()
for n in ['qcut_qm_add_total_canonical','qcut_qm_sub_total_canonical','qcut_mul_u_total_canonical']:
 assert f'AspisR1S9WideSourceQMCanonicalV1.{n}' in log
assert 'sorryAx' not in log
print('PASS')
