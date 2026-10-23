from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parent
m=json.loads((root/'manifest.json').read_text())
assert m['schema']=='focused-extractor-proof-packet-v1' and m['compiled_objects_included'] is False
for f in m['files']:
 p=root/f['path']; assert p.is_file(), f['path']
 assert hashlib.sha256(p.read_bytes()).hexdigest()==f['sha256'], f['path']
assert not list(root.rglob('*.olean'))
for tag,mod,namespace,theorem in [('add','S9WideSourceQMAddV1','AspisR1S9WideSourceQMAddV1','qm_add_maps'),('sub','S9WideSourceQMSubV1','AspisR1S9WideSourceQMSubV1','qm_sub_maps')]:
 r=json.loads((root/f'run/{tag}/receipt.json').read_text())
 assert r['exit_status']==0 and r['process_swaps']==0
 src=root/f'sources/{mod}.lean'
 assert r['source_sha256']==hashlib.sha256(src.read_bytes()).hexdigest()
 log=(root/f'run/{tag}/lean.log').read_text()
 assert f'{namespace}.{theorem}' in log and 'sorryAx' not in log
print('PASS')
