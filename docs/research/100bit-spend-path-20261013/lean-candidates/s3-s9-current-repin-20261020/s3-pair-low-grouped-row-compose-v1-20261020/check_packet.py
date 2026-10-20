from pathlib import Path
import hashlib,json
root=Path(__file__).parent
m=json.loads((root/'manifest.json').read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert m['schema']=='focused-extractor-proof-packet-v1'
assert sha(root/m['source']['path'])==m['source']['sha256']
for name,item in m['direct_import_source_map'].items():
    assert sha(root/item['path'])==item['sha256'],name
attempt=root/m['attempt']; receipt=json.loads((attempt/'receipt.json').read_text()); pre=json.loads((attempt/'preflight.json').read_text())
assert receipt['exit_status']==0
assert receipt['source_sha256']==m['source']['sha256']
assert receipt['object_sha256']==m['object']['sha256']
assert pre['lean_sha256']==m['compiler']['sha256']
assert pre['source_sha256']==m['source']['sha256']
log=(attempt/'lean.log').read_text()
for ax in m['axioms']:
    assert ax in log,ax
assert 'sorryAx' not in log and 'native_decide' not in (root/m['source']['path']).read_text()
print('focused Lean proof packet: PASS')
