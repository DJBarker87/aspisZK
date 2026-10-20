from pathlib import Path
import hashlib,json
root=Path(__file__).parent
repo=root.parents[4]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((root/'manifest.json').read_text())
assert m['schema']=='focused-extractor-proof-packet-v1'
for mod in m['modules']:
    assert sha(root/mod['source'])==mod['source_sha256']
    rec=json.loads((root/mod['receipt']).read_text())
    assert rec['exit_status']==0 and rec['source_sha256']==mod['source_sha256']
    assert rec['object_sha256']==mod['object_sha256']
    assert rec['axioms']==mod['axioms']
for name,item in m['direct_import_source_map'].items():
    assert sha(root/item['packet_snapshot_path'])==item['source_sha256'],name
    assert sha(repo/item['producer_manifest_repository_path'])
    assert sha(repo/item['producer_receipt_repository_path'])==item['producer_receipt_sha256']
log=(root/'attempt/lean.log').read_text()
for ax in m['modules'][0]['axioms']: assert ax in log,ax
assert 'sorryAx' not in log and 'native_decide' not in (root/m['modules'][0]['source']).read_text()
print('focused-extractor-proof-packet-v1: PASS')
