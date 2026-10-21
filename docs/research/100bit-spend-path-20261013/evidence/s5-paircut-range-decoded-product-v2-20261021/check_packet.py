#!/usr/bin/env python3
import hashlib, json
from pathlib import Path
root=Path(__file__).resolve().parent
m=json.loads((root/'manifest.json').read_text())
assert m['schema']=='focused-extractor-proof-packet-v1'
assert m['packet']==root.name
for f in m['files']:
 p=root/f['path']; b=p.read_bytes()
 assert len(b)==f['size_bytes'], f['path']
 assert hashlib.sha256(b).hexdigest()==f['sha256'], f['path']
r=json.loads((root/'receipts/receipt.json').read_text()); mod=m['modules'][0]
assert r['exit_status']==mod['exit_status']==0
assert r['source_sha256']==mod['source_sha256']
assert r['object_sha256']==mod['object_sha256']
assert r['git_head_at_launch']==mod['source_revision']
assert r['compiler_sha256']==m['compiler']['sha256']
assert r['argv'][1:3]==['-j1','-M4400']
log=(root/'receipts/lean.log').read_text()
assert "'AspisR1S5PairCutRangeDecodedProductV3.successful_run_decoded_product_sum' depends on axioms: [propext," in log
assert "'AspisR1S5PairCutRangeDecodedProductV3.checked_field_run_decoded_product_sum' depends on axioms: [propext," in log
source=(root/'sources/S5PairCutRangeDecodedProductV3.lean').read_text()
assert 'AspisR1DotCountBoundV1.AcceptedPushTrace' in source
assert 'List.Forall₂' in source
for name, pin in m['direct_import_source_map'].items():
 rec=json.loads((root/pin['producer_receipt']).read_text())
 assert rec['exit_status']==0, name
 assert rec['source_sha256']==pin['source_sha256'], name
 assert rec['object_sha256']==pin['object_sha256'], name
assert not any(p.suffix in {'.olean','.ilean','.c','.so','.dylib'} for p in root.rglob('*'))
print('packet checks passed')
