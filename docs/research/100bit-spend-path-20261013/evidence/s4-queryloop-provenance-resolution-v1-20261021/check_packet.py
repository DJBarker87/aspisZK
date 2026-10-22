#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
r=Path(__file__).resolve().parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
meta=json.loads((r/'evidence/owner-resolution.json').read_text())
receipt=json.loads((r/'evidence/query-loop-v2-producer-receipt.json').read_text())
assert meta['producer_exit_status']==0 and receipt['exit_status']==0
assert meta['current_source_sha256']==meta['producer_source_sha256']==receipt['source_sha256']==sha(r/'sources/Stage2ContinuationQueryLoop-current.lean')
objinv=json.loads((r/'evidence/current-object-inventory-entry.json').read_text())
assert objinv['object_sha256']==meta['selected_object_sha256']=='20a8d68464f20012572d37f1228045ac2a42a5776e3d5f8281f7180b24c0d450'
assert objinv['source_sha256']==meta['current_source_sha256'] and objinv['status']=='current-compiled'
assert meta['v1_receipt_source_sha256']=='6eec6a3fe88cb01481e4933b287d7c4c52f72eefce6f30fdc5ae33731827742c'
assert sha(r/'sources/Stage2ContinuationQueryLoop-v1.lean')==meta['v1_receipt_source_sha256']
diff=(r/'evidence/v1-to-current.diff').read_text()
assert diff.count('@@')==2 and '-    simp only [verifier.candidate.query_loop_loop.body, Stage2ContinuationOwnedLoop.body,' in diff and '+    rfl' in diff
assert 'def verifier.candidate.query_loop_loop.body' not in diff.split('@@')[1].split('@@')[0]
for line in (r/'SHA256SUMS').read_text().splitlines():
 h,n=line.split('  ',1); f=r/n; assert f.is_file() and sha(f)==h,n
assert not list(r.rglob('*.olean'))
print('provenance resolution checks PASS: selected object matches successful v2/current source; only v1 proof-script hunk differs')
