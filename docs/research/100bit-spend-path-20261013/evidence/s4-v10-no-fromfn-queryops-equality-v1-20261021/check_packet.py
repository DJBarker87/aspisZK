#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,sys
root=Path(__file__).resolve().parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
r=json.loads((root/'evidence/receipt.json').read_text())
assert r['exit_status']==0
assert r['source_sha256']==sha(root/'sources/S4NoFromFnQueryOpsEqualityV1.lean')
assert r['object_sha256']=='dcf017e2fdeb86bf7db7d6373ff7b187bc8891dbb23618b3896d38549ef15186'
log=(root/'evidence/lean.log').read_text()
for name in ['noFromFnQueryOps_eq_concrete','queryWithOps_eq_all_results','query_loop_eq_all_results']:
 assert f"AspisR1S4V10NoFromFnQueryOpsEqualityV1.{name}' depends on axioms: [propext," in log
assert 'sorryAx' not in log
assert not list(root.rglob('*.olean')) and not list(root.rglob('*.ilean'))
imports=json.loads((root/'evidence/direct-imports.json').read_text())
assert imports['S4V10NoFromFnKernelRootV1']['object_sha256']=='ca18a216918afcabfd2731a0b72a6f74f2bf872aa7819b5ac9ca68034e9ab3a3'
assert imports['Stage2ContinuationQueryLoop']['object_sha256']=='20a8d68464f20012572d37f1228045ac2a42a5776e3d5f8281f7180b24c0d450'
assert imports['Stage2ContinuationQueryLoop']['source_snapshot_matches_producer'] is False
for line in (root/'SHA256SUMS').read_text().splitlines():
 h,name=line.split('  ',1); q=root/name
 assert q.is_file() and sha(q)==h,(name,h)
print('packet checks PASS; object binaries omitted; loop source/object provenance mismatch explicitly retained')
