from pathlib import Path
import json,hashlib,difflib
B=Path(__file__).resolve().parent;S=B/'NKD_src';p=S/'programs/r1-cost-probe/src/NKD_native.rs'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
x=json.loads((B/'NKD_SOURCE_PINS.json').read_text());assert sha(p)==x['programs/r1-cost-probe/src/NKD_native.rs']
p.write_bytes((B/'NKD_native_generated.rs.txt').read_bytes());x['programs/r1-cost-probe/src/NKD_native.rs']=sha(p)
(B/'NKD_SOURCE_PINS.json').write_text(json.dumps(x,indent=1)+'\n')
patch=(B/'NKD_harness.patch').read_text();start=patch.index('--- /dev/null\n');patch=patch[:start]+''.join(difflib.unified_diff([],p.read_text().splitlines(True),fromfile='/dev/null',tofile='b/programs/r1-cost-probe/src/NKD_native.rs'))
(B/'NKD_harness.patch').write_text(patch)
print('Own KMX include scope repaired with extern crate alloc; validation unchanged')
