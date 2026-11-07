from pathlib import Path
import hashlib,json,lzma,base64,difflib
B=Path.cwd();S=B/'NMX_src';p=S/'programs/r1-cost-probe/src/NMX_217_native.rs'
p=S/'programs/r1-cost-probe/src/NMX_217_native.rs'
assert hashlib.sha256(p.read_bytes()).hexdigest()=='9c45ca85d453289757aec1210d9265018b477a86d98387fed8803e095b807f58'
p.write_text(p.read_text()+'\n'+(B/'NMX_217_guard_extra.rs').read_text())
payload=json.loads(lzma.decompress((B/'NMX_FROZEN_PAYLOAD.json.xz').read_bytes()));diffs=[]
for rel in ['programs/r1-cost-probe/src/lib.rs','programs/r1-cost-probe/src/r1_pool_adapter.rs']:
 original=base64.b64decode(payload[rel]).decode();diffs.extend(difflib.unified_diff(original.splitlines(True),(S/rel).read_text().splitlines(True),fromfile='a/'+rel,tofile='b/'+rel))
for name in ['NMX_217_native.rs','NMX_217_reference.rs','NMX_217_fidelity.rs']:
 rel='programs/r1-cost-probe/src/'+name;diffs.extend(difflib.unified_diff([], (S/rel).read_text().splitlines(True),fromfile='/dev/null',tofile='b/'+rel))
(B/'NMX_217_harness.patch').write_text(''.join(diffs));print('Prepared all-usize first-guard cut; actual decoder body unchanged')
