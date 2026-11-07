from pathlib import Path
import hashlib,json,lzma,base64,difflib
B=Path.cwd();S=B/'NMX_src';p=S/'programs/r1-cost-probe/src/NMX_217_native.rs'
assert hashlib.sha256(p.read_bytes()).hexdigest()=='0c53473cbbd1c0865eb49446b886361469ce37fedd6fc347e31fc1ba3e0b7dd3'
p.write_text(p.read_text()+'\n#[path="NMX_217_fidelity.rs"] mod fidelity;\n')
(S/'programs/r1-cost-probe/src/NMX_217_fidelity.rs').write_bytes((B/'NMX_217_fidelity.rs').read_bytes())
payload=json.loads(lzma.decompress((B/'NMX_FROZEN_PAYLOAD.json.xz').read_bytes()));diffs=[]
for rel in ['programs/r1-cost-probe/src/lib.rs','programs/r1-cost-probe/src/r1_pool_adapter.rs']:
 original=base64.b64decode(payload[rel]).decode();diffs.extend(difflib.unified_diff(original.splitlines(True),(S/rel).read_text().splitlines(True),fromfile='a/'+rel,tofile='b/'+rel))
for name in ['NMX_217_native.rs','NMX_217_reference.rs','NMX_217_fidelity.rs']:
 rel='programs/r1-cost-probe/src/'+name;diffs.extend(difflib.unified_diff([], (S/rel).read_text().splitlines(True),fromfile='/dev/null',tofile='b/'+rel))
(B/'NMX_217_harness.patch').write_text(''.join(diffs));print('Added typed interface fidelity controls; actual decoder body unchanged')
