from pathlib import Path
import json,hashlib,lzma,base64,difflib
B=Path(__file__).resolve().parent;S=B/'NKQ_src';pins=json.loads((B/'NKQ_SOURCE_PINS.json').read_text());payload=json.loads(lzma.decompress((B/'NKQ_FROZEN_PAYLOAD.json.xz').read_bytes()))
n='crates/aspis-r1-cost-probe/src/r1_semantic.rs';p=S/n
assert hashlib.sha256(p.read_bytes()).hexdigest()==pins[n]
p.write_bytes(base64.b64decode(payload[n])+b'\n#[cfg(kani)]\n#[path="NKQ_rejections.rs"]\nmod NKQ_rejections;\n')
q=p.with_name('NKQ_rejections.rs');assert hashlib.sha256(q.read_bytes()).hexdigest()==pins[str(q.relative_to(S))];q.write_text((B/'NKQ_rejections.rs.txt').read_text())
for f in [p,q]:pins[str(f.relative_to(S))]=hashlib.sha256(f.read_bytes()).hexdigest()
(B/'NKQ_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2))
patch=''
for n in [str(p.relative_to(S)),str(q.relative_to(S))]:
 old=base64.b64decode(payload[n]).decode() if n in payload else ''
 patch+=''.join(difflib.unified_diff(old.splitlines(True),(S/n).read_text().splitlines(True),fromfile='a/'+n if n in payload else '/dev/null',tofile='b/'+n))
(B/'NKQ_NATIVE.patch').write_text(patch);print('Own cfg-only module path/harness repaired; frozen bodies retained')
