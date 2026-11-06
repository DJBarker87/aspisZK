from pathlib import Path
import json,hashlib,difflib,base64,lzma
B=Path(__file__).resolve().parent;S=B/'NJM_src';n='programs/r1-cost-probe/src/lib.rs';p=S/n
s=p.read_text();assert '#[cfg(kani)] extern crate alloc;' not in s;p.write_text(s+'\n#[cfg(kani)] extern crate alloc;\n')
pins=json.loads((B/'NJM_SOURCE_PINS.json').read_text());pins[n]=hashlib.sha256(p.read_bytes()).hexdigest();(B/'NJM_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
payload=json.loads(lzma.decompress((B/'NJM_FROZEN_PAYLOAD.json.xz').read_bytes()));patch=''
for n in ['crates/aspis-r1-cost-probe/src/r1_semantic.rs','programs/r1-cost-probe/src/lib.rs']:
 patch+=''.join(difflib.unified_diff(base64.b64decode(payload[n]).decode().splitlines(True),(S/n).read_text().splitlines(True),fromfile='a/'+n,tofile='b/'+n))
(B/'NJM_NATIVE.patch').write_text(patch)
print('NJM cfg(kani)-only alloc declaration installed for exact KMX module')
