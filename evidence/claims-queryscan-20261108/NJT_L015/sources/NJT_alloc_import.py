from pathlib import Path
import hashlib,json,difflib,base64,lzma
B=Path(__file__).resolve().parent;S=B/'NJT_src';n='programs/r1-cost-probe/src/lib.rs';p=S/n
pins=json.loads((B/'NJT_SOURCE_PINS.json').read_text());assert hashlib.sha256(p.read_bytes()).hexdigest()==pins[n]
s=p.read_text();needle='#[cfg(kani)] #[path="../../../KMX_stubs.rs"]';assert needle in s
s=s.replace(needle,'#[cfg(kani)] extern crate alloc;\n'+needle);p.write_text(s)
pins[n]=hashlib.sha256(p.read_bytes()).hexdigest();(B/'NJT_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
payload=json.loads(lzma.decompress((B/'NJT_FROZEN_PAYLOAD.json.xz').read_bytes()));patch=''
for n in ['crates/aspis-r1-cost-probe/src/r1_semantic.rs','programs/r1-cost-probe/src/lib.rs']:
 patch+=''.join(difflib.unified_diff(base64.b64decode(payload[n]).decode().splitlines(True),(S/n).read_text().splitlines(True),fromfile='a/'+n,tofile='b/'+n))
(B/'NJT_NATIVE.patch').write_text(patch)
print('NJT own harness imports alloc for exact KMX module')
