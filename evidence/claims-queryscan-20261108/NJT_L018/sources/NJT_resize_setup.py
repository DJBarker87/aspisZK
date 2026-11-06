from pathlib import Path
import hashlib,json,difflib,base64,lzma
B=Path(__file__).resolve().parent;S=B/'NJT_src';n='programs/r1-cost-probe/src/lib.rs';p=S/n
pins=json.loads((B/'NJT_SOURCE_PINS.json').read_text());assert hashlib.sha256(p.read_bytes()).hexdigest()==pins[n]
for n,source in [('crates/aspis-r1-cost-probe/src/r1_semantic.rs','NJT_resize_window.rs.txt'),('programs/r1-cost-probe/src/lib.rs','NJT_resize_program.rs.txt')]:
 p=S/n;assert hashlib.sha256(p.read_bytes()).hexdigest()==pins[n];p.write_text(p.read_text()+'\n'+(B/source).read_text());pins[n]=hashlib.sha256(p.read_bytes()).hexdigest()
pins[n]=hashlib.sha256(p.read_bytes()).hexdigest();(B/'NJT_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
payload=json.loads(lzma.decompress((B/'NJT_FROZEN_PAYLOAD.json.xz').read_bytes()));patch=''
for n in ['crates/aspis-r1-cost-probe/src/r1_semantic.rs','programs/r1-cost-probe/src/lib.rs']:
 patch+=''.join(difflib.unified_diff(base64.b64decode(payload[n]).decode().splitlines(True),(S/n).read_text().splitlines(True),fromfile='a/'+n,tofile='b/'+n))
(B/'NJT_NATIVE.patch').write_text(patch)
print('NJT safe-resize one-iteration data cut installed')
