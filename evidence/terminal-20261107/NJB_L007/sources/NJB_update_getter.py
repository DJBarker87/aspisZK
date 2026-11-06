from pathlib import Path
import json,hashlib,lzma,base64
b=Path(__file__).resolve().parent;s=b/'NJB_src';x=json.loads((b/'NJB_PATCH_FILES.json').read_text());data=json.loads(lzma.decompress((b/'NHR_FROZEN_PAYLOAD.json.xz').read_bytes()));pins=json.loads((b/'NJB_SOURCE_PINS.json').read_text())
for q,r in x.items():
 raw=r.get('prepend','').encode()+base64.b64decode(data[q])+r['append'].encode();assert hashlib.sha256(raw).hexdigest()==r['after_sha256'];(s/q).write_bytes(raw);pins[q]=r['after_sha256']
q='crates/aspis-statement/src/pool_v1/NJB_terminal.rs';raw=(b/'NJB_terminal.rs.txt').read_bytes();(s/q).write_bytes(raw);pins[q]=hashlib.sha256(raw).hexdigest();(b/'NJB_SOURCE_PINS.json').write_text(json.dumps(pins));print('all-bit-valid M31 generators and cfg-only allocator feature repaired')
