from pathlib import Path
import json,hashlib,lzma,base64,difflib
B=Path(__file__).resolve().parent;S=B/'NKQ_src';pins=json.loads((B/'NKQ_SOURCE_PINS.json').read_text());frozen=json.loads((B/'NKQ_FROZEN_FILE_PINS.json').read_text());n='crates/aspis-r1-cost-probe/src/lib.rs';p=S/n
assert hashlib.sha256(p.read_bytes()).hexdigest()==frozen[n]
p.write_text('#![cfg_attr(kani, feature(allocator_api))]\n'+p.read_text());pins[n]=hashlib.sha256(p.read_bytes()).hexdigest();del frozen[n]
(B/'NKQ_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2));(B/'NKQ_FROZEN_FILE_PINS.json').write_text(json.dumps(frozen,indent=2))
payload=json.loads(lzma.decompress((B/'NKQ_FROZEN_PAYLOAD.json.xz').read_bytes()));patch=''
for n in pins:
 if n.startswith('KMX'):continue
 old=base64.b64decode(payload[n]).decode() if n in payload else ''
 patch+=''.join(difflib.unified_diff(old.splitlines(True),(S/n).read_text().splitlines(True),fromfile='a/'+n if n in payload else '/dev/null',tofile='b/'+n))
(B/'NKQ_NATIVE.patch').write_text(patch);print('Enable allocator_api only under cfg(kani), as required by exact KMX patch')
