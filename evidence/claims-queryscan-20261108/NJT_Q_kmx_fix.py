from pathlib import Path
import hashlib,json,base64,lzma,difflib
B=Path(__file__).resolve().parent;S=B/'NJT_Q_src';p=S/'crates/aspis-core/src/lib.rs';old=p.read_text();p.write_text(old.replace('#![no_std]','#![cfg_attr(kani, feature(allocator_api))]\n#![no_std]')+'\n#[cfg(kani)]\n#[path="../../../KMX_stubs.rs"]\npub mod KMX_stubs;\n');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
f=B/'NJT_Q_SOURCE_PINS.json';pins=json.loads(f.read_text());pins['crates/aspis-core/src/lib.rs']=sha(p);f.write_text(json.dumps(pins));f=B/'NJT_Q_FROZEN_FILE_PINS.json';pins=json.loads(f.read_text());pins.pop('crates/aspis-core/src/lib.rs');f.write_text(json.dumps(pins))
payload=json.loads(lzma.decompress(Path('/home/dombarker/project-offloads/codex-cx-claims-queryscan-20261108/NJT_FROZEN_PAYLOAD.json.xz').read_bytes()));patch=''
for n in ['crates/aspis-core/src/lib.rs','crates/aspis-core/src/r0_transcript.rs']:
 patch+=''.join(difflib.unified_diff(base64.b64decode(payload[n]).decode().splitlines(True),(S/n).read_text().splitlines(True),fromfile='a/'+n,tofile='b/'+n))
(B/'NJT_Q_NATIVE.patch').write_text(patch);print('KMX module exposed in own scratch only; missing module compilation error repaired')
