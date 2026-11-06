from pathlib import Path
import json,hashlib,difflib,base64,lzma
B=Path(__file__).resolve().parent;S=B/'NKA_src';pins=json.loads((B/'NKA_SOURCE_PINS.json').read_text());frozen=json.loads((B/'NKA_FROZEN_FILE_PINS.json').read_text())
for n in ['crates/aspis-core/src/lib.rs','crates/aspis-core/src/r0_transcript.rs']:
 p=S/n;assert hashlib.sha256(p.read_bytes()).hexdigest()==frozen[n];old=p.read_text()
 p.write_text('#![cfg_attr(kani, feature(allocator_api))]\n'+old+'\n#[cfg(kani)] #[path="../../../KMX_stubs.rs"] mod NKA_kmx;\n' if n.endswith('/lib.rs') else old+'\n'+(B/'NKA_pairs_cut.rs.txt').read_text())
 pins[n]=hashlib.sha256(p.read_bytes()).hexdigest();del frozen[n]
(B/'NKA_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2));(B/'NKA_FROZEN_FILE_PINS.json').write_text(json.dumps(frozen,indent=2))
payload=json.loads(lzma.decompress((B/'NKA_FROZEN_PAYLOAD.json.xz').read_bytes()));patch=''
for n in sorted(pins):
 if n not in payload:continue
 old=base64.b64decode(payload[n]).decode();patch+=''.join(difflib.unified_diff(old.splitlines(True),(S/n).read_text().splitlines(True),fromfile='a/'+n,tofile='b/'+n))
(B/'NKA_NATIVE.patch').write_text(patch)
print('NKA full-footprint local-record one outer iteration and derived-default controls installed')
