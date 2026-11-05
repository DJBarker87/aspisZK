from pathlib import Path
import json,hashlib,difflib
B=Path(__file__).resolve().parent;S=B/'NIX_src';pins=json.loads((B/'NIX_SOURCE_PINS.json').read_text());frozen=json.loads((B/'NIX_FROZEN_FILE_PINS.json').read_text())
patch=[]
for n,addition in [('crates/aspis-core/src/circle.rs','NIX_circle.rs.txt'),('crates/aspis-core/src/r0/heap.rs','NIX_heap_claims.rs.txt')]:
 p=S/n;old=p.read_text();p.write_text(old+'\n'+(B/addition).read_text());pins[n]=hashlib.sha256(p.read_bytes()).hexdigest();frozen.pop(n,None)
 patch.extend(difflib.unified_diff(old.splitlines(True),p.read_text().splitlines(True),fromfile='a/'+n,tofile='b/'+n))
n='crates/aspis-core/src/field.rs';p=S/n;old=p.read_text();new=old
for name in ['M31','CM31','QM31']:new=new.replace('pub struct '+name,'#[cfg_attr(kani, derive(kani::Arbitrary))]\npub struct '+name)
p.write_text(new);pins[n]=hashlib.sha256(p.read_bytes()).hexdigest();frozen.pop(n,None)
patch.extend(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+n,tofile='b/'+n))
(B/'NIX_PACKET_INSTALL.patch').write_text(''.join(patch));(B/'NIX_SOURCE_PINS.json').write_text(json.dumps(pins));(B/'NIX_FROZEN_FILE_PINS.json').write_text(json.dumps(frozen));print('NIX packet harnesses installed')
