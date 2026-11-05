from pathlib import Path
import json,hashlib,difflib
B=Path(__file__).resolve().parent;S=B/'NIH_src';q='crates/aspis-statement/src/state_only_poseidon.rs';p=S/q;old=p.read_text();assert 'mod NDE_native' not in old
hook='\n#[cfg(kani)]\n#[path="NIH_NDE_poseidon.rs"]\nmod NDE_native;\n';p.write_text(old+hook)
(B/'NIH_packed.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),(old+hook).splitlines(True),fromfile='a/'+q,tofile='b/'+q)))
pins=json.loads((B/'NIH_SOURCE_PINS.json').read_text());frozen=json.loads((B/'NIH_FROZEN_FILE_PINS.json').read_text());frozen.pop(q,None);pins[q]=hashlib.sha256(p.read_bytes()).hexdigest()
for dst,src in [('crates/aspis-statement/src/NIH_NDE_poseidon.rs','NIH_NDE_poseidon.rs.txt'),('crates/aspis-statement/src/NIH_NDE_reference.rs','NIH_NDE_reference.rs.txt')]:
 p=S/dst;p.write_text((B/src).read_text());pins[dst]=hashlib.sha256(p.read_bytes()).hexdigest()
(B/'NIH_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n');(B/'NIH_FROZEN_FILE_PINS.json').write_text(json.dumps(frozen,indent=2)+'\n')
