from pathlib import Path
import json,hashlib,difflib
B=Path(__file__).resolve().parent;S=B/'NIH_src';q='crates/aspis-statement/src/state_only_poseidon.rs';p=S/q;old=p.read_text();assert 'mod NIH_local_native' not in old
hook='\n#[cfg(kani)]\n#[path="NIH_local_packed.rs"]\nmod NIH_local_native;\n';p.write_text(old+hook)
(B/'NIH_local.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),(old+hook).splitlines(True),fromfile='a/'+q,tofile='b/'+q)))
pins=json.loads((B/'NIH_SOURCE_PINS.json').read_text());pins[q]=hashlib.sha256(p.read_bytes()).hexdigest()
q='crates/aspis-statement/src/NIH_local_packed.rs';p=S/q;p.write_text((B/'NIH_local_packed.rs.txt').read_text());pins[q]=hashlib.sha256(p.read_bytes()).hexdigest()
(B/'NIH_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
