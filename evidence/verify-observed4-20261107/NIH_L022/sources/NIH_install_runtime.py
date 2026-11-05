from pathlib import Path
import hashlib,json,difflib
B=Path(__file__).resolve().parent;S=B/'NIH_src';q='crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs';p=S/q;old=p.read_text();assert 'mod NIH_runtime' not in old
hook='\n#[cfg(test)]\n#[path="NIH_runtime.rs"]\nmod NIH_runtime;\n';p.write_text(old+hook)
(B/'NIH_runtime.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),(old+hook).splitlines(True),fromfile='a/'+q,tofile='b/'+q)))
q2='crates/aspis-statement/src/pool_v1/NIH_runtime.rs';(S/q2).write_text((B/'NIH_runtime.rs.txt').read_text())
pins=json.loads((B/'NIH_SOURCE_PINS.json').read_text());frozen=json.loads((B/'NIH_FROZEN_FILE_PINS.json').read_text());frozen.pop(q,None)
for n in [q,q2]:pins[n]=hashlib.sha256((S/n).read_bytes()).hexdigest()
(B/'NIH_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n');(B/'NIH_FROZEN_FILE_PINS.json').write_text(json.dumps(frozen,indent=2)+'\n')
