from pathlib import Path
import json,hashlib
b=Path.cwd();s=b/'NJB_src';pins=json.loads((b/'NJB_SOURCE_PINS.json').read_text());q='crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs';p=s/q;assert hashlib.sha256(p.read_bytes()).hexdigest()==pins[q];p.write_text(p.read_text()+'\n#[cfg(kani)]\n#[path="NJB_factored.rs"]\nmod NJB_factored_native;\n');pins[q]=hashlib.sha256(p.read_bytes()).hexdigest()
for q,n in [('crates/aspis-statement/src/pool_v1/NJB_factored.rs','NJB_factored.rs.txt'),('crates/aspis-statement/src/pool_v1/NJB_endpoint.rs','NJB_endpoint.rs.txt')]:
 p=s/q
 if q in pins:assert hashlib.sha256(p.read_bytes()).hexdigest()==pins[q]
 p.write_bytes((b/n).read_bytes());pins[q]=hashlib.sha256(p.read_bytes()).hexdigest()
(b/'NJB_SOURCE_PINS.json').write_text(json.dumps(pins));print('independent path/occupancy and split endpoint windows installed')
