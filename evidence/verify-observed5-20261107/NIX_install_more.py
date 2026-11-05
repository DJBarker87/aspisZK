from pathlib import Path
import json,hashlib
B=Path(__file__).resolve().parent;pins=json.loads((B/'NIX_SOURCE_PINS.json').read_text())
for tail,src in [('pair_forest_copy_terminal.rs','NIX_more_copy.rs.txt'),('pair_forest_semantic_terminal.rs','NIX_more_semantic.rs.txt')]:
 n='crates/aspis-statement/src/pool_v1/'+tail;p=B/'NIX_src'/n;s=p.read_text();p.write_text(s+(B/src).read_text());pins[n]=hashlib.sha256(p.read_bytes()).hexdigest()
(B/'NIX_SOURCE_PINS.json').write_text(json.dumps(pins));print('Independent one-iteration and boundary stages installed; no field multiplication executed; local stages are not composed-row credit')
