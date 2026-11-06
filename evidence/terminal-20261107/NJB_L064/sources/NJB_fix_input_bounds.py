from pathlib import Path
import json,hashlib
b=Path(__file__).resolve().parent;s=b/'NJB_src';pins=json.loads((b/'NJB_SOURCE_PINS.json').read_text())
for q,n in [('crates/aspis-statement/src/pool_v1/NJB_absorption.rs','NJB_absorption.rs.txt'),('crates/aspis-statement/src/pool_v1/NJB_pattern.rs','NJB_pattern.rs.txt')]:
 p=s/q;assert hashlib.sha256(p.read_bytes()).hexdigest()==pins[q];p.write_bytes((b/n).read_bytes());pins[q]=hashlib.sha256(p.read_bytes()).hexdigest()
(b/'NJB_SOURCE_PINS.json').write_text(json.dumps(pins));print('exact fixed-array arbitrary-input initialization bounds repaired; no timeout or memory cap change')
