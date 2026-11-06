from pathlib import Path
import json,hashlib
b=Path(__file__).resolve().parent;p=b/'NJB_src/crates/aspis-statement/src/pool_v1/NJB_forward.rs';pins=json.loads((b/'NJB_SOURCE_PINS.json').read_text());q='crates/aspis-statement/src/pool_v1/NJB_forward.rs';assert hashlib.sha256(p.read_bytes()).hexdigest()==pins[q];p.write_bytes((b/'NJB_forward.rs.txt').read_bytes());pins[q]=hashlib.sha256(p.read_bytes()).hexdigest();(b/'NJB_SOURCE_PINS.json').write_text(json.dumps(pins));print('exact80-element arbitrary-input initialization bound corrected; native function has no loop')
