from pathlib import Path
import json,hashlib
b=Path(__file__).resolve().parent;s=b/'NJB_src';pins=json.loads((b/'NJB_SOURCE_PINS.json').read_text());q='crates/aspis-statement/src/pool_v1/NJB_active.rs';p=s/q;assert hashlib.sha256(p.read_bytes()).hexdigest()==pins[q];raw=(b/'NJB_active.rs.txt').read_bytes();p.write_bytes(raw);pins[q]=hashlib.sha256(raw).hexdigest();(b/'NJB_SOURCE_PINS.json').write_text(json.dumps(pins));print('active harness initialization split; native step name/body unchanged')
