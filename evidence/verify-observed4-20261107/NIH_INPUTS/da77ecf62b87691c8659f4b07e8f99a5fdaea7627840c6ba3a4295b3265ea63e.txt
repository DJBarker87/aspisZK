from pathlib import Path
import json,hashlib
B=Path(__file__).resolve().parent;S=B/'NIH_src';q='crates/aspis-statement/src/pool_v1/NIH_copy.rs';p=S/q;p.write_text((B/'NIH_copy.rs.txt').read_text());pins=json.loads((B/'NIH_SOURCE_PINS.json').read_text());pins[q]=hashlib.sha256(p.read_bytes()).hexdigest();(B/'NIH_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
