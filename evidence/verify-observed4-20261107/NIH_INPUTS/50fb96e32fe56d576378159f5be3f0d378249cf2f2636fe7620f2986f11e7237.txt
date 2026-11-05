from pathlib import Path
import json,hashlib
B=Path(__file__).resolve().parent;S=B/'NIH_src';pins=json.loads((B/'NIH_SOURCE_PINS.json').read_text())
for q,n in [('crates/aspis-statement/src/pool_v1/NIH_copy.rs','NIH_copy.rs.txt'),('crates/aspis-statement/src/NIH_internal.rs','NIH_internal.rs.txt')]:
 p=S/q;p.write_text((B/n).read_text());pins[q]=hashlib.sha256(p.read_bytes()).hexdigest()
(B/'NIH_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
