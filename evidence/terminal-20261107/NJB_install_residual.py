from pathlib import Path
import json,hashlib
b=Path(__file__).resolve().parent;s=b/'NJB_src';pins=json.loads((b/'NJB_SOURCE_PINS.json').read_text());q='crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs';p=s/q
assert hashlib.sha256(p.read_bytes()).hexdigest()==json.loads((b/'NJB_FROZEN_FILE_PINS.json').read_text())[q]
p.write_text(p.read_text()+'\n#[cfg(kani)]\n#[path="NJB_residual.rs"]\nmod NJB_native;\n');pins[q]=hashlib.sha256(p.read_bytes()).hexdigest();q='crates/aspis-statement/src/pool_v1/NJB_residual.rs';(s/q).write_bytes((b/'NJB_residual.rs.txt').read_bytes());pins[q]=hashlib.sha256((s/q).read_bytes()).hexdigest();(b/'NJB_SOURCE_PINS.json').write_text(json.dumps(pins));print('residual local-record cut installed; 17 ordered opaque operations')
