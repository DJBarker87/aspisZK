from pathlib import Path
import json,hashlib
b=Path(__file__).resolve().parent;s=b/'NJB_src';pins=json.loads((b/'NJB_SOURCE_PINS.json').read_text());f=json.loads((b/'NJB_FROZEN_FILE_PINS.json').read_text());q='crates/aspis-core/src/field.rs';p=s/q;assert hashlib.sha256(p.read_bytes()).hexdigest()==f[q];p.write_text(p.read_text()+'\n#[cfg(kani)]\npub mod NJB_observe { include!("NJB_observe.rs"); }\n');pins[q]=hashlib.sha256(p.read_bytes()).hexdigest()
for q,n in [('crates/aspis-core/src/NJB_observe.rs','NJB_observe.rs.txt'),('crates/aspis-statement/src/pool_v1/NJB_absorption.rs','NJB_absorption.rs.txt')]:
 p=s/q
 if q in pins:assert hashlib.sha256(p.read_bytes()).hexdigest()==pins[q]
 raw=(b/n).read_bytes();p.write_bytes(raw);pins[q]=hashlib.sha256(raw).hexdigest()
(b/'NJB_SOURCE_PINS.json').write_text(json.dumps(pins));print('actual nine-word prepared carriers installed; earlier token windows excluded from native credit')
