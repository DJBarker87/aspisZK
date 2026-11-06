from pathlib import Path
import json,hashlib
B=Path(__file__).resolve().parent;S=B/'NIX_src';pins=json.loads((B/'NIX_SOURCE_PINS.json').read_text())
for n,tag,source in [('crates/aspis-core/src/circle.rs','#[cfg(kani)]\nmod NIX_circle','NIX_circle.rs.txt'),('crates/aspis-r1-cost-probe/src/r1_wire.rs','#[cfg(kani)]\npub mod NIX_circle_validated','NIX_validated.rs.txt')]:
 p=S/n;s=p.read_text();p.write_text(s[:s.index(tag)]+(B/source).read_text());pins[n]=hashlib.sha256(p.read_bytes()).hexdigest()
(B/'NIX_SOURCE_PINS.json').write_text(json.dumps(pins));print('NIX complete mutable-log frames and validated child pre-state observations installed')
