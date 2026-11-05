from pathlib import Path
import json,hashlib
B=Path(__file__).resolve().parent;S=B/'NIX_src';pins=json.loads((B/'NIX_SOURCE_PINS.json').read_text())
for n,tag,source in [('crates/aspis-r1-cost-probe/src/sampler.rs','#[cfg(kani)]\npub mod NIX_sampler','NIX_sampler.rs.txt'),('crates/aspis-r1-cost-probe/src/r1_wire.rs','#[cfg(kani)]\npub mod NIX_circle_validated','NIX_validated.rs.txt'),('programs/r1-cost-probe/src/lib.rs','#[cfg(kani)]\nmod NIX_validated_program','NIX_validated_program.rs.txt')]:
 p=S/n;s=p.read_text();suffix=''
 if n.startswith('programs/'):
  suffix='\n#[cfg(kani)] extern crate alloc;\n#[cfg(kani)] #[path="../../../KMX_stubs.rs"] mod NIX_kmx;\n'
 p.write_text(s[:s.index(tag)]+(B/source).read_text()+suffix);pins[n]=hashlib.sha256(p.read_bytes()).hexdigest()
(B/'NIX_SOURCE_PINS.json').write_text(json.dumps(pins));print('NIX full caller assertions and explicit matched controls installed with reusable identical compiler flags')
