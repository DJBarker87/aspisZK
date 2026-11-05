from pathlib import Path
import hashlib,json
B=Path(__file__).resolve().parent;p=B/'NIX_src/crates/aspis-core/src/lib.rs'
p.write_text('#![cfg_attr(kani, feature(allocator_api))]\n'+p.read_text())
x=json.loads((B/'NIX_SOURCE_PINS.json').read_text());x['crates/aspis-core/src/lib.rs']=hashlib.sha256(p.read_bytes()).hexdigest();(B/'NIX_SOURCE_PINS.json').write_text(json.dumps(x))
print('NIX KMX allocator_api input repaired')
