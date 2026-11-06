from pathlib import Path
import hashlib,json
E=Path(__file__).resolve().parent
p=E/'NKK_NATIVE_INPUTS.json';x=json.loads(p.read_text());x['crates/aspis-r1-cost-probe/src/NKK_parent.rs']=(E/'NKK_parent.rs').read_text();p.write_text(json.dumps(x))
p=E/'NKK_SOURCE_PINS.json';pins=json.loads(p.read_text());pins.update({n:hashlib.sha256(t.encode()).hexdigest() for n,t in x.items()});p.write_text(json.dumps(pins,indent=2))
