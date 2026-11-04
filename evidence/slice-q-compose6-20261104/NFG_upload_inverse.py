from NFG_remote import *
import hashlib
assert not (E/'NFG_ACTIVE.json').exists()
a='NFG_UPLOAD_'+hashlib.sha256((E/'NFG_inverse.rs.txt').read_bytes()).hexdigest()[:12];admit(a)
upload(a,{'NFG_inverse.rs.txt':(E/'NFG_inverse.rs.txt').read_text()})
r=ssh(a,'python3',f'''from pathlib import Path
import json,hashlib
b=Path({B!r});s=b/'NFG_src';p=s/'crates/aspis-r1-cost-probe/src/verifier/NFG_inverse.rs';p.write_bytes((b/'NFG_inverse.rs.txt').read_bytes())
pins=json.loads((b/'NFG_SOURCE_PINS.json').read_text());pins[str(p.relative_to(s))]=hashlib.sha256(p.read_bytes()).hexdigest();(b/'NFG_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+chr(10));print(json.dumps(pins))
''');assert r.returncode==0,r.stderr
(E/'NFG_SOURCE_PINS.json').write_text(r.stdout)
