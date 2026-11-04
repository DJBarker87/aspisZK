from NFB_remote import *
import hashlib,json
assert not (E/'NFB_ACTIVE.json').exists()
a='NFB_GEOMETRY_INPUT';admit(a)
upload(a,{'NFB_src/crates/aspis-r1-cost-probe/src/verifier/NFB_geometry.rs':(E/'NFB_geometry.rs.txt').read_text()})
r=ssh(a,'python3',f'''from pathlib import Path
import hashlib,json
b=Path({B!r});s=b/'NFB_src';pins={{str(p.relative_to(s)):hashlib.sha256(p.read_bytes()).hexdigest() for p in s.rglob('*') if p.is_file()}}
(b/'NFB_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\\n');print(json.dumps(pins))
''');assert r.returncode==0,r.stderr;(E/'NFB_SOURCE_PINS.json').write_text(r.stdout)
