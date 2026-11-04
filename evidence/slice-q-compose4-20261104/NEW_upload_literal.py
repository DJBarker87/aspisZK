from NEW_remote import *
import hashlib,difflib
assert not (E/'NEW_ACTIVE.json').exists()
a='NEW_LITERAL_INPUT';admit(a)
base=(E/'NEW_geometry.rs.txt').read_text();append=(E/'NEW_geometry_literal.rs.txt').read_text();assert 'fn NEW_shift_literal' not in base
new=base+append;upload(a,{'NEW_src/crates/aspis-r1-cost-probe/src/verifier/NEW_geometry.rs':new})
(E/'NEW_geometry.rs.txt').write_text(new)
(E/'NEW_LITERAL_NATIVE.patch').write_text(''.join(difflib.unified_diff(base.splitlines(True),new.splitlines(True),fromfile='a/crates/aspis-r1-cost-probe/src/verifier/NEW_geometry.rs',tofile='b/crates/aspis-r1-cost-probe/src/verifier/NEW_geometry.rs')))
r=ssh(a,'python3',f'''from pathlib import Path
import hashlib,json
b=Path({B!r});s=b/'NEW_src';pins={{str(p.relative_to(s)):hashlib.sha256(p.read_bytes()).hexdigest() for p in s.rglob('*') if p.is_file()}}
(b/'NEW_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\\n');print(json.dumps(pins))
''');assert r.returncode==0,r.stderr;(E/'NEW_SOURCE_PINS.json').write_text(r.stdout)
