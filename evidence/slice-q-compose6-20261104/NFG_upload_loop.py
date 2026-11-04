from NFG_remote import *
import hashlib,subprocess
assert not (E/'NFG_ACTIVE.json').exists()
a='NFG_UPLOAD_LOOP';admit(a)
frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-r1-cost-probe/src/candidate.rs'],cwd=E.parent.parent,text=True)
files={'NFG_src/crates/aspis-r1-cost-probe/src/candidate.rs':frozen+'\n#[cfg(kani)] #[path="NFG_loop.rs"] mod NFG_loop;\n',
'NFG_src/crates/aspis-r1-cost-probe/src/NFG_loop.rs':(E/'NFG_loop.rs.txt').read_text()}
upload(a,files)
r=ssh(a,'python3',f'''from pathlib import Path
import json,hashlib
b=Path({B!r});s=b/'NFG_src';pins=json.loads((b/'NFG_SOURCE_PINS.json').read_text())
for n in {list(files)!r}:
 p=b/n;pins[str(p.relative_to(s))]=hashlib.sha256(p.read_bytes()).hexdigest()
(b/'NFG_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\\n');print(json.dumps(pins))
''');assert r.returncode==0,r.stderr
(E/'NFG_SOURCE_PINS.json').write_text(r.stdout)
