from NEO_remote import *
import hashlib,difflib
R=E.parent.parent;a='NEO_GEOMETRY_INPUT';admit(a)
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';v='crates/aspis-r1-cost-probe/src/verifier.rs';lib='crates/aspis-r1-cost-probe/src/lib.rs'
old={n:subprocess.check_output(['git','show',rev+':'+n],cwd=R,text=True) for n in [v,lib]}
new={v:old[v]+'\n#[cfg(kani)]\nmod NEO_geometry;\n',lib:old[lib].replace('#![no_std]','#![no_std]\n#![cfg_attr(kani,feature(allocator_api))]'),'crates/aspis-r1-cost-probe/src/verifier/NEO_geometry.rs':(E/'NEO_geometry.rs.txt').read_text(),'crates/aspis-r1-cost-probe/src/NEO_getter_reference.rs':(E/'NEO_getter_reference.rs').read_text(),'crates/aspis-r1-cost-probe/src/NEO_cell_reference.rs':(E/'NEO_cell_reference.rs').read_text()}
patch=''.join(''.join(difflib.unified_diff(old.get(n,'').splitlines(True),s.splitlines(True),fromfile='a/'+n if n in old else '/dev/null',tofile='b/'+n)) for n,s in new.items());(E/'NEO_GEOMETRY.patch').write_text(patch)
upload(a,{'NEO_src/'+n:s for n,s in new.items()})
r=ssh(a,'python3',f'''from pathlib import Path
import json,hashlib
b=Path({B!r});s=b/'NEO_src';pins={{str(p.relative_to(s)):hashlib.sha256(p.read_bytes()).hexdigest() for p in s.rglob('*') if p.is_file()}}
(b/'NEO_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\\n');print(json.dumps(pins))
''');assert r.returncode==0,r.stderr
(E/'NEO_SOURCE_PINS.json').write_text(r.stdout)
