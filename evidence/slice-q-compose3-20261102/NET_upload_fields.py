from NET_remote import *
import hashlib,difflib
R=E.parent.parent;a='NET_FIELD_INPUT';admit(a)
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
f='crates/aspis-r1-cost-probe/src/verifier.rs';l='crates/aspis-r1-cost-probe/src/lib.rs'
old={n:subprocess.check_output(['git','show',rev+':'+n],cwd=R,text=True) for n in [f,l]}
new={f:old[f]+'\n#[cfg(kani)]\nmod NET_fields;\n',l:old[l].replace('#![no_std]','#![no_std]\n#![cfg_attr(kani,feature(allocator_api))]'),'crates/aspis-r1-cost-probe/src/verifier/NET_fields.rs':(E/'NET_fields.rs.txt').read_text(),'crates/aspis-r1-cost-probe/src/NET_window_reference.rs':(E/'NET_window_reference.rs').read_text()}
patch=''.join(''.join(difflib.unified_diff(old.get(n,'').splitlines(True),v.splitlines(True),fromfile='a/'+n if n in old else '/dev/null',tofile='b/'+n)) for n,v in new.items())
(E/'NET_FIELDS.patch').write_text(patch)
upload(a,{'NET_src/'+n:v for n,v in new.items()})
r=ssh(a,'python3',f'''from pathlib import Path
import hashlib,json
b=Path({B!r});s=b/'NET_src';pins={{str(p.relative_to(s)):hashlib.sha256(p.read_bytes()).hexdigest() for p in s.rglob('*') if p.is_file()}}
(b/'NET_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\\n');print(json.dumps(pins))
''');assert r.returncode==0,r.stderr
(E/'NET_SOURCE_PINS.json').write_text(r.stdout);print('Uploaded actual weights::field caller contexts')
