from NEW_remote import *
import hashlib,difflib
assert not (E/'NEW_ACTIVE.json').exists()
R=E.parent.parent;a='NEW_GEOMETRY_INPUT';admit(a);rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
f='crates/aspis-r1-cost-probe/src/verifier.rs';old=subprocess.check_output(['git','show',rev+':'+f],cwd=R,text=True)
new=old+''.join('\n#[cfg(kani)]\nmod '+n+';\n' for n in ['NEW_geometry'])
files={'NEW_src/'+f:new};patch=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+f,tofile='b/'+f))
for name in ['NEW_geometry']:
 mod='crates/aspis-r1-cost-probe/src/verifier/'+name+'.rs';src=(E/(name+'.rs.txt')).read_text();files['NEW_src/'+mod]=src
 patch+=''.join(difflib.unified_diff([],src.splitlines(True),fromfile='/dev/null',tofile='b/'+mod))
files['NEW_src/crates/aspis-core/src/field/NEW_inverse.rs']=(E/'NEW_inverse.rs.txt').read_text()
(E/'NEW_GEOMETRY.patch').write_text(patch);upload(a,files)
r=ssh(a,'python3',f'''from pathlib import Path
import hashlib,json
b=Path({B!r});s=b/'NEW_src';pins={{str(p.relative_to(s)):hashlib.sha256(p.read_bytes()).hexdigest() for p in s.rglob('*') if p.is_file()}}
(b/'NEW_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\\n');print(json.dumps(pins))
''');assert r.returncode==0,r.stderr;(E/'NEW_SOURCE_PINS.json').write_text(r.stdout)
