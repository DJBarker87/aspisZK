from NET_remote import *
import hashlib,difflib
R=E.parent.parent;a='NET_WINDOW_INPUT';admit(a)
f='crates/aspis-core/src/field.rs';rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
old=subprocess.check_output(['git','show',rev+':'+f],cwd=R,text=True)
new=old+'\n#[cfg(kani)]\nmod NET_inverse;\n#[cfg(kani)]\nmod NET_qinverse;\n#[cfg(kani)]\nmod NET_windows;\n'
module='crates/aspis-core/src/field/NET_windows.rs';src=(E/'NET_windows.rs.txt').read_text()
patch=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+f,tofile='b/'+f))+''.join(difflib.unified_diff([],src.splitlines(True),fromfile='/dev/null',tofile='b/'+module))
(E/'NET_WINDOWS.patch').write_text(patch)
ref='crates/aspis-core/src/field/NET_window_reference.rs'
reference=(E/'NET_window_reference.rs').read_text()
patch+=''.join(difflib.unified_diff([],reference.splitlines(True),fromfile='/dev/null',tofile='b/'+ref))
(E/'NET_WINDOWS.patch').write_text(patch)
upload(a,{'NET_src/'+f:new,'NET_src/'+module:src,'NET_src/'+ref:reference})
r=ssh(a,'python3',f'''from pathlib import Path
import hashlib,json
b=Path({B!r});s=b/'NET_src';pins={{str(p.relative_to(s)):hashlib.sha256(p.read_bytes()).hexdigest() for p in s.rglob('*') if p.is_file()}}
(b/'NET_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\\n');print(json.dumps(pins))
''');assert r.returncode==0,r.stderr
(E/'NET_SOURCE_PINS.json').write_text(r.stdout);print('Complete physical caller-window input uploaded; no composed claim')
