from NET_remote import *
import hashlib,difflib
R=E.parent.parent;a='NET_PREFIX_INPUT';admit(a);rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
f='crates/aspis-r1-cost-probe/src/verifier.rs';old=subprocess.check_output(['git','show',rev+':'+f],cwd=R,text=True)
new=old+'\n#[cfg(kani)]\nmod NET_fields;\n#[cfg(kani)]\nmod NET_prefix;\n'
mod='crates/aspis-r1-cost-probe/src/verifier/NET_prefix.rs';src=(E/'NET_prefix.rs.txt').read_text()
patch=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+f,tofile='b/'+f))+''.join(difflib.unified_diff([],src.splitlines(True),fromfile='/dev/null',tofile='b/'+mod))
(E/'NET_PREFIX.patch').write_text(patch);upload(a,{'NET_src/'+f:new,'NET_src/'+mod:src})
r=ssh(a,'python3',f'''from pathlib import Path
import hashlib,json
b=Path({B!r});s=b/'NET_src';pins={{str(p.relative_to(s)):hashlib.sha256(p.read_bytes()).hexdigest() for p in s.rglob('*') if p.is_file()}}
(b/'NET_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\\n');print(json.dumps(pins))
''');assert r.returncode==0,r.stderr;(E/'NET_SOURCE_PINS.json').write_text(r.stdout)
print('Native prefix single-iteration packet uploaded')
