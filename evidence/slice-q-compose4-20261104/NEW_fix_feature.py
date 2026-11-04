from NEW_remote import *
import hashlib,difflib
assert not (E/'NEW_ACTIVE.json').exists()
a='NEW_FEATURE_INPUT';admit(a)
f='crates/aspis-r1-cost-probe/src/lib.rs'
old=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+f],text=True)
assert old.count('#![no_std]')==1
new=old.replace('#![no_std]','#![no_std]\n#![cfg_attr(kani,feature(allocator_api))]',1)
upload(a,{'NEW_src/'+f:new})
(E/'NEW_KMX_FEATURE.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+f,tofile='b/'+f)))
r=ssh(a,'python3',f'''from pathlib import Path
import hashlib,json
b=Path({B!r});s=b/'NEW_src';pins={{str(p.relative_to(s)):hashlib.sha256(p.read_bytes()).hexdigest() for p in s.rglob('*') if p.is_file()}}
(b/'NEW_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\\n');print(json.dumps(pins))
''');assert r.returncode==0,r.stderr;(E/'NEW_SOURCE_PINS.json').write_text(r.stdout)
