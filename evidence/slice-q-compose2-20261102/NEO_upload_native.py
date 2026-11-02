from NEO_remote import *
import hashlib,difflib
R=E.parent.parent;a='NEO_NATIVE_INPUT';admit(a)
f='crates/aspis-core/src/field.rs';l='crates/aspis-core/src/lib.rs'
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
original={n:subprocess.check_output(['git','show',rev+':'+n],cwd=R,text=True) for n in [f,l]}
new={f:original[f]+'\n#[cfg(kani)]\nmod NEO_parsers;\n',l:original[l].replace('#![no_std]','#![no_std]\n#![cfg_attr(kani,feature(allocator_api))]')}
new['crates/aspis-core/src/field/NEO_parsers.rs']=(E/'NEO_parsers.rs.txt').read_text()
patch=''.join(''.join(difflib.unified_diff(original.get(n,'').splitlines(True),s.splitlines(True),fromfile='a/'+n if n in original else '/dev/null',tofile='b/'+n)) for n,s in new.items())
(E/'NEO_NATIVE.patch').write_text(patch)
# Validation clients preserve all NEB checks; own path/prefix adaptation only.
for name in ['gate','graph']:
 s=(E.parent/'slice-q-compose-20261029'/('NEB_'+name+'.py')).read_text().replace('NEB','NEO')
 (E/('NEO_'+name+'.py')).write_text(s)
(E/'NEO_TOOL_PINS.json').write_bytes((E.parent/'slice-q-compose-20261029/NEB_TOOL_PINS.json').read_bytes())
files={('NEO_src/'+n):s for n,s in new.items()}
files.update({n:(E/n).read_text() for n in ['NEO_gate.py','NEO_graph.py','NEO_TOOL_PINS.json']})
upload(a,files)
r=ssh(a,'python3',f'''from pathlib import Path
import json,hashlib
b=Path({B!r});s=b/'NEO_src'
pins={{str(p.relative_to(s)):hashlib.sha256(p.read_bytes()).hexdigest() for p in s.rglob('*') if p.is_file()}}
(b/'NEO_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\\n');print(json.dumps(pins))
''');assert r.returncode==0,r.stderr
(E/'NEO_SOURCE_PINS.json').write_text(r.stdout)
print('Uploaded frozen source plus committed scratch-only parser patch')
