from NFG_remote import *
import hashlib,difflib,subprocess
assert not (E/'NFG_ACTIVE.json').exists()
a='NFG_SMALL_SETUP';admit(a)
R=E.parent.parent;rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
paths=['crates/aspis-core/src/field.rs','crates/aspis-core/src/lib.rs']
old={n:subprocess.check_output(['git','show',rev+':'+n],cwd=R,text=True) for n in paths}
field=old[paths[0]]
cm='''    #[cfg_attr(kani, kani::requires(self.a.0 < P && self.b.0 < P))]
    #[cfg_attr(kani, kani::ensures(|r| (*r == NFG_contract::NFG_cm_ref(self)) != cfg!(NFG_bad_cm_contract)))]
    #[cfg_attr(kani, kani::modifies())]
'''
field=field.replace('    pub fn neg(self) -> CM31 {',cm+'    pub fn neg(self) -> CM31 {',1)
i=field.index('impl QM31 {');left,right=field[:i],field[i:]
qm='''    #[cfg_attr(kani, kani::ensures(|r| (*r == NFG_contract::NFG_qm_zero_ref(self)) != cfg!(NFG_bad_zero_contract)))]
    #[cfg_attr(kani, kani::modifies())]
'''
right=right.replace('    pub fn is_zero(self) -> bool {',qm+'    pub fn is_zero(self) -> bool {',1)
field=left+right+'\n#[cfg(kani)] pub mod NFG_contract;\n'
lib=old[paths[1]].replace('#![no_std]','#![no_std]\n#![cfg_attr(kani, feature(allocator_api))]').replace('extern crate alloc;','extern crate alloc;\n#[cfg(kani)] extern crate self as aspis_core;')
files={paths[0]:field,paths[1]:lib,'crates/aspis-core/src/field/NFG_contract.rs':(E/'NFG_contract.rs.txt').read_text(),'NFG_small_refs.rs':(E/'NFG_small_refs.rs.txt').read_text()}
(E/'NFG_SMALL.patch').write_text(''.join(''.join(difflib.unified_diff(old.get(n,'').splitlines(True),v.splitlines(True),fromfile='a/'+n,tofile='b/'+n)) for n,v in files.items()))
upload(a,{'NFG_src/'+n:s for n,s in files.items()})
r=ssh(a,'python3',f'''from pathlib import Path
import hashlib,json
b=Path({B!r});s=b/'NFG_src';pins=json.loads((b/'NFG_SOURCE_PINS.json').read_text())
for n in {list(files)!r}:pins[n]=hashlib.sha256((s/n).read_bytes()).hexdigest()
(b/'NFG_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\\n');print(json.dumps(pins))
''');assert r.returncode==0,r.stderr
(E/'NFG_SOURCE_PINS.json').write_text(r.stdout)
