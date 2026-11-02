from NEO_remote import *
import difflib,hashlib
R=E.parent.parent;a='NEO_Q_INPUT';admit(a)
REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';f='crates/aspis-r1-cost-probe/src/fast_pairing.rs';w='crates/aspis-core/src/field/wide_exact.rs'
old={n:subprocess.check_output(['git','show',REV+':'+n],cwd=R,text=True) for n in [f,w]}
marker='\n}\n\n\nuse aspis_core::field::{CM31, QM31, WideExact as E};';assert old[f].count(marker)==1
new={f:old[f].replace(marker,'\n#[cfg(kani)]\nmod NEO_q { include!(concat!(env!("CARGO_MANIFEST_DIR"),"/src/NEO_q.rs")); }'+marker),w:old[w]+'''
#[cfg(kani)]
impl WideExact {
 pub fn NEO_from_raw(x:[u32;8])->Self {
  Self{c0:QM31{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}},c1:QM31{c0:CM31{a:M31(x[4]),b:M31(x[5])},c1:CM31{a:M31(x[6]),b:M31(x[7])}}}
 }
}
''','crates/aspis-r1-cost-probe/src/NEO_q.rs':(E/'NEO_q.rs.txt').read_text(),'crates/aspis-r1-cost-probe/src/NEO_q_reference.rs':(E/'NEO_q_reference.rs').read_text()}
patch=''.join(''.join(difflib.unified_diff(old.get(n,'').splitlines(True),s.splitlines(True),fromfile='a/'+n if n in old else '/dev/null',tofile='b/'+n)) for n,s in new.items());(E/'NEO_Q.patch').write_text(patch)
upload(a,{'NEO_src/'+n:s for n,s in new.items()})
r=ssh(a,'python3',f'''from pathlib import Path
import json,hashlib
b=Path({B!r});s=b/'NEO_src';pins={{str(p.relative_to(s)):hashlib.sha256(p.read_bytes()).hexdigest() for p in s.rglob('*') if p.is_file()}}
(b/'NEO_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\\n');print(json.dumps(pins))
''');assert r.returncode==0,r.stderr;(E/'NEO_SOURCE_PINS.json').write_text(r.stdout)
