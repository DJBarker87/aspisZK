from pathlib import Path
import json,hashlib,subprocess,difflib
E=Path(__file__).resolve().parent;REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';path='crates/aspis-r1-cost-probe/src/verifier.rs'
frozen=subprocess.check_output(['git','show',REV+':'+path],text=True)
assert 'bytes[11..16].iter().any(|&x|x!=0)' in frozen
s='''use super::*;
use crate::{KMX_copy_nonoverlapping,KMX_copy_from_slice};
fn check(){let bytes:[u8;5]=kani::any();let i:usize=kani::any();kani::assume(i<=5);let mut it=bytes[i..].iter();let next=it.next();let mut cursor=i+(if next.is_some(){1}else{0});let answer=next.map(|&x|x!=0);if cfg!(NIL_invert){cursor^=1;}assert_eq!(cursor,if i<5{i+1}else{i});assert_eq!(it.len(),5-cursor);assert_eq!(answer,if i<5{Some(bytes[i]!=0)}else{None});}
'''
for suffix in ['','_renamed']:
 s+='#[kani::proof]\n#[kani::unwind(8)]\n#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]\n#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]\nfn header_step'+suffix+'(){check();}\n'
x=json.loads((E/'NIL_NATIVE_INPUTS.json').read_text());assert 'mod NIL_header_native;' not in x[path]
x[path]+='\n#[cfg(kani)]\n#[path="NIL_header_native.rs"]\nmod NIL_header_native;\n';n='crates/aspis-r1-cost-probe/src/NIL_header_native.rs';x[n]=s
(E/'NIL_NATIVE_INPUTS.json').write_text(json.dumps(x,indent=2)+'\n');(E/'NIL_header_native.rs.txt').write_text(s)
pins=json.loads((E/'NIL_SOURCE_PINS.json').read_text());pins.update({n:hashlib.sha256(v.encode()).hexdigest() for n,v in x.items()});(E/'NIL_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
rows=[dict(family='header_step',function='verifier::NIL_header_native::header_step',rename='verifier::NIL_header_native::header_step_renamed',status='planned',domain='arbitrary five header bytes and iterator pre-cursor0..5; one actual native slice iterator next plus the frozen closure; NID/NIL header induction retained but native/emitted step association OPEN')]
(E/'NIL_HEADER_MATRIX.json').write_text(json.dumps(rows,indent=2)+'\n')
patch=''
for n,v in x.items():
 try:old=subprocess.check_output(['git','show',REV+':'+n],text=True,stderr=subprocess.DEVNULL)
 except subprocess.CalledProcessError:old=''
 patch+=''.join(difflib.unified_diff(old.splitlines(True),v.splitlines(True),fromfile='a/'+n,tofile='b/'+n))
(E/'NIL_native.patch').write_text(patch)
