from pathlib import Path
import json,hashlib,subprocess,difflib
E=Path(__file__).resolve().parent
import time
while (E/'NGW_LEAN_TURN').exists():time.sleep(2)
C='crates/aspis-r1-cost-probe/src/';x=json.loads((E/'NGW_NATIVE_INPUTS.json').read_text());fast=x[C+'fast_pairing.rs'];needle=' #[cfg(kani)] pub(super) mod NGM_canonical';i=fast.index(needle)
fast=fast[:i]+' #[cfg(kani)] pub(super) mod NGW_abi_canonical { include!(concat!(env!("CARGO_MANIFEST_DIR"),"/src/NGW_abi_canonical.rs")); }\n'+fast[i:]
fast+='\n#[cfg(kani)] #[path="NGW_abi.rs"] mod NGW_abi;\n';x[C+'fast_pairing.rs']=fast
x[C+'NGW_abi_canonical.rs']='pub(crate) fn word(x:&super::Dot,j:usize)->u64{x.sums[j]}\n'
x[C+'NGW_dot_reference.rs']=(E/'NGW_dot_reference.rs.txt').read_text()
x[C+'NGW_abi.rs']=r'''use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
mod reference{include!("NGW_dot_reference.rs");}
#[kani::proof]#[kani::unwind(65)]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn nine_word_model(){let w:[u64;9]=kani::any();kani::assume(w[8]<=64);let actual=NGM_helpers::make(w);let expected=reference::pack(reference::unpack(w));let j:usize=kani::any();kani::assume(j<9);let mut observed=if j<4{canonical::NGW_abi_canonical::word(&actual.c0,j)}else if j<8{canonical::NGW_abi_canonical::word(&actual.c1,j-4)}else{actual.count as u64};if cfg!(NGW_invert){observed^=1;}assert!(observed==expected[j]);}
'''
(E/'NGW_NATIVE_INPUTS.json').write_text(json.dumps(x,indent=1)+'\n');pins=json.loads((E/'NGW_SOURCE_PINS.json').read_text());pins.update({n:hashlib.sha256(t.encode()).hexdigest()for n,t in x.items()});(E/'NGW_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
patch=[]
for n,t in x.items():
 r=subprocess.run(['git','show','4bb3b3f:'+n],capture_output=True,text=True);patch+=difflib.unified_diff(r.stdout.splitlines(True),t.splitlines(True),fromfile='a/'+n if not r.returncode else '/dev/null',tofile='b/'+n)
(E/'NGW_harness.patch').write_text(''.join(patch))
