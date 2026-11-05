from pathlib import Path
import json,hashlib,subprocess,difflib
E=Path(__file__).resolve().parent;C='crates/aspis-r1-cost-probe/src/';x=json.loads((E/'NGW_NATIVE_INPUTS.json').read_text());old=x[C+'NGM_helpers.rs']
def block(mark):
 a=old.index(mark);b=old.index('{',a);depth=1;c=b+1
 while depth:depth+=(old[c]=='{')-(old[c]=='}');c+=1
 return old[a:c]
s='use super::*;\ninclude!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));\n'
for n in ['q','wide','words','encode']:s+=block('fn '+n+'(')+'\n'
s+=block('struct RoundLog')+'\n'
for n in ['scale','polynomial_reply','source_round']:s+=block('fn '+n+'(')+'\n'
s+=r'''
#[kani::proof]#[kani::unwind(65)]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn round_frame(){let values:[[u32;8];7]=core::array::from_fn(|_|words());let mut bytes=[0u8;224];for i in 0..7{encode(&mut bytes,32*i,values[i]);}let alpha=words();let claim=words();let rhs=words();let out=words();let round:usize=kani::any();kani::assume(round<2);let offset:usize=kani::any();kani::assume(offset<224);let limb:usize=kani::any();kani::assume(limb<8);let mut saved=bytes[offset];let mut log=RoundLog{scaled:wide(rhs),polynomial:wide(out),left:[0;8],factor:0,scale_calls:0,poly_args:None,poly_calls:0};let _=source_round(&bytes,wide(alpha),wide(claim),round,&mut log);if cfg!(NGW_invert){saved^=1;}assert!(bytes[offset]==saved&&log.scaled.to_limbs()[limb]==rhs[limb]&&log.polynomial.to_limbs()[limb]==out[limb]);}
'''
x[C+'NGW_round.rs']=s;x[C+'verifier.rs']+='\n#[cfg(kani)] #[path="NGW_round.rs"] mod NGW_round;\n'
(E/'NGW_NATIVE_INPUTS.json').write_text(json.dumps(x,indent=1)+'\n');pins=json.loads((E/'NGW_SOURCE_PINS.json').read_text());pins.update({n:hashlib.sha256(t.encode()).hexdigest()for n,t in x.items()});(E/'NGW_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
patch=[]
for n,t in x.items():
 r=subprocess.run(['git','show','4bb3b3f:'+n],capture_output=True,text=True);patch+=difflib.unified_diff(r.stdout.splitlines(True),t.splitlines(True),fromfile='a/'+n if not r.returncode else '/dev/null',tofile='b/'+n)
(E/'NGW_harness.patch').write_text(''.join(patch))
