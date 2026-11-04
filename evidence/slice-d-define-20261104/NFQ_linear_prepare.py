from pathlib import Path
import json,hashlib,difflib,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1];C='crates/aspis-core/src/';inputs=json.loads((E/'NFQ_NATIVE_INPUTS.json').read_text());old={};files={}
n=C+'NFQ_field.rs';old[n]=inputs[n]
kmx='''#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[M31]>::copy_from_slice,KMX_copy_from_slice)]
'''
code='''
impl kani::Arbitrary for PreparedQm31Multiplier{fn any()->Self{any_prepared()}}
#[kani::modifies()] #[kani::ensures(|r| r.components[0][0].0==0)]
fn weak_prepared()->PreparedQm31Multiplier{PreparedQm31Multiplier{components:[[M31(0),M31(1),M31(2)],[M31(3),M31(4),M31(5)],[M31(6),M31(7),M31(8)]]}}
#[kani::proof_for_contract(weak_prepared)]
KMXL
fn record_real(){assert!(weak_prepared().components[1][1].0==4);}
#[kani::proof] #[kani::stub_verified(weak_prepared)]
KMXL
fn record_unimplied(){assert!(weak_prepared().components[1][1].0==4);}
#[kani::modifies(&mut x[0])] #[kani::ensures(|r| r.components[0][0].0==0)]
fn bad_record_frame(x:&mut[u8;2])->PreparedQm31Multiplier{x[1]=x[1].wrapping_add(1);weak_prepared()}
#[kani::proof_for_contract(bad_record_frame)]
KMXL
fn record_frame(){let mut x:[u8;2]=kani::any();let _=bad_record_frame(&mut x);}
'''.replace('KMXL',kmx);files[n]=old[n]+code
n=C+'state_only_hiding.rs';old[n]=subprocess.check_output(['git','show','4bb3b3f:'+n],cwd=R,text=True);sig='fn cm31_mul_r(value: CM31) -> CM31';assert old[n].count(sig)==1
files[n]=old[n].replace(sig,'#[cfg_attr(kani,kani::requires(value.a.0<P && value.b.0<P))]\n#[cfg_attr(kani,kani::modifies())]\n#[cfg_attr(kani,kani::ensures(|r| ((r.a.0,r.b.0)==NFQ_hiding::reference(value.a.0,value.b.0)) != cfg!(NFQ_invert)))]\n'+sig,1)+'\n#[cfg(kani)]\n#[path="NFQ_hiding.rs"]\nmod NFQ_hiding;\n'
files[C+'NFQ_hiding.rs']='''use super::*;
pub(super) fn reference(a:u32,b:u32)->(u32,u32){
 let aa=a+a;let aa=if aa>=P{aa-P}else{aa};
 let bb=b+b;let bb=if bb>=P{bb-P}else{bb};
 ((((aa as u64)+(P as u64)-(b as u64))%(P as u64))as u32,(((a as u64)+(bb as u64))%(P as u64))as u32)
}
#[kani::proof_for_contract(cm31_mul_r)]
fn linear_contract(){let value=CM31{a:M31(kani::any()),b:M31(kani::any())};kani::assume(value.a.0<P&&value.b.0<P);let _=cm31_mul_r(value);}
'''
# P is imported in this frozen module? Resolve explicitly to the same field constant.
files[C+'state_only_hiding.rs']=files[C+'state_only_hiding.rs'].replace('value.a.0<P && value.b.0<P','value.a.0<crate::field::P && value.b.0<crate::field::P')
files[C+'NFQ_hiding.rs']=files[C+'NFQ_hiding.rs'].replace('use super::*;','use super::*;\nuse crate::field::{P,M31};')
inputs.update(files);(E/'NFQ_NATIVE_INPUTS.json').write_text(json.dumps(inputs,indent=1)+'\n')
pins=json.loads((E/'NFQ_SOURCE_PINS.json').read_text());pins.update({n:hashlib.sha256(s.encode()).hexdigest() for n,s in files.items()});(E/'NFQ_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
patch=[]
for n,s in files.items():patch+=difflib.unified_diff(old.get(n,'').splitlines(True),s.splitlines(True),fromfile='a/'+n if n in old else '/dev/null',tofile='b/'+n)
(E/'NFQ_linear.patch').write_text(''.join(patch))
