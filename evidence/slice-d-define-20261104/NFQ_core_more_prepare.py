from pathlib import Path
import json,hashlib,difflib,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1];C='crates/aspis-core/src/';inputs=json.loads((E/'NFQ_NATIVE_INPUTS.json').read_text())
old={n:inputs.get(n,subprocess.check_output(['git','show','4bb3b3f:'+n],cwd=R,text=True) if n.endswith('lib.rs') else '') for n in [C+'field.rs',C+'lib.rs',C+'NFQ_field.rs']};files=dict(old)
s=files[C+'field.rs'];sig='pub fn reduce_u62(value: u64) -> M31';assert s.count(sig)==1
s=s.replace(sig,'#[cfg_attr(kani,kani::requires(value < (1u64<<62)))]\n#[cfg_attr(kani,kani::modifies())]\n#[cfg_attr(kani,kani::ensures(|r| (r.0 == (value % (P as u64)) as u32) != cfg!(NFQ_invert)))]\n'+sig,1)
sig='pub fn new(value: QM31) -> Self';assert s.count(sig)==1
s=s.replace(sig,'#[cfg_attr(kani,kani::requires(value.c0.a.0<P && value.c0.b.0<P && value.c1.a.0<P && value.c1.b.0<P))]\n#[cfg_attr(kani,kani::modifies())]\n#[cfg_attr(kani,kani::ensures(|r| NFQ_field::prep_matches(r,value) != cfg!(NFQ_invert)))]\n'+sig,1);files[C+'field.rs']=s
files[C+'lib.rs']=files[C+'lib.rs'].replace('#![no_std]','#![cfg_attr(kani,feature(allocator_api))]\n#![no_std]',1)
code='''
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn add_word(a:u32,b:u32)->u32{let s=a+b;if s>=P{s-P}else{s}}
pub(super) fn prep_spec(v:QM31)->[[u32;3];3]{
 let a=v.c0.a.0;let b=v.c0.b.0;let c=v.c1.a.0;let d=v.c1.b.0;
 let ac=add_word(a,c);let bd=add_word(b,d);
 [[a,b,add_word(a,b)],[c,d,add_word(c,d)],[ac,bd,add_word(ac,bd)]]
}
pub(super) fn prep_matches(r:&PreparedQm31Multiplier,v:QM31)->bool{
 let e=prep_spec(v);
 r.components[0][0].0==e[0][0] && r.components[0][1].0==e[0][1] && r.components[0][2].0==e[0][2] &&
 r.components[1][0].0==e[1][0] && r.components[1][1].0==e[1][1] && r.components[1][2].0==e[1][2] &&
 r.components[2][0].0==e[2][0] && r.components[2][1].0==e[2][1] && r.components[2][2].0==e[2][2]
}
fn any_q()->QM31{QM31{c0:CM31{a:M31(kani::any()),b:M31(kani::any())},c1:CM31{a:M31(kani::any()),b:M31(kani::any())}}}
fn any_prepared()->PreparedQm31Multiplier{PreparedQm31Multiplier{components:[
 [M31(kani::any()),M31(kani::any()),M31(kani::any())],
 [M31(kani::any()),M31(kani::any()),M31(kani::any())],
 [M31(kani::any()),M31(kani::any()),M31(kani::any())]]}}
#[kani::proof_for_contract(M31::reduce_u62)]
fn reduce_contract(){let x:u64=kani::any();kani::assume(x<(1u64<<62));let _=M31::reduce_u62(x);}
#[kani::proof_for_contract(PreparedQm31Multiplier::new)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[M31]>::copy_from_slice,KMX_copy_from_slice)]
fn prep_contract(){let v=any_q();kani::assume(v.c0.a.0<P && v.c0.b.0<P && v.c1.a.0<P && v.c1.b.0<P);let _=PreparedQm31Multiplier::new(v);}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[M31]>::copy_from_slice,KMX_copy_from_slice)]
fn prep_copy_positive(){let src=any_prepared();let mut dst=any_prepared();let r:usize=kani::any();let c:usize=kani::any();kani::assume(r<3&&c<3);unsafe{core::ptr::copy_nonoverlapping(&src,&mut dst,1)};assert!(dst.components[r][c].0==src.components[r][c].0);}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[M31]>::copy_from_slice,KMX_copy_from_slice)]
fn prep_copy_negative(){let src=any_prepared();let mut dst=any_prepared();let r:usize=kani::any();let c:usize=kani::any();kani::assume(r<3&&c<3);unsafe{core::ptr::copy_nonoverlapping(&src,&mut dst,1)};assert!(dst.components[r][c].0!=src.components[r][c].0);}
'''
files[C+'NFQ_field.rs']+=code
inputs.update(files);(E/'NFQ_NATIVE_INPUTS.json').write_text(json.dumps(inputs,indent=1)+'\n')
pins=json.loads((E/'NFQ_SOURCE_PINS.json').read_text());pins.update({n:hashlib.sha256(s.encode()).hexdigest() for n,s in files.items()});(E/'NFQ_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
patch=[]
for n,s in files.items():patch+=difflib.unified_diff(old[n].splitlines(True),s.splitlines(True),fromfile='a/'+n,tofile='b/'+n)
(E/'NFQ_core_more.patch').write_text(''.join(patch))
