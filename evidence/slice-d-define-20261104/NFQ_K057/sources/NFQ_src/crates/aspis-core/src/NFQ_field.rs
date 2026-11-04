use super::*;
// Natural-number field specs paired with emitted-definition theorems.
pub(super) fn neg_ref(x:u32)->u32{if x==0{0}else{2147483647-x}}
pub(super) fn cm_ref(x:u32)->(u32,u32){(x,0)}
pub(super) fn qm_ref(a:u32,b:u32)->(u32,u32,u32,u32){(a,b,0,0)}
#[kani::proof_for_contract(M31::neg)]
fn neg_contract(){let x=M31(kani::any());kani::assume(x.0<P);let _=x.neg();}
#[kani::proof_for_contract(CM31::from_m31)]
fn cm_contract(){let _=CM31::from_m31(M31(kani::any()));}
#[kani::proof_for_contract(QM31::from_cm31)]
fn qm_contract(){let _=QM31::from_cm31(CM31{a:M31(kani::any()),b:M31(kani::any())});}

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

impl kani::Arbitrary for PreparedQm31Multiplier{fn any()->Self{any_prepared()}}
#[kani::modifies()] #[kani::ensures(|r| r.components[0][0].0==0)]
fn weak_prepared()->PreparedQm31Multiplier{PreparedQm31Multiplier{components:[[M31(0),M31(1),M31(2)],[M31(3),M31(4),M31(5)],[M31(6),M31(7),M31(8)]]}}
#[kani::proof_for_contract(weak_prepared)]
#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[M31]>::copy_from_slice,KMX_copy_from_slice)]

fn record_real(){assert!(weak_prepared().components[1][1].0==4);}
#[kani::proof] #[kani::stub_verified(weak_prepared)]
#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[M31]>::copy_from_slice,KMX_copy_from_slice)]

fn record_unimplied(){assert!(weak_prepared().components[1][1].0==4);}
#[kani::modifies(&mut x[0])] #[kani::ensures(|r| r.components[0][0].0==0)]
fn bad_record_frame(x:&mut[u8;2])->PreparedQm31Multiplier{x[1]=x[1].wrapping_add(1);weak_prepared()}
#[kani::proof_for_contract(bad_record_frame)]
#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[M31]>::copy_from_slice,KMX_copy_from_slice)]

fn record_frame(){let mut x:[u8;2]=kani::any();let _=bad_record_frame(&mut x);}
