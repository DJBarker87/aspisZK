use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
mod reference { include!("NGM_reference.rs"); }
fn qwords(x:K)->[u32;4]{[x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0]}
fn fromq(x:[u32;4])->K{K{c0:aspis_core::field::CM31{a:M31(x[0]),b:M31(x[1])},c1:aspis_core::field::CM31{a:M31(x[2]),b:M31(x[3])}}}
fn rawrow(a:&[K;4])->[[u32;4];4]{[qwords(a[0]),qwords(a[1]),qwords(a[2]),qwords(a[3])]}
pub(super) fn guard_raw_post(r:bool,w:&Weights,folds:usize)->bool{
 let variant=match w.variant{Variant::S1=>0,Variant::S2=>1,Variant::D=>2};
 let reference=reference::guard_raw_ref(variant,folds,rawrow(&w.factors[0][2]),rawrow(&w.factors[2][2]),rawrow(&w.factors[0][3]),rawrow(&w.factors[2][3]));
 let same=r==reference;if cfg!(NGM_invert){!same}else{same}
}
#[kani::proof_for_contract(shared_two_point_guard)] #[kani::unwind(12)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn guard_raw_contract(){let w=Weights{variant:match kani::any::<u8>()%3{0=>Variant::S1,1=>Variant::S2,_=>Variant::D},
 factors:core::array::from_fn(|_|core::array::from_fn(|_|core::array::from_fn(|_|fromq(kani::any())))),
 points:core::array::from_fn(|_|core::array::from_fn(|_|fromq(kani::any()))),extra:core::array::from_fn(|_|fromq(kani::any()))};
 shared_two_point_guard(&w,kani::any());}
#[kani::proof] #[kani::unwind(65)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn copy_control(){let src:[u8;64]=kani::any();let mut dst:[u8;64]=kani::any();dst.copy_from_slice(&src);let i:usize=kani::any();kani::assume(i<64);assert!((dst[i]==src[i]) != cfg!(NGM_invert));}
