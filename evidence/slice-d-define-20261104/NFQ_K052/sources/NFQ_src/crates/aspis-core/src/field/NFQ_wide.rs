use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn any_q()->QM31{QM31{c0:CM31{a:M31(kani::any()),b:M31(kani::any())},c1:CM31{a:M31(kani::any()),b:M31(kani::any())}}}
fn any_wide()->WideExact{WideExact{c0:any_q(),c1:any_q()}}
#[kani::proof_for_contract(WideExact::c0)]
#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[M31]>::copy_from_slice,KMX_copy_from_slice)]

fn c0_contract(){let _=any_wide().c0();}
#[kani::proof_for_contract(WideExact::c1)]
#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[M31]>::copy_from_slice,KMX_copy_from_slice)]

fn c1_contract(){let _=any_wide().c1();}
#[kani::proof]
#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[M31]>::copy_from_slice,KMX_copy_from_slice)]

fn copy_positive(){let src=any_wide();let mut dst=any_wide();let qs=any_q();let mut qd=any_q();unsafe{core::ptr::copy_nonoverlapping(&src,&mut dst,1);core::ptr::copy_nonoverlapping(&qs,&mut qd,1)};assert!(src==dst&&qs==qd);}
#[kani::proof]
#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[M31]>::copy_from_slice,KMX_copy_from_slice)]

fn copy_negative(){let src=any_wide();let mut dst=any_wide();let qs=any_q();let mut qd=any_q();unsafe{core::ptr::copy_nonoverlapping(&src,&mut dst,1);core::ptr::copy_nonoverlapping(&qs,&mut qd,1)};assert!(!(src==dst&&qs==qd));}
