use crate::equivalence16::qs;
use crate::{deployed_poseidon16::access16 as d,reference_poseidon16::access16 as r};
#[kani::proof] #[kani::unwind(128)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn raw_all_words_wrong() {let s=qs::<4>();let left=d::raw(s);let mut right=r::raw(s);right[0]^=1;assert_eq!(left,right);}
#[kani::proof] #[kani::unwind(128)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn raw_all_words() {let s=qs::<4>();let left=d::raw(s);let right=r::raw(s);assert_eq!(left,right);}
#[kani::proof] #[kani::unwind(128)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn internal_all_words_wrong() {let s=qs::<16>();let left=d::internal(s);let mut right=r::internal(s);right[0].c0.a.0^=1;assert_eq!(left,right);}
#[kani::proof] #[kani::unwind(128)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn internal_all_words() {let s=qs::<16>();let left=d::internal(s);let right=r::internal(s);assert_eq!(left,right);}
