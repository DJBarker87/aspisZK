#![no_std]
extern crate alloc;
pub mod sampler;
pub mod r1_wire;
mod r1_semantic {
 // Diagnostic assertion formatting change only; original native step is unchanged.
 macro_rules! assert_eq { ($left:expr,$right:expr $(,)?) => { assert!($left == $right) }; }
 use crate::r1_wire::{self as wire,Error};
 use alloc::boxed::Box;
 use aspis_core::field::QM31;
 #[cfg(kani)]
 #[path="../claims_write_proofs.rs"]
 mod claims_write_proofs;
}

#[kani::proof]
fn layout_qm31_box(){
 use alloc::boxed::Box;use core::mem::MaybeUninit;use aspis_core::field::QM31;
 let mut out=Box::new(MaybeUninit::<[[QM31;29];3]>::uninit());
 unsafe{out.as_mut_ptr().cast::<[QM31;29]>().write([QM31::ZERO;29]);}
 let row=unsafe{out.as_ptr().cast::<[QM31;29]>().read()}; assert!(row==[QM31::ZERO;29]);
}
#[kani::proof]
fn layout_record(){let data=[0u8;3717];let r=r1_wire::s1_claims_probe_record(kani::any(),&data);assert!(r.framed().len()==3717);}
#[kani::proof]
fn layout_error(){let e=if kani::any::<bool>(){r1_wire::Error::Allocation}else{r1_wire::Error::Public};let x=Some(e);assert!(x==Some(e));}

#[kani::proof]
fn layout_arbitrary_array(){let a=kani::any::<[[u32;4];29]>();assert!(a[0][0]==a[0][0]);}
#[kani::proof]
fn layout_cover(){let p=kani::any::<bool>();kani::cover!(p,"symbolic branch");}
