#![allow(unexpected_cfgs, dead_code)]
extern crate alloc;
use aspis_core::field;
#[path = "reference/field.rs"] mod reference;
#[cfg(kani)]
mod proofs {
    use super::*;
    fn canonical() -> u32 { let x:u32=kani::any(); kani::assume(x<field::P); x }
    #[kani::proof]
    fn equiv_reduce64() { let x:u64=kani::any(); assert_eq!(field::M31::reduce_u64(x).0, reference::M31::reduce_u64(x).0); }
    #[kani::proof]
    fn equiv_reduce128() { let x:u128=kani::any(); assert_eq!(field::M31::reduce_u128(x).0, reference::M31::reduce_u128(x).0); }
    #[kani::proof]
    fn equiv_add() { let a=canonical();let b=canonical(); assert_eq!(field::M31(a).add(field::M31(b)).0, reference::M31(a).add(reference::M31(b)).0); }
    #[kani::proof]
    fn equiv_sub() { let a=canonical();let b=canonical(); assert_eq!(field::M31(a).sub(field::M31(b)).0, reference::M31(a).sub(reference::M31(b)).0); }
    #[kani::proof]
    fn equiv_neg() { let a=canonical(); assert_eq!(field::M31(a).neg().0, reference::M31(a).neg().0); }
    #[kani::proof]
    fn equiv_zero() { let a:u32=kani::any(); assert_eq!(field::M31(a).is_zero(), reference::M31(a).is_zero()); }
    #[kani::proof]
    fn equiv_raw_normalize() { let a:u32=kani::any(); assert_eq!(field::ct::reduce64(a as u64), a % field::P); }
}



#[cfg(kani)] mod instrumented;
#[cfg(kani)] mod traces {
use super::instrumented::*;
#[kani::proof]
#[kani::unwind(40)]
fn two_run_subtract_p() { let mut t=Trace::new(); let mut u=Trace::new(); let a:u32=kani::any();let b:u32=kani::any();let _=subtract_p(a,&mut t);let _=subtract_p(b,&mut u);assert_eq!(t.len,u.len);for i in 0..32 {assert_eq!(t.events[i],u.events[i]);}}
#[kani::proof]
#[kani::unwind(40)]
fn two_run_reduce64() { let mut t=Trace::new(); let mut u=Trace::new(); let a:u64=kani::any();let b:u64=kani::any();let _=reduce64(a,&mut t);let _=reduce64(b,&mut u);assert_eq!(t.len,u.len);for i in 0..32 {assert_eq!(t.events[i],u.events[i]);}}
#[kani::proof]
#[kani::unwind(40)]
fn two_run_reduce128() { let mut t=Trace::new(); let mut u=Trace::new(); let a:u128=kani::any();let b:u128=kani::any();let _=reduce128(a,&mut t);let _=reduce128(b,&mut u);assert_eq!(t.len,u.len);for i in 0..32 {assert_eq!(t.events[i],u.events[i]);}}
#[kani::proof]
#[kani::unwind(40)]
fn two_run_add() { let mut t=Trace::new(); let mut u=Trace::new(); let a:u32=kani::any();let b:u32=kani::any();let c:u32=kani::any();let d:u32=kani::any();let _=add(a,c,&mut t);let _=add(b,d,&mut u);assert_eq!(t.len,u.len);for i in 0..32 {assert_eq!(t.events[i],u.events[i]);}}
#[kani::proof]
#[kani::unwind(40)]
fn two_run_sub() { let mut t=Trace::new(); let mut u=Trace::new(); let a:u32=kani::any();let b:u32=kani::any();let c:u32=kani::any();let d:u32=kani::any();let _=sub(a,c,&mut t);let _=sub(b,d,&mut u);assert_eq!(t.len,u.len);for i in 0..32 {assert_eq!(t.events[i],u.events[i]);}}
#[kani::proof]
#[kani::unwind(40)]
fn two_run_neg() { let mut t=Trace::new(); let mut u=Trace::new(); let a:u32=kani::any();let b:u32=kani::any();let _=neg(a,&mut t);let _=neg(b,&mut u);assert_eq!(t.len,u.len);for i in 0..32 {assert_eq!(t.events[i],u.events[i]);}}
#[kani::proof]
#[kani::unwind(40)]
fn two_run_is_zero() { let mut t=Trace::new(); let mut u=Trace::new(); let a:u32=kani::any();let b:u32=kani::any();let _=is_zero(a,&mut t);let _=is_zero(b,&mut u);assert_eq!(t.len,u.len);for i in 0..32 {assert_eq!(t.events[i],u.events[i]);}}
}

#[cfg(kani)] mod tower_linear {
use super::*;
fn limbs()->[u32;8] {let x:[u32;8]=kani::any(); for a in x {kani::assume(a<field::P);} x}
#[kani::proof]
#[kani::unwind(40)]
fn cm_add() {let a=limbs();let b=limbs();let x=field::WideExact::from_limbs(a).unwrap();let y=field::WideExact::from_limbs(b).unwrap();let r=reference::WideExact::from_limbs(a).unwrap();let t=reference::WideExact::from_limbs(b).unwrap();let x=x.c0().c0;let y=y.c0().c0;let r=r.c0().c0;let t=t.c0().c0;let mut left=[0u8;8];let mut right=[0u8;8];x.add(y).write_le_bytes(&mut left);r.add(t).write_le_bytes(&mut right);assert_eq!(left,right);}
#[kani::proof]
#[kani::unwind(40)]
fn cm_sub() {let a=limbs();let b=limbs();let x=field::WideExact::from_limbs(a).unwrap();let y=field::WideExact::from_limbs(b).unwrap();let r=reference::WideExact::from_limbs(a).unwrap();let t=reference::WideExact::from_limbs(b).unwrap();let x=x.c0().c0;let y=y.c0().c0;let r=r.c0().c0;let t=t.c0().c0;let mut left=[0u8;8];let mut right=[0u8;8];x.sub(y).write_le_bytes(&mut left);r.sub(t).write_le_bytes(&mut right);assert_eq!(left,right);}
#[kani::proof]
#[kani::unwind(40)]
fn cm_neg() {let a=limbs();let b=limbs();let x=field::WideExact::from_limbs(a).unwrap();let y=field::WideExact::from_limbs(b).unwrap();let r=reference::WideExact::from_limbs(a).unwrap();let t=reference::WideExact::from_limbs(b).unwrap();let x=x.c0().c0;let y=y.c0().c0;let r=r.c0().c0;let t=t.c0().c0;let mut left=[0u8;8];let mut right=[0u8;8];x.neg().write_le_bytes(&mut left);r.neg().write_le_bytes(&mut right);assert_eq!(left,right);}
#[kani::proof]
#[kani::unwind(40)]
fn cm_is_zero() {let a=limbs();let b=limbs();let x=field::WideExact::from_limbs(a).unwrap();let y=field::WideExact::from_limbs(b).unwrap();let r=reference::WideExact::from_limbs(a).unwrap();let t=reference::WideExact::from_limbs(b).unwrap();let x=x.c0().c0;let y=y.c0().c0;let r=r.c0().c0;let t=t.c0().c0;assert_eq!(x.is_zero(),r.is_zero());}
#[kani::proof]
#[kani::unwind(40)]
fn qm_add() {let a=limbs();let b=limbs();let x=field::WideExact::from_limbs(a).unwrap();let y=field::WideExact::from_limbs(b).unwrap();let r=reference::WideExact::from_limbs(a).unwrap();let t=reference::WideExact::from_limbs(b).unwrap();let x=x.c0();let y=y.c0();let r=r.c0();let t=t.c0();let mut left=[0u8;16];let mut right=[0u8;16];x.add(y).write_le_bytes(&mut left);r.add(t).write_le_bytes(&mut right);assert_eq!(left,right);}
#[kani::proof]
#[kani::unwind(40)]
fn qm_sub() {let a=limbs();let b=limbs();let x=field::WideExact::from_limbs(a).unwrap();let y=field::WideExact::from_limbs(b).unwrap();let r=reference::WideExact::from_limbs(a).unwrap();let t=reference::WideExact::from_limbs(b).unwrap();let x=x.c0();let y=y.c0();let r=r.c0();let t=t.c0();let mut left=[0u8;16];let mut right=[0u8;16];x.sub(y).write_le_bytes(&mut left);r.sub(t).write_le_bytes(&mut right);assert_eq!(left,right);}
#[kani::proof]
#[kani::unwind(40)]
fn qm_neg() {let a=limbs();let b=limbs();let x=field::WideExact::from_limbs(a).unwrap();let y=field::WideExact::from_limbs(b).unwrap();let r=reference::WideExact::from_limbs(a).unwrap();let t=reference::WideExact::from_limbs(b).unwrap();let x=x.c0();let y=y.c0();let r=r.c0();let t=t.c0();let mut left=[0u8;16];let mut right=[0u8;16];x.neg().write_le_bytes(&mut left);r.neg().write_le_bytes(&mut right);assert_eq!(left,right);}
#[kani::proof]
#[kani::unwind(40)]
fn qm_is_zero() {let a=limbs();let b=limbs();let x=field::WideExact::from_limbs(a).unwrap();let y=field::WideExact::from_limbs(b).unwrap();let r=reference::WideExact::from_limbs(a).unwrap();let t=reference::WideExact::from_limbs(b).unwrap();let x=x.c0();let y=y.c0();let r=r.c0();let t=t.c0();assert_eq!(x.is_zero(),r.is_zero());}
#[kani::proof]
#[kani::unwind(40)]
fn wide_add() {let a=limbs();let b=limbs();let x=field::WideExact::from_limbs(a).unwrap();let y=field::WideExact::from_limbs(b).unwrap();let r=reference::WideExact::from_limbs(a).unwrap();let t=reference::WideExact::from_limbs(b).unwrap();assert_eq!(x.add(y).to_limbs(),r.add(t).to_limbs());}
#[kani::proof]
#[kani::unwind(40)]
fn wide_sub() {let a=limbs();let b=limbs();let x=field::WideExact::from_limbs(a).unwrap();let y=field::WideExact::from_limbs(b).unwrap();let r=reference::WideExact::from_limbs(a).unwrap();let t=reference::WideExact::from_limbs(b).unwrap();assert_eq!(x.sub(y).to_limbs(),r.sub(t).to_limbs());}
#[kani::proof]
#[kani::unwind(40)]
fn wide_neg() {let a=limbs();let b=limbs();let x=field::WideExact::from_limbs(a).unwrap();let y=field::WideExact::from_limbs(b).unwrap();let r=reference::WideExact::from_limbs(a).unwrap();let t=reference::WideExact::from_limbs(b).unwrap();assert_eq!(x.neg().to_limbs(),r.neg().to_limbs());}
#[kani::proof]
#[kani::unwind(40)]
fn wide_is_zero() {let a=limbs();let b=limbs();let x=field::WideExact::from_limbs(a).unwrap();let y=field::WideExact::from_limbs(b).unwrap();let r=reference::WideExact::from_limbs(a).unwrap();let t=reference::WideExact::from_limbs(b).unwrap();assert_eq!(x.is_zero(),r.is_zero());}
}
#[cfg(kani)] mod products {
use super::*;
fn old_reduce(x:u64)->u32 {reference::M31::reduce_u64(x).0}
#[kani::proof]
#[kani::stub(field::ct::reduce64, old_reduce)]
fn m31_mul_composed() {let a:u32=kani::any();let b:u32=kani::any();assert_eq!(field::M31(a).mul(field::M31(b)).0,reference::M31(a).mul(reference::M31(b)).0);}
}
