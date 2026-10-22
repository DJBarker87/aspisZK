#![recursion_limit = "512"]
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
fn two_run_subtract_p() { let mut t=Trace::new(); let mut u=Trace::new(); let a:u32=kani::any();let b:u32=kani::any();let _=subtract_p(a,&mut t);let _=subtract_p(b,&mut u);assert!(t.len<=32);assert_eq!(t.len,u.len);for i in 0..32 {assert_eq!(t.events[i],u.events[i]);}}
#[kani::proof]
#[kani::unwind(40)]
fn two_run_reduce64() { let mut t=Trace::new(); let mut u=Trace::new(); let a:u64=kani::any();let b:u64=kani::any();let _=reduce64(a,&mut t);let _=reduce64(b,&mut u);assert!(t.len<=32);assert_eq!(t.len,u.len);for i in 0..32 {assert_eq!(t.events[i],u.events[i]);}}
#[kani::proof]
#[kani::unwind(40)]
fn two_run_reduce128() { let mut t=Trace::new(); let mut u=Trace::new(); let a:u128=kani::any();let b:u128=kani::any();let _=reduce128(a,&mut t);let _=reduce128(b,&mut u);assert!(t.len<=32);assert_eq!(t.len,u.len);for i in 0..32 {assert_eq!(t.events[i],u.events[i]);}}
#[kani::proof]
#[kani::unwind(40)]
fn two_run_add() { let mut t=Trace::new(); let mut u=Trace::new(); let a:u32=kani::any();let b:u32=kani::any();let c:u32=kani::any();let d:u32=kani::any();let _=add(a,c,&mut t);let _=add(b,d,&mut u);assert!(t.len<=32);assert_eq!(t.len,u.len);for i in 0..32 {assert_eq!(t.events[i],u.events[i]);}}
#[kani::proof]
#[kani::unwind(40)]
fn two_run_sub() { let mut t=Trace::new(); let mut u=Trace::new(); let a:u32=kani::any();let b:u32=kani::any();let c:u32=kani::any();let d:u32=kani::any();let _=sub(a,c,&mut t);let _=sub(b,d,&mut u);assert!(t.len<=32);assert_eq!(t.len,u.len);for i in 0..32 {assert_eq!(t.events[i],u.events[i]);}}
#[kani::proof]
#[kani::unwind(40)]
fn two_run_neg() { let mut t=Trace::new(); let mut u=Trace::new(); let a:u32=kani::any();let b:u32=kani::any();let _=neg(a,&mut t);let _=neg(b,&mut u);assert!(t.len<=32);assert_eq!(t.len,u.len);for i in 0..32 {assert_eq!(t.events[i],u.events[i]);}}
#[kani::proof]
#[kani::unwind(40)]
fn two_run_is_zero() { let mut t=Trace::new(); let mut u=Trace::new(); let a:u32=kani::any();let b:u32=kani::any();let _=is_zero(a,&mut t);let _=is_zero(b,&mut u);assert!(t.len<=32);assert_eq!(t.len,u.len);for i in 0..32 {assert_eq!(t.events[i],u.events[i]);}}
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

// Replay checks compare every emitted event online, then require equal length.
// The record/replay branch is public harness instrumentation, not a field event.
#[cfg(kani)] mod tower_traces {
use super::*;
use super::instrumented::{self,Trace};
static mut TRACE: Trace = Trace::new();
fn add(a:u32,b:u32)->u32 {unsafe{instrumented::add(a,b,&mut TRACE)}}
fn sub(a:u32,b:u32)->u32 {unsafe{instrumented::sub(a,b,&mut TRACE)}}
fn neg(a:u32)->u32 {unsafe{instrumented::neg(a,&mut TRACE)}}
fn zero(a:u32)->bool {unsafe{instrumented::is_zero(a,&mut TRACE)}}
fn reduce(a:u64)->u32 {unsafe{instrumented::reduce64(a,&mut TRACE)}}
fn limbs()->[u32;8] {let x:[u32;8]=kani::any();for a in x {kani::assume(a<field::P);} x}
#[kani::proof]
#[kani::unwind(12)]
#[kani::stub(field::ct::add, add)]
#[kani::stub(field::ct::sub, sub)]
#[kani::stub(field::ct::neg, neg)]
#[kani::stub(field::ct::is_zero, zero)]
#[kani::stub(field::ct::reduce64, reduce)]
fn m_add() {let x=field::WideExact::from_limbs(limbs()).unwrap();let x=x.c0().c0.a;let y=field::WideExact::from_limbs(limbs()).unwrap();let y=y.c0().c0.a;let r=field::WideExact::from_limbs(limbs()).unwrap();let r=r.c0().c0.a;let t=field::WideExact::from_limbs(limbs()).unwrap();let t=t.c0().c0.a;unsafe{TRACE=Trace::new();}let _=x.add(y);let n=unsafe{TRACE.len};unsafe{TRACE.len=0;TRACE.replay=true;}let _=r.add(t);assert_eq!(unsafe{TRACE.len},n);}
#[kani::proof]
#[kani::unwind(12)]
#[kani::stub(field::ct::add, add)]
#[kani::stub(field::ct::sub, sub)]
#[kani::stub(field::ct::neg, neg)]
#[kani::stub(field::ct::is_zero, zero)]
#[kani::stub(field::ct::reduce64, reduce)]
fn m_sub() {let x=field::WideExact::from_limbs(limbs()).unwrap();let x=x.c0().c0.a;let y=field::WideExact::from_limbs(limbs()).unwrap();let y=y.c0().c0.a;let r=field::WideExact::from_limbs(limbs()).unwrap();let r=r.c0().c0.a;let t=field::WideExact::from_limbs(limbs()).unwrap();let t=t.c0().c0.a;unsafe{TRACE=Trace::new();}let _=x.sub(y);let n=unsafe{TRACE.len};unsafe{TRACE.len=0;TRACE.replay=true;}let _=r.sub(t);assert_eq!(unsafe{TRACE.len},n);}
#[kani::proof]
#[kani::unwind(12)]
#[kani::stub(field::ct::add, add)]
#[kani::stub(field::ct::sub, sub)]
#[kani::stub(field::ct::neg, neg)]
#[kani::stub(field::ct::is_zero, zero)]
#[kani::stub(field::ct::reduce64, reduce)]
fn m_neg() {let x=field::WideExact::from_limbs(limbs()).unwrap();let x=x.c0().c0.a;let y=field::WideExact::from_limbs(limbs()).unwrap();let y=y.c0().c0.a;let r=field::WideExact::from_limbs(limbs()).unwrap();let r=r.c0().c0.a;let t=field::WideExact::from_limbs(limbs()).unwrap();let t=t.c0().c0.a;unsafe{TRACE=Trace::new();}let _=x.neg();let n=unsafe{TRACE.len};unsafe{TRACE.len=0;TRACE.replay=true;}let _=r.neg();assert_eq!(unsafe{TRACE.len},n);}
#[kani::proof]
#[kani::unwind(12)]
#[kani::stub(field::ct::add, add)]
#[kani::stub(field::ct::sub, sub)]
#[kani::stub(field::ct::neg, neg)]
#[kani::stub(field::ct::is_zero, zero)]
#[kani::stub(field::ct::reduce64, reduce)]
fn m_is_zero() {let x=field::WideExact::from_limbs(limbs()).unwrap();let x=x.c0().c0.a;let y=field::WideExact::from_limbs(limbs()).unwrap();let y=y.c0().c0.a;let r=field::WideExact::from_limbs(limbs()).unwrap();let r=r.c0().c0.a;let t=field::WideExact::from_limbs(limbs()).unwrap();let t=t.c0().c0.a;unsafe{TRACE=Trace::new();}let _=x.is_zero();let n=unsafe{TRACE.len};unsafe{TRACE.len=0;TRACE.replay=true;}let _=r.is_zero();assert_eq!(unsafe{TRACE.len},n);}
#[kani::proof]
#[kani::unwind(12)]
#[kani::stub(field::ct::add, add)]
#[kani::stub(field::ct::sub, sub)]
#[kani::stub(field::ct::neg, neg)]
#[kani::stub(field::ct::is_zero, zero)]
#[kani::stub(field::ct::reduce64, reduce)]
fn m_mul() {let x=field::WideExact::from_limbs(limbs()).unwrap();let x=x.c0().c0.a;let y=field::WideExact::from_limbs(limbs()).unwrap();let y=y.c0().c0.a;let r=field::WideExact::from_limbs(limbs()).unwrap();let r=r.c0().c0.a;let t=field::WideExact::from_limbs(limbs()).unwrap();let t=t.c0().c0.a;unsafe{TRACE=Trace::new();}let _=x.mul(y);let n=unsafe{TRACE.len};unsafe{TRACE.len=0;TRACE.replay=true;}let _=r.mul(t);assert_eq!(unsafe{TRACE.len},n);}
#[kani::proof]
#[kani::unwind(12)]
#[kani::stub(field::ct::add, add)]
#[kani::stub(field::ct::sub, sub)]
#[kani::stub(field::ct::neg, neg)]
#[kani::stub(field::ct::is_zero, zero)]
#[kani::stub(field::ct::reduce64, reduce)]
fn cm_add() {let x=field::WideExact::from_limbs(limbs()).unwrap();let x=x.c0().c0;let y=field::WideExact::from_limbs(limbs()).unwrap();let y=y.c0().c0;let r=field::WideExact::from_limbs(limbs()).unwrap();let r=r.c0().c0;let t=field::WideExact::from_limbs(limbs()).unwrap();let t=t.c0().c0;unsafe{TRACE=Trace::new();}let _=x.add(y);let n=unsafe{TRACE.len};unsafe{TRACE.len=0;TRACE.replay=true;}let _=r.add(t);assert_eq!(unsafe{TRACE.len},n);}
#[kani::proof]
#[kani::unwind(12)]
#[kani::stub(field::ct::add, add)]
#[kani::stub(field::ct::sub, sub)]
#[kani::stub(field::ct::neg, neg)]
#[kani::stub(field::ct::is_zero, zero)]
#[kani::stub(field::ct::reduce64, reduce)]
fn cm_sub() {let x=field::WideExact::from_limbs(limbs()).unwrap();let x=x.c0().c0;let y=field::WideExact::from_limbs(limbs()).unwrap();let y=y.c0().c0;let r=field::WideExact::from_limbs(limbs()).unwrap();let r=r.c0().c0;let t=field::WideExact::from_limbs(limbs()).unwrap();let t=t.c0().c0;unsafe{TRACE=Trace::new();}let _=x.sub(y);let n=unsafe{TRACE.len};unsafe{TRACE.len=0;TRACE.replay=true;}let _=r.sub(t);assert_eq!(unsafe{TRACE.len},n);}
#[kani::proof]
#[kani::unwind(12)]
#[kani::stub(field::ct::add, add)]
#[kani::stub(field::ct::sub, sub)]
#[kani::stub(field::ct::neg, neg)]
#[kani::stub(field::ct::is_zero, zero)]
#[kani::stub(field::ct::reduce64, reduce)]
fn cm_neg() {let x=field::WideExact::from_limbs(limbs()).unwrap();let x=x.c0().c0;let y=field::WideExact::from_limbs(limbs()).unwrap();let y=y.c0().c0;let r=field::WideExact::from_limbs(limbs()).unwrap();let r=r.c0().c0;let t=field::WideExact::from_limbs(limbs()).unwrap();let t=t.c0().c0;unsafe{TRACE=Trace::new();}let _=x.neg();let n=unsafe{TRACE.len};unsafe{TRACE.len=0;TRACE.replay=true;}let _=r.neg();assert_eq!(unsafe{TRACE.len},n);}
#[kani::proof]
#[kani::unwind(12)]
#[kani::stub(field::ct::add, add)]
#[kani::stub(field::ct::sub, sub)]
#[kani::stub(field::ct::neg, neg)]
#[kani::stub(field::ct::is_zero, zero)]
#[kani::stub(field::ct::reduce64, reduce)]
fn cm_is_zero() {let x=field::WideExact::from_limbs(limbs()).unwrap();let x=x.c0().c0;let y=field::WideExact::from_limbs(limbs()).unwrap();let y=y.c0().c0;let r=field::WideExact::from_limbs(limbs()).unwrap();let r=r.c0().c0;let t=field::WideExact::from_limbs(limbs()).unwrap();let t=t.c0().c0;unsafe{TRACE=Trace::new();}let _=x.is_zero();let n=unsafe{TRACE.len};unsafe{TRACE.len=0;TRACE.replay=true;}let _=r.is_zero();assert_eq!(unsafe{TRACE.len},n);}
#[kani::proof]
#[kani::unwind(12)]
#[kani::stub(field::ct::add, add)]
#[kani::stub(field::ct::sub, sub)]
#[kani::stub(field::ct::neg, neg)]
#[kani::stub(field::ct::is_zero, zero)]
#[kani::stub(field::ct::reduce64, reduce)]
fn cm_mul() {let x=field::WideExact::from_limbs(limbs()).unwrap();let x=x.c0().c0;let y=field::WideExact::from_limbs(limbs()).unwrap();let y=y.c0().c0;let r=field::WideExact::from_limbs(limbs()).unwrap();let r=r.c0().c0;let t=field::WideExact::from_limbs(limbs()).unwrap();let t=t.c0().c0;unsafe{TRACE=Trace::new();}let _=x.mul(y);let n=unsafe{TRACE.len};unsafe{TRACE.len=0;TRACE.replay=true;}let _=r.mul(t);assert_eq!(unsafe{TRACE.len},n);}
#[kani::proof]
#[kani::unwind(12)]
#[kani::stub(field::ct::add, add)]
#[kani::stub(field::ct::sub, sub)]
#[kani::stub(field::ct::neg, neg)]
#[kani::stub(field::ct::is_zero, zero)]
#[kani::stub(field::ct::reduce64, reduce)]
fn cm_square() {let x=field::WideExact::from_limbs(limbs()).unwrap();let x=x.c0().c0;let y=field::WideExact::from_limbs(limbs()).unwrap();let y=y.c0().c0;let r=field::WideExact::from_limbs(limbs()).unwrap();let r=r.c0().c0;let t=field::WideExact::from_limbs(limbs()).unwrap();let t=t.c0().c0;unsafe{TRACE=Trace::new();}let _=x.square();let n=unsafe{TRACE.len};unsafe{TRACE.len=0;TRACE.replay=true;}let _=r.square();assert_eq!(unsafe{TRACE.len},n);}
#[kani::proof]
#[kani::unwind(12)]
#[kani::stub(field::ct::add, add)]
#[kani::stub(field::ct::sub, sub)]
#[kani::stub(field::ct::neg, neg)]
#[kani::stub(field::ct::is_zero, zero)]
#[kani::stub(field::ct::reduce64, reduce)]
fn qm_add() {let x=field::WideExact::from_limbs(limbs()).unwrap();let x=x.c0();let y=field::WideExact::from_limbs(limbs()).unwrap();let y=y.c0();let r=field::WideExact::from_limbs(limbs()).unwrap();let r=r.c0();let t=field::WideExact::from_limbs(limbs()).unwrap();let t=t.c0();unsafe{TRACE=Trace::new();}let _=x.add(y);let n=unsafe{TRACE.len};unsafe{TRACE.len=0;TRACE.replay=true;}let _=r.add(t);assert_eq!(unsafe{TRACE.len},n);}
#[kani::proof]
#[kani::unwind(12)]
#[kani::stub(field::ct::add, add)]
#[kani::stub(field::ct::sub, sub)]
#[kani::stub(field::ct::neg, neg)]
#[kani::stub(field::ct::is_zero, zero)]
#[kani::stub(field::ct::reduce64, reduce)]
fn qm_sub() {let x=field::WideExact::from_limbs(limbs()).unwrap();let x=x.c0();let y=field::WideExact::from_limbs(limbs()).unwrap();let y=y.c0();let r=field::WideExact::from_limbs(limbs()).unwrap();let r=r.c0();let t=field::WideExact::from_limbs(limbs()).unwrap();let t=t.c0();unsafe{TRACE=Trace::new();}let _=x.sub(y);let n=unsafe{TRACE.len};unsafe{TRACE.len=0;TRACE.replay=true;}let _=r.sub(t);assert_eq!(unsafe{TRACE.len},n);}
#[kani::proof]
#[kani::unwind(12)]
#[kani::stub(field::ct::add, add)]
#[kani::stub(field::ct::sub, sub)]
#[kani::stub(field::ct::neg, neg)]
#[kani::stub(field::ct::is_zero, zero)]
#[kani::stub(field::ct::reduce64, reduce)]
fn qm_neg() {let x=field::WideExact::from_limbs(limbs()).unwrap();let x=x.c0();let y=field::WideExact::from_limbs(limbs()).unwrap();let y=y.c0();let r=field::WideExact::from_limbs(limbs()).unwrap();let r=r.c0();let t=field::WideExact::from_limbs(limbs()).unwrap();let t=t.c0();unsafe{TRACE=Trace::new();}let _=x.neg();let n=unsafe{TRACE.len};unsafe{TRACE.len=0;TRACE.replay=true;}let _=r.neg();assert_eq!(unsafe{TRACE.len},n);}
#[kani::proof]
#[kani::unwind(12)]
#[kani::stub(field::ct::add, add)]
#[kani::stub(field::ct::sub, sub)]
#[kani::stub(field::ct::neg, neg)]
#[kani::stub(field::ct::is_zero, zero)]
#[kani::stub(field::ct::reduce64, reduce)]
fn qm_is_zero() {let x=field::WideExact::from_limbs(limbs()).unwrap();let x=x.c0();let y=field::WideExact::from_limbs(limbs()).unwrap();let y=y.c0();let r=field::WideExact::from_limbs(limbs()).unwrap();let r=r.c0();let t=field::WideExact::from_limbs(limbs()).unwrap();let t=t.c0();unsafe{TRACE=Trace::new();}let _=x.is_zero();let n=unsafe{TRACE.len};unsafe{TRACE.len=0;TRACE.replay=true;}let _=r.is_zero();assert_eq!(unsafe{TRACE.len},n);}
#[kani::proof]
#[kani::unwind(12)]
#[kani::stub(field::ct::add, add)]
#[kani::stub(field::ct::sub, sub)]
#[kani::stub(field::ct::neg, neg)]
#[kani::stub(field::ct::is_zero, zero)]
#[kani::stub(field::ct::reduce64, reduce)]
fn qm_mul() {let x=field::WideExact::from_limbs(limbs()).unwrap();let x=x.c0();let y=field::WideExact::from_limbs(limbs()).unwrap();let y=y.c0();let r=field::WideExact::from_limbs(limbs()).unwrap();let r=r.c0();let t=field::WideExact::from_limbs(limbs()).unwrap();let t=t.c0();unsafe{TRACE=Trace::new();}let _=x.mul(y);let n=unsafe{TRACE.len};unsafe{TRACE.len=0;TRACE.replay=true;}let _=r.mul(t);assert_eq!(unsafe{TRACE.len},n);}
#[kani::proof]
#[kani::unwind(12)]
#[kani::stub(field::ct::add, add)]
#[kani::stub(field::ct::sub, sub)]
#[kani::stub(field::ct::neg, neg)]
#[kani::stub(field::ct::is_zero, zero)]
#[kani::stub(field::ct::reduce64, reduce)]
fn qm_square() {let x=field::WideExact::from_limbs(limbs()).unwrap();let x=x.c0();let y=field::WideExact::from_limbs(limbs()).unwrap();let y=y.c0();let r=field::WideExact::from_limbs(limbs()).unwrap();let r=r.c0();let t=field::WideExact::from_limbs(limbs()).unwrap();let t=t.c0();unsafe{TRACE=Trace::new();}let _=x.square();let n=unsafe{TRACE.len};unsafe{TRACE.len=0;TRACE.replay=true;}let _=r.square();assert_eq!(unsafe{TRACE.len},n);}
#[kani::proof]
#[kani::unwind(12)]
#[kani::stub(field::ct::add, add)]
#[kani::stub(field::ct::sub, sub)]
#[kani::stub(field::ct::neg, neg)]
#[kani::stub(field::ct::is_zero, zero)]
#[kani::stub(field::ct::reduce64, reduce)]
fn wide_add() {let x=field::WideExact::from_limbs(limbs()).unwrap();let y=field::WideExact::from_limbs(limbs()).unwrap();let r=field::WideExact::from_limbs(limbs()).unwrap();let t=field::WideExact::from_limbs(limbs()).unwrap();unsafe{TRACE=Trace::new();}let _=x.add(y);let n=unsafe{TRACE.len};unsafe{TRACE.len=0;TRACE.replay=true;}let _=r.add(t);assert_eq!(unsafe{TRACE.len},n);}
#[kani::proof]
#[kani::unwind(12)]
#[kani::stub(field::ct::add, add)]
#[kani::stub(field::ct::sub, sub)]
#[kani::stub(field::ct::neg, neg)]
#[kani::stub(field::ct::is_zero, zero)]
#[kani::stub(field::ct::reduce64, reduce)]
fn wide_sub() {let x=field::WideExact::from_limbs(limbs()).unwrap();let y=field::WideExact::from_limbs(limbs()).unwrap();let r=field::WideExact::from_limbs(limbs()).unwrap();let t=field::WideExact::from_limbs(limbs()).unwrap();unsafe{TRACE=Trace::new();}let _=x.sub(y);let n=unsafe{TRACE.len};unsafe{TRACE.len=0;TRACE.replay=true;}let _=r.sub(t);assert_eq!(unsafe{TRACE.len},n);}
#[kani::proof]
#[kani::unwind(12)]
#[kani::stub(field::ct::add, add)]
#[kani::stub(field::ct::sub, sub)]
#[kani::stub(field::ct::neg, neg)]
#[kani::stub(field::ct::is_zero, zero)]
#[kani::stub(field::ct::reduce64, reduce)]
fn wide_neg() {let x=field::WideExact::from_limbs(limbs()).unwrap();let y=field::WideExact::from_limbs(limbs()).unwrap();let r=field::WideExact::from_limbs(limbs()).unwrap();let t=field::WideExact::from_limbs(limbs()).unwrap();unsafe{TRACE=Trace::new();}let _=x.neg();let n=unsafe{TRACE.len};unsafe{TRACE.len=0;TRACE.replay=true;}let _=r.neg();assert_eq!(unsafe{TRACE.len},n);}
#[kani::proof]
#[kani::unwind(12)]
#[kani::stub(field::ct::add, add)]
#[kani::stub(field::ct::sub, sub)]
#[kani::stub(field::ct::neg, neg)]
#[kani::stub(field::ct::is_zero, zero)]
#[kani::stub(field::ct::reduce64, reduce)]
fn wide_is_zero() {let x=field::WideExact::from_limbs(limbs()).unwrap();let y=field::WideExact::from_limbs(limbs()).unwrap();let r=field::WideExact::from_limbs(limbs()).unwrap();let t=field::WideExact::from_limbs(limbs()).unwrap();unsafe{TRACE=Trace::new();}let _=x.is_zero();let n=unsafe{TRACE.len};unsafe{TRACE.len=0;TRACE.replay=true;}let _=r.is_zero();assert_eq!(unsafe{TRACE.len},n);}
#[kani::proof]
#[kani::unwind(12)]
#[kani::stub(field::ct::add, add)]
#[kani::stub(field::ct::sub, sub)]
#[kani::stub(field::ct::neg, neg)]
#[kani::stub(field::ct::is_zero, zero)]
#[kani::stub(field::ct::reduce64, reduce)]
fn wide_mul() {let x=field::WideExact::from_limbs(limbs()).unwrap();let y=field::WideExact::from_limbs(limbs()).unwrap();let r=field::WideExact::from_limbs(limbs()).unwrap();let t=field::WideExact::from_limbs(limbs()).unwrap();unsafe{TRACE=Trace::new();}let _=x.mul(y);let n=unsafe{TRACE.len};unsafe{TRACE.len=0;TRACE.replay=true;}let _=r.mul(t);assert_eq!(unsafe{TRACE.len},n);}
#[kani::proof]
#[kani::unwind(12)]
#[kani::stub(field::ct::add, add)]
#[kani::stub(field::ct::sub, sub)]
#[kani::stub(field::ct::neg, neg)]
#[kani::stub(field::ct::is_zero, zero)]
#[kani::stub(field::ct::reduce64, reduce)]
fn wide_square() {let x=field::WideExact::from_limbs(limbs()).unwrap();let y=field::WideExact::from_limbs(limbs()).unwrap();let r=field::WideExact::from_limbs(limbs()).unwrap();let t=field::WideExact::from_limbs(limbs()).unwrap();unsafe{TRACE=Trace::new();}let _=x.square();let n=unsafe{TRACE.len};unsafe{TRACE.len=0;TRACE.replay=true;}let _=r.square();assert_eq!(unsafe{TRACE.len},n);}
#[kani::proof]
#[kani::unwind(12)]
#[kani::stub(field::ct::add, add)]
#[kani::stub(field::ct::sub, sub)]
#[kani::stub(field::ct::neg, neg)]
#[kani::stub(field::ct::is_zero, zero)]
#[kani::stub(field::ct::reduce64, reduce)]
fn mixed_cm_mul_m31() {let x=field::WideExact::from_limbs(limbs()).unwrap();let x=x.c0().c0;let y=field::WideExact::from_limbs(limbs()).unwrap();let y=y.c0().c0;let r=field::WideExact::from_limbs(limbs()).unwrap();let r=r.c0().c0;let t=field::WideExact::from_limbs(limbs()).unwrap();let t=t.c0().c0;unsafe{TRACE=Trace::new();}let _=x.mul_m31(y.a);let n=unsafe{TRACE.len};unsafe{TRACE.len=0;TRACE.replay=true;}let _=r.mul_m31(t.a);assert_eq!(unsafe{TRACE.len},n);}
#[kani::proof]
#[kani::unwind(12)]
#[kani::stub(field::ct::add, add)]
#[kani::stub(field::ct::sub, sub)]
#[kani::stub(field::ct::neg, neg)]
#[kani::stub(field::ct::is_zero, zero)]
#[kani::stub(field::ct::reduce64, reduce)]
fn mixed_qm_mul_m31() {let x=field::WideExact::from_limbs(limbs()).unwrap();let x=x.c0();let y=field::WideExact::from_limbs(limbs()).unwrap();let y=y.c0();let r=field::WideExact::from_limbs(limbs()).unwrap();let r=r.c0();let t=field::WideExact::from_limbs(limbs()).unwrap();let t=t.c0();unsafe{TRACE=Trace::new();}let _=x.mul_m31(y.c0.a);let n=unsafe{TRACE.len};unsafe{TRACE.len=0;TRACE.replay=true;}let _=r.mul_m31(t.c0.a);assert_eq!(unsafe{TRACE.len},n);}
#[kani::proof]
#[kani::unwind(12)]
#[kani::stub(field::ct::add, add)]
#[kani::stub(field::ct::sub, sub)]
#[kani::stub(field::ct::neg, neg)]
#[kani::stub(field::ct::is_zero, zero)]
#[kani::stub(field::ct::reduce64, reduce)]
fn mixed_qm_mul_cm31() {let x=field::WideExact::from_limbs(limbs()).unwrap();let x=x.c0();let y=field::WideExact::from_limbs(limbs()).unwrap();let y=y.c0();let r=field::WideExact::from_limbs(limbs()).unwrap();let r=r.c0();let t=field::WideExact::from_limbs(limbs()).unwrap();let t=t.c0();unsafe{TRACE=Trace::new();}let _=x.mul_cm31(y.c0);let n=unsafe{TRACE.len};unsafe{TRACE.len=0;TRACE.replay=true;}let _=r.mul_cm31(t.c0);assert_eq!(unsafe{TRACE.len},n);}
#[kani::proof]
#[kani::unwind(12)]
#[kani::stub(field::ct::add, add)]
#[kani::stub(field::ct::sub, sub)]
#[kani::stub(field::ct::neg, neg)]
#[kani::stub(field::ct::is_zero, zero)]
#[kani::stub(field::ct::reduce64, reduce)]
fn mixed_wide_mul_m31() {let x=field::WideExact::from_limbs(limbs()).unwrap();let y=field::WideExact::from_limbs(limbs()).unwrap();let r=field::WideExact::from_limbs(limbs()).unwrap();let t=field::WideExact::from_limbs(limbs()).unwrap();unsafe{TRACE=Trace::new();}let _=x.mul_m31(y.c0().c0.a);let n=unsafe{TRACE.len};unsafe{TRACE.len=0;TRACE.replay=true;}let _=r.mul_m31(t.c0().c0.a);assert_eq!(unsafe{TRACE.len},n);}
#[kani::proof]
#[kani::unwind(12)]
#[kani::stub(field::ct::add, add)]
#[kani::stub(field::ct::sub, sub)]
#[kani::stub(field::ct::neg, neg)]
#[kani::stub(field::ct::is_zero, zero)]
#[kani::stub(field::ct::reduce64, reduce)]
fn mixed_wide_mul_qm31() {let x=field::WideExact::from_limbs(limbs()).unwrap();let y=field::WideExact::from_limbs(limbs()).unwrap();let r=field::WideExact::from_limbs(limbs()).unwrap();let t=field::WideExact::from_limbs(limbs()).unwrap();unsafe{TRACE=Trace::new();}let _=x.mul_qm31(y.c0());let n=unsafe{TRACE.len};unsafe{TRACE.len=0;TRACE.replay=true;}let _=r.mul_qm31(t.c0());assert_eq!(unsafe{TRACE.len},n);}
}

// Parametric composition: the old run chooses arbitrary canonical leaf outputs;
// the candidate must replay the same operation/operands and return those outputs.
// Leaf equivalence and canonical-output gates discharge this abstraction.
#[cfg(kani)] mod parametric {
use super::*;
struct Oracle {op:[u8;512],a:[u64;512],b:[u64;512],out:[u32;512],n:usize,replay:bool}
impl Oracle { const fn new()->Self {Self{op:[0;512],a:[0;512],b:[0;512],out:[0;512],n:0,replay:false}} }
static mut O:Oracle=Oracle::new();
fn leaf(op:u8,a:u64,b:u64)->u32 {unsafe{
 let n=O.n;O.n+=1;
 if O.replay {assert_eq!(O.op[n],op);assert_eq!(O.a[n],a);assert_eq!(O.b[n],b);O.out[n]}
 else {let v:u32=kani::any();kani::assume(v<field::P);O.op[n]=op;O.a[n]=a;O.b[n]=b;O.out[n]=v;v}
}}
fn limbs()->[u32;8] {let a:[u32;8]=kani::any();for x in a {kani::assume(x<field::P);} a}
fn c_add(a:field::M31,b:field::M31)->field::M31 {assert!(a.0<field::P);assert!(b.0<field::P);field::M31(leaf(1,a.0 as u64,b.0 as u64))}
fn c_sub(a:field::M31,b:field::M31)->field::M31 {assert!(a.0<field::P);assert!(b.0<field::P);field::M31(leaf(2,a.0 as u64,b.0 as u64))}
fn c_neg(a:field::M31)->field::M31 {assert!(a.0<field::P);field::M31(leaf(3,a.0 as u64,0))}
fn c_mul(a:field::M31,b:field::M31)->field::M31 {assert!(a.0<field::P);assert!(b.0<field::P);field::M31(leaf(4,a.0 as u64,b.0 as u64))}
fn c_reduce(a:u64)->field::M31 {field::M31(leaf(5,a,0))}
fn r_add(a:reference::M31,b:reference::M31)->reference::M31 {assert!(a.0<field::P);assert!(b.0<field::P);reference::M31(leaf(1,a.0 as u64,b.0 as u64))}
fn r_sub(a:reference::M31,b:reference::M31)->reference::M31 {assert!(a.0<field::P);assert!(b.0<field::P);reference::M31(leaf(2,a.0 as u64,b.0 as u64))}
fn r_neg(a:reference::M31)->reference::M31 {assert!(a.0<field::P);reference::M31(leaf(3,a.0 as u64,0))}
fn r_mul(a:reference::M31,b:reference::M31)->reference::M31 {assert!(a.0<field::P);assert!(b.0<field::P);reference::M31(leaf(4,a.0 as u64,b.0 as u64))}
fn r_reduce(a:u64)->reference::M31 {reference::M31(leaf(5,a,0))}
fn c_cm_mul(a:field::CM31,b:field::CM31)->field::CM31 {field::CM31 {a:field::M31(leaf(10,a.a.0 as u64,b.a.0 as u64)),b:field::M31(leaf(11,a.b.0 as u64,b.b.0 as u64))}}
fn c_cm_square(a:field::CM31)->field::CM31 {field::CM31 {a:field::M31(leaf(12,a.a.0 as u64,0 as u64)),b:field::M31(leaf(13,a.b.0 as u64,0 as u64))}}
fn c_cm_mul_m31(a:field::CM31,b:field::M31)->field::CM31 {field::CM31 {a:field::M31(leaf(14,a.a.0 as u64,b.0 as u64)),b:field::M31(leaf(15,a.b.0 as u64,b.0 as u64))}}
fn c_qm_mul(a:field::QM31,b:field::QM31)->field::QM31 {field::QM31{c0:field::CM31{a:field::M31(leaf(20,a.c0.a.0 as u64,b.c0.a.0 as u64)),b:field::M31(leaf(21,a.c0.b.0 as u64,b.c0.b.0 as u64))},c1:field::CM31{a:field::M31(leaf(22,a.c1.a.0 as u64,b.c1.a.0 as u64)),b:field::M31(leaf(23,a.c1.b.0 as u64,b.c1.b.0 as u64))}}}
fn c_qm_square(a:field::QM31)->field::QM31 {field::QM31{c0:field::CM31{a:field::M31(leaf(24,a.c0.a.0 as u64,0 as u64)),b:field::M31(leaf(25,a.c0.b.0 as u64,0 as u64))},c1:field::CM31{a:field::M31(leaf(26,a.c1.a.0 as u64,0 as u64)),b:field::M31(leaf(27,a.c1.b.0 as u64,0 as u64))}}}
fn c_qm_mul_m31(a:field::QM31,b:field::M31)->field::QM31 {field::QM31{c0:field::CM31{a:field::M31(leaf(28,a.c0.a.0 as u64,b.0 as u64)),b:field::M31(leaf(29,a.c0.b.0 as u64,b.0 as u64))},c1:field::CM31{a:field::M31(leaf(30,a.c1.a.0 as u64,b.0 as u64)),b:field::M31(leaf(31,a.c1.b.0 as u64,b.0 as u64))}}}
fn r_cm_mul(a:reference::CM31,b:reference::CM31)->reference::CM31 {reference::CM31 {a:reference::M31(leaf(10,a.a.0 as u64,b.a.0 as u64)),b:reference::M31(leaf(11,a.b.0 as u64,b.b.0 as u64))}}
fn r_cm_square(a:reference::CM31)->reference::CM31 {reference::CM31 {a:reference::M31(leaf(12,a.a.0 as u64,0 as u64)),b:reference::M31(leaf(13,a.b.0 as u64,0 as u64))}}
fn r_cm_mul_m31(a:reference::CM31,b:reference::M31)->reference::CM31 {reference::CM31 {a:reference::M31(leaf(14,a.a.0 as u64,b.0 as u64)),b:reference::M31(leaf(15,a.b.0 as u64,b.0 as u64))}}
fn r_qm_mul(a:reference::QM31,b:reference::QM31)->reference::QM31 {reference::QM31{c0:reference::CM31{a:reference::M31(leaf(20,a.c0.a.0 as u64,b.c0.a.0 as u64)),b:reference::M31(leaf(21,a.c0.b.0 as u64,b.c0.b.0 as u64))},c1:reference::CM31{a:reference::M31(leaf(22,a.c1.a.0 as u64,b.c1.a.0 as u64)),b:reference::M31(leaf(23,a.c1.b.0 as u64,b.c1.b.0 as u64))}}}
fn r_qm_square(a:reference::QM31)->reference::QM31 {reference::QM31{c0:reference::CM31{a:reference::M31(leaf(24,a.c0.a.0 as u64,0 as u64)),b:reference::M31(leaf(25,a.c0.b.0 as u64,0 as u64))},c1:reference::CM31{a:reference::M31(leaf(26,a.c1.a.0 as u64,0 as u64)),b:reference::M31(leaf(27,a.c1.b.0 as u64,0 as u64))}}}
fn r_qm_mul_m31(a:reference::QM31,b:reference::M31)->reference::QM31 {reference::QM31{c0:reference::CM31{a:reference::M31(leaf(28,a.c0.a.0 as u64,b.0 as u64)),b:reference::M31(leaf(29,a.c0.b.0 as u64,b.0 as u64))},c1:reference::CM31{a:reference::M31(leaf(30,a.c1.a.0 as u64,b.0 as u64)),b:reference::M31(leaf(31,a.c1.b.0 as u64,b.0 as u64))}}}
#[kani::proof]
#[kani::unwind(40)]
#[kani::stub(field::M31::add, c_add)]
#[kani::stub(field::M31::sub, c_sub)]
#[kani::stub(field::M31::neg, c_neg)]
#[kani::stub(field::M31::mul, c_mul)]
#[kani::stub(field::M31::reduce_u64, c_reduce)]
#[kani::stub(reference::M31::add, r_add)]
#[kani::stub(reference::M31::sub, r_sub)]
#[kani::stub(reference::M31::neg, r_neg)]
#[kani::stub(reference::M31::mul, r_mul)]
#[kani::stub(reference::M31::reduce_u64, r_reduce)]
fn cm_mul() {let a=limbs();let b=limbs();let x=field::WideExact::from_limbs(a).unwrap();let y=field::WideExact::from_limbs(b).unwrap();let r=reference::WideExact::from_limbs(a).unwrap();let t=reference::WideExact::from_limbs(b).unwrap();let x=x.c0().c0;let y=y.c0().c0;let r=r.c0().c0;let t=t.c0().c0;unsafe{O=Oracle::new();}let expected=r.mul(t);let n=unsafe{O.n};unsafe{O.n=0;O.replay=true;}let actual=x.mul(y);assert_eq!(unsafe{O.n},n);let mut aa=[0u8;8];let mut bb=[0u8;8];actual.write_le_bytes(&mut aa);expected.write_le_bytes(&mut bb);assert_eq!(aa,bb);}
#[kani::proof]
#[kani::unwind(40)]
#[kani::stub(field::M31::add, c_add)]
#[kani::stub(field::M31::sub, c_sub)]
#[kani::stub(field::M31::neg, c_neg)]
#[kani::stub(field::M31::mul, c_mul)]
#[kani::stub(field::M31::reduce_u64, c_reduce)]
#[kani::stub(reference::M31::add, r_add)]
#[kani::stub(reference::M31::sub, r_sub)]
#[kani::stub(reference::M31::neg, r_neg)]
#[kani::stub(reference::M31::mul, r_mul)]
#[kani::stub(reference::M31::reduce_u64, r_reduce)]
fn cm_square() {let a=limbs();let b=limbs();let x=field::WideExact::from_limbs(a).unwrap();let y=field::WideExact::from_limbs(b).unwrap();let r=reference::WideExact::from_limbs(a).unwrap();let t=reference::WideExact::from_limbs(b).unwrap();let x=x.c0().c0;let y=y.c0().c0;let r=r.c0().c0;let t=t.c0().c0;unsafe{O=Oracle::new();}let expected=r.square();let n=unsafe{O.n};unsafe{O.n=0;O.replay=true;}let actual=x.square();assert_eq!(unsafe{O.n},n);let mut aa=[0u8;8];let mut bb=[0u8;8];actual.write_le_bytes(&mut aa);expected.write_le_bytes(&mut bb);assert_eq!(aa,bb);}
#[kani::proof]
#[kani::unwind(40)]
#[kani::stub(field::M31::add, c_add)]
#[kani::stub(field::M31::sub, c_sub)]
#[kani::stub(field::M31::neg, c_neg)]
#[kani::stub(field::M31::mul, c_mul)]
#[kani::stub(field::M31::reduce_u64, c_reduce)]
#[kani::stub(reference::M31::add, r_add)]
#[kani::stub(reference::M31::sub, r_sub)]
#[kani::stub(reference::M31::neg, r_neg)]
#[kani::stub(reference::M31::mul, r_mul)]
#[kani::stub(reference::M31::reduce_u64, r_reduce)]
fn cm_mul_m31() {let a=limbs();let b=limbs();let x=field::WideExact::from_limbs(a).unwrap();let y=field::WideExact::from_limbs(b).unwrap();let r=reference::WideExact::from_limbs(a).unwrap();let t=reference::WideExact::from_limbs(b).unwrap();let x=x.c0().c0;let y=y.c0().c0;let r=r.c0().c0;let t=t.c0().c0;unsafe{O=Oracle::new();}let expected=r.mul_m31(t.a);let n=unsafe{O.n};unsafe{O.n=0;O.replay=true;}let actual=x.mul_m31(y.a);assert_eq!(unsafe{O.n},n);let mut aa=[0u8;8];let mut bb=[0u8;8];actual.write_le_bytes(&mut aa);expected.write_le_bytes(&mut bb);assert_eq!(aa,bb);}
#[kani::proof]
#[kani::unwind(40)]
#[kani::stub(field::M31::add, c_add)]
#[kani::stub(field::M31::sub, c_sub)]
#[kani::stub(field::M31::neg, c_neg)]
#[kani::stub(field::M31::mul, c_mul)]
#[kani::stub(field::M31::reduce_u64, c_reduce)]
#[kani::stub(reference::M31::add, r_add)]
#[kani::stub(reference::M31::sub, r_sub)]
#[kani::stub(reference::M31::neg, r_neg)]
#[kani::stub(reference::M31::mul, r_mul)]
#[kani::stub(reference::M31::reduce_u64, r_reduce)]
#[kani::stub(field::CM31::mul, c_cm_mul)]
#[kani::stub(field::CM31::square, c_cm_square)]
#[kani::stub(field::CM31::mul_m31, c_cm_mul_m31)]
#[kani::stub(reference::CM31::mul, r_cm_mul)]
#[kani::stub(reference::CM31::square, r_cm_square)]
#[kani::stub(reference::CM31::mul_m31, r_cm_mul_m31)]
fn qm_mul() {let a=limbs();let b=limbs();let x=field::WideExact::from_limbs(a).unwrap();let y=field::WideExact::from_limbs(b).unwrap();let r=reference::WideExact::from_limbs(a).unwrap();let t=reference::WideExact::from_limbs(b).unwrap();let x=x.c0();let y=y.c0();let r=r.c0();let t=t.c0();unsafe{O=Oracle::new();}let expected=r.mul(t);let n=unsafe{O.n};unsafe{O.n=0;O.replay=true;}let actual=x.mul(y);assert_eq!(unsafe{O.n},n);let mut aa=[0u8;16];let mut bb=[0u8;16];actual.write_le_bytes(&mut aa);expected.write_le_bytes(&mut bb);assert_eq!(aa,bb);}
#[kani::proof]
#[kani::unwind(40)]
#[kani::stub(field::M31::add, c_add)]
#[kani::stub(field::M31::sub, c_sub)]
#[kani::stub(field::M31::neg, c_neg)]
#[kani::stub(field::M31::mul, c_mul)]
#[kani::stub(field::M31::reduce_u64, c_reduce)]
#[kani::stub(reference::M31::add, r_add)]
#[kani::stub(reference::M31::sub, r_sub)]
#[kani::stub(reference::M31::neg, r_neg)]
#[kani::stub(reference::M31::mul, r_mul)]
#[kani::stub(reference::M31::reduce_u64, r_reduce)]
#[kani::stub(field::CM31::mul, c_cm_mul)]
#[kani::stub(field::CM31::square, c_cm_square)]
#[kani::stub(field::CM31::mul_m31, c_cm_mul_m31)]
#[kani::stub(reference::CM31::mul, r_cm_mul)]
#[kani::stub(reference::CM31::square, r_cm_square)]
#[kani::stub(reference::CM31::mul_m31, r_cm_mul_m31)]
fn qm_square() {let a=limbs();let b=limbs();let x=field::WideExact::from_limbs(a).unwrap();let y=field::WideExact::from_limbs(b).unwrap();let r=reference::WideExact::from_limbs(a).unwrap();let t=reference::WideExact::from_limbs(b).unwrap();let x=x.c0();let y=y.c0();let r=r.c0();let t=t.c0();unsafe{O=Oracle::new();}let expected=r.square();let n=unsafe{O.n};unsafe{O.n=0;O.replay=true;}let actual=x.square();assert_eq!(unsafe{O.n},n);let mut aa=[0u8;16];let mut bb=[0u8;16];actual.write_le_bytes(&mut aa);expected.write_le_bytes(&mut bb);assert_eq!(aa,bb);}
#[kani::proof]
#[kani::unwind(40)]
#[kani::stub(field::M31::add, c_add)]
#[kani::stub(field::M31::sub, c_sub)]
#[kani::stub(field::M31::neg, c_neg)]
#[kani::stub(field::M31::mul, c_mul)]
#[kani::stub(field::M31::reduce_u64, c_reduce)]
#[kani::stub(reference::M31::add, r_add)]
#[kani::stub(reference::M31::sub, r_sub)]
#[kani::stub(reference::M31::neg, r_neg)]
#[kani::stub(reference::M31::mul, r_mul)]
#[kani::stub(reference::M31::reduce_u64, r_reduce)]
#[kani::stub(field::CM31::mul, c_cm_mul)]
#[kani::stub(field::CM31::square, c_cm_square)]
#[kani::stub(field::CM31::mul_m31, c_cm_mul_m31)]
#[kani::stub(reference::CM31::mul, r_cm_mul)]
#[kani::stub(reference::CM31::square, r_cm_square)]
#[kani::stub(reference::CM31::mul_m31, r_cm_mul_m31)]
fn qm_mul_m31() {let a=limbs();let b=limbs();let x=field::WideExact::from_limbs(a).unwrap();let y=field::WideExact::from_limbs(b).unwrap();let r=reference::WideExact::from_limbs(a).unwrap();let t=reference::WideExact::from_limbs(b).unwrap();let x=x.c0();let y=y.c0();let r=r.c0();let t=t.c0();unsafe{O=Oracle::new();}let expected=r.mul_m31(t.c0.a);let n=unsafe{O.n};unsafe{O.n=0;O.replay=true;}let actual=x.mul_m31(y.c0.a);assert_eq!(unsafe{O.n},n);let mut aa=[0u8;16];let mut bb=[0u8;16];actual.write_le_bytes(&mut aa);expected.write_le_bytes(&mut bb);assert_eq!(aa,bb);}
#[kani::proof]
#[kani::unwind(40)]
#[kani::stub(field::M31::add, c_add)]
#[kani::stub(field::M31::sub, c_sub)]
#[kani::stub(field::M31::neg, c_neg)]
#[kani::stub(field::M31::mul, c_mul)]
#[kani::stub(field::M31::reduce_u64, c_reduce)]
#[kani::stub(reference::M31::add, r_add)]
#[kani::stub(reference::M31::sub, r_sub)]
#[kani::stub(reference::M31::neg, r_neg)]
#[kani::stub(reference::M31::mul, r_mul)]
#[kani::stub(reference::M31::reduce_u64, r_reduce)]
#[kani::stub(field::CM31::mul, c_cm_mul)]
#[kani::stub(field::CM31::square, c_cm_square)]
#[kani::stub(field::CM31::mul_m31, c_cm_mul_m31)]
#[kani::stub(reference::CM31::mul, r_cm_mul)]
#[kani::stub(reference::CM31::square, r_cm_square)]
#[kani::stub(reference::CM31::mul_m31, r_cm_mul_m31)]
fn qm_mul_cm31() {let a=limbs();let b=limbs();let x=field::WideExact::from_limbs(a).unwrap();let y=field::WideExact::from_limbs(b).unwrap();let r=reference::WideExact::from_limbs(a).unwrap();let t=reference::WideExact::from_limbs(b).unwrap();let x=x.c0();let y=y.c0();let r=r.c0();let t=t.c0();unsafe{O=Oracle::new();}let expected=r.mul_cm31(t.c0);let n=unsafe{O.n};unsafe{O.n=0;O.replay=true;}let actual=x.mul_cm31(y.c0);assert_eq!(unsafe{O.n},n);let mut aa=[0u8;16];let mut bb=[0u8;16];actual.write_le_bytes(&mut aa);expected.write_le_bytes(&mut bb);assert_eq!(aa,bb);}
#[kani::proof]
#[kani::unwind(40)]
#[kani::stub(field::M31::add, c_add)]
#[kani::stub(field::M31::sub, c_sub)]
#[kani::stub(field::M31::neg, c_neg)]
#[kani::stub(field::M31::mul, c_mul)]
#[kani::stub(field::M31::reduce_u64, c_reduce)]
#[kani::stub(reference::M31::add, r_add)]
#[kani::stub(reference::M31::sub, r_sub)]
#[kani::stub(reference::M31::neg, r_neg)]
#[kani::stub(reference::M31::mul, r_mul)]
#[kani::stub(reference::M31::reduce_u64, r_reduce)]
#[kani::stub(field::CM31::mul, c_cm_mul)]
#[kani::stub(field::QM31::mul, c_qm_mul)]
#[kani::stub(field::CM31::square, c_cm_square)]
#[kani::stub(field::QM31::square, c_qm_square)]
#[kani::stub(field::CM31::mul_m31, c_cm_mul_m31)]
#[kani::stub(field::QM31::mul_m31, c_qm_mul_m31)]
#[kani::stub(reference::CM31::mul, r_cm_mul)]
#[kani::stub(reference::QM31::mul, r_qm_mul)]
#[kani::stub(reference::CM31::square, r_cm_square)]
#[kani::stub(reference::QM31::square, r_qm_square)]
#[kani::stub(reference::CM31::mul_m31, r_cm_mul_m31)]
#[kani::stub(reference::QM31::mul_m31, r_qm_mul_m31)]
fn wide_mul() {let a=limbs();let b=limbs();let x=field::WideExact::from_limbs(a).unwrap();let y=field::WideExact::from_limbs(b).unwrap();let r=reference::WideExact::from_limbs(a).unwrap();let t=reference::WideExact::from_limbs(b).unwrap();unsafe{O=Oracle::new();}let expected=r.mul(t);let n=unsafe{O.n};unsafe{O.n=0;O.replay=true;}let actual=x.mul(y);assert_eq!(unsafe{O.n},n);assert_eq!(actual.to_limbs(),expected.to_limbs());}
#[kani::proof]
#[kani::unwind(40)]
#[kani::stub(field::M31::add, c_add)]
#[kani::stub(field::M31::sub, c_sub)]
#[kani::stub(field::M31::neg, c_neg)]
#[kani::stub(field::M31::mul, c_mul)]
#[kani::stub(field::M31::reduce_u64, c_reduce)]
#[kani::stub(reference::M31::add, r_add)]
#[kani::stub(reference::M31::sub, r_sub)]
#[kani::stub(reference::M31::neg, r_neg)]
#[kani::stub(reference::M31::mul, r_mul)]
#[kani::stub(reference::M31::reduce_u64, r_reduce)]
#[kani::stub(field::CM31::mul, c_cm_mul)]
#[kani::stub(field::QM31::mul, c_qm_mul)]
#[kani::stub(field::CM31::square, c_cm_square)]
#[kani::stub(field::QM31::square, c_qm_square)]
#[kani::stub(field::CM31::mul_m31, c_cm_mul_m31)]
#[kani::stub(field::QM31::mul_m31, c_qm_mul_m31)]
#[kani::stub(reference::CM31::mul, r_cm_mul)]
#[kani::stub(reference::QM31::mul, r_qm_mul)]
#[kani::stub(reference::CM31::square, r_cm_square)]
#[kani::stub(reference::QM31::square, r_qm_square)]
#[kani::stub(reference::CM31::mul_m31, r_cm_mul_m31)]
#[kani::stub(reference::QM31::mul_m31, r_qm_mul_m31)]
fn wide_square() {let a=limbs();let b=limbs();let x=field::WideExact::from_limbs(a).unwrap();let y=field::WideExact::from_limbs(b).unwrap();let r=reference::WideExact::from_limbs(a).unwrap();let t=reference::WideExact::from_limbs(b).unwrap();unsafe{O=Oracle::new();}let expected=r.square();let n=unsafe{O.n};unsafe{O.n=0;O.replay=true;}let actual=x.square();assert_eq!(unsafe{O.n},n);assert_eq!(actual.to_limbs(),expected.to_limbs());}
#[kani::proof]
#[kani::unwind(40)]
#[kani::stub(field::M31::add, c_add)]
#[kani::stub(field::M31::sub, c_sub)]
#[kani::stub(field::M31::neg, c_neg)]
#[kani::stub(field::M31::mul, c_mul)]
#[kani::stub(field::M31::reduce_u64, c_reduce)]
#[kani::stub(reference::M31::add, r_add)]
#[kani::stub(reference::M31::sub, r_sub)]
#[kani::stub(reference::M31::neg, r_neg)]
#[kani::stub(reference::M31::mul, r_mul)]
#[kani::stub(reference::M31::reduce_u64, r_reduce)]
#[kani::stub(field::CM31::mul, c_cm_mul)]
#[kani::stub(field::QM31::mul, c_qm_mul)]
#[kani::stub(field::CM31::square, c_cm_square)]
#[kani::stub(field::QM31::square, c_qm_square)]
#[kani::stub(field::CM31::mul_m31, c_cm_mul_m31)]
#[kani::stub(field::QM31::mul_m31, c_qm_mul_m31)]
#[kani::stub(reference::CM31::mul, r_cm_mul)]
#[kani::stub(reference::QM31::mul, r_qm_mul)]
#[kani::stub(reference::CM31::square, r_cm_square)]
#[kani::stub(reference::QM31::square, r_qm_square)]
#[kani::stub(reference::CM31::mul_m31, r_cm_mul_m31)]
#[kani::stub(reference::QM31::mul_m31, r_qm_mul_m31)]
fn wide_mul_m31() {let a=limbs();let b=limbs();let x=field::WideExact::from_limbs(a).unwrap();let y=field::WideExact::from_limbs(b).unwrap();let r=reference::WideExact::from_limbs(a).unwrap();let t=reference::WideExact::from_limbs(b).unwrap();unsafe{O=Oracle::new();}let expected=r.mul_m31(t.c0().c0.a);let n=unsafe{O.n};unsafe{O.n=0;O.replay=true;}let actual=x.mul_m31(y.c0().c0.a);assert_eq!(unsafe{O.n},n);assert_eq!(actual.to_limbs(),expected.to_limbs());}
#[kani::proof]
#[kani::unwind(40)]
#[kani::stub(field::M31::add, c_add)]
#[kani::stub(field::M31::sub, c_sub)]
#[kani::stub(field::M31::neg, c_neg)]
#[kani::stub(field::M31::mul, c_mul)]
#[kani::stub(field::M31::reduce_u64, c_reduce)]
#[kani::stub(reference::M31::add, r_add)]
#[kani::stub(reference::M31::sub, r_sub)]
#[kani::stub(reference::M31::neg, r_neg)]
#[kani::stub(reference::M31::mul, r_mul)]
#[kani::stub(reference::M31::reduce_u64, r_reduce)]
#[kani::stub(field::CM31::mul, c_cm_mul)]
#[kani::stub(field::QM31::mul, c_qm_mul)]
#[kani::stub(field::CM31::square, c_cm_square)]
#[kani::stub(field::QM31::square, c_qm_square)]
#[kani::stub(field::CM31::mul_m31, c_cm_mul_m31)]
#[kani::stub(field::QM31::mul_m31, c_qm_mul_m31)]
#[kani::stub(reference::CM31::mul, r_cm_mul)]
#[kani::stub(reference::QM31::mul, r_qm_mul)]
#[kani::stub(reference::CM31::square, r_cm_square)]
#[kani::stub(reference::QM31::square, r_qm_square)]
#[kani::stub(reference::CM31::mul_m31, r_cm_mul_m31)]
#[kani::stub(reference::QM31::mul_m31, r_qm_mul_m31)]
fn wide_mul_qm31() {let a=limbs();let b=limbs();let x=field::WideExact::from_limbs(a).unwrap();let y=field::WideExact::from_limbs(b).unwrap();let r=reference::WideExact::from_limbs(a).unwrap();let t=reference::WideExact::from_limbs(b).unwrap();unsafe{O=Oracle::new();}let expected=r.mul_qm31(t.c0());let n=unsafe{O.n};unsafe{O.n=0;O.replay=true;}let actual=x.mul_qm31(y.c0());assert_eq!(unsafe{O.n},n);assert_eq!(actual.to_limbs(),expected.to_limbs());}
}
#[cfg(kani)] mod closure {
use super::*;
#[kani::proof]
fn canonical_reducers() {let a:u64=kani::any();let b:u128=kani::any();assert!(field::ct::reduce64(a)<field::P);assert!(field::ct::reduce128(b)<field::P);}
#[kani::proof]
fn canonical_arithmetic() {let a:u32=kani::any();let b:u32=kani::any();kani::assume(a<field::P);kani::assume(b<field::P);assert!(field::ct::add(a,b)<field::P);assert!(field::ct::sub(a,b)<field::P);assert!(field::ct::neg(a)<field::P);}
}

#[cfg(kani)] mod raw_constructors {
use super::*;
#[kani::proof]
#[kani::unwind(40)]
fn raw_wide_constructor_equivalence() {
 let a:[u32;8]=kani::any();
 let q=|i:usize|field::QM31{c0:field::CM31{a:field::M31(a[i]),b:field::M31(a[i+1])},c1:field::CM31{a:field::M31(a[i+2]),b:field::M31(a[i+3])}};
 let r=|i:usize|reference::QM31{c0:reference::CM31{a:reference::M31(a[i]),b:reference::M31(a[i+1])},c1:reference::CM31{a:reference::M31(a[i+2]),b:reference::M31(a[i+3])}};
 assert_eq!(field::WideExact::new(q(0),q(4)).to_limbs(),reference::WideExact::new(r(0),r(4)).to_limbs());
 assert_eq!(field::WideExact::from_qm31(q(0)).to_limbs(),reference::WideExact::from_qm31(r(0)).to_limbs());
}
}

#[cfg(any(kani,test))] #[path="../../crates/aspis-r1-cost-probe/src/ct_pole.rs"] mod pole_actual;
#[cfg(any(kani,test))] #[path="pole-instrumented.rs"] mod pole_instrumented;
#[cfg(any(kani,test))] #[path="pole-compression.rs"] mod pole_compression;
#[cfg(any(kani,test))] #[path="pole-compression-reference.rs"] mod pole_compression_reference;
#[cfg(any(kani,test))] #[path="pole-compression-instrumented.rs"] mod pole_compression_instrumented;
#[cfg(any(kani,test))] #[path="pole-proofs.rs"] mod pole_proofs;
