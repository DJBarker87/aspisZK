use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn any_cm()->CM31{CM31{a:M31(kani::any()),b:M31(kani::any())}}
fn any_q()->QM31{QM31{c0:any_cm(),c1:any_cm()}}
pub(super) fn canonical(x:QM31)->bool{canonical_cm(x.c0)&&canonical_cm(x.c1)}
fn canonical_cm(x:CM31)->bool{x.a.0<P&&x.b.0<P}
fn spec_mul(x:CM31,y:CM31)->CM31{
 let p=P as u64;let a=x.a.0 as u64;let b=x.b.0 as u64;let c=y.a.0 as u64;let d=y.b.0 as u64;
 CM31{a:M31((((a*c)%p+p-(b*d)%p)%p) as u32),b:M31((((a*d)%p+(b*c)%p)%p) as u32)}
}
// No multiplication theorem is checked by Kani. The returned value is
// nondeterministic, constrained by the paired Lean natural-coordinate law.
fn product(x:CM31,y:CM31)->CM31{assert!(canonical_cm(x)&&canonical_cm(y));let z=any_cm();kani::assume(z==spec_mul(x,y));z}
fn square(x:CM31)->CM31{assert!(canonical_cm(x));let z=any_cm();kani::assume(z==spec_mul(x,x));z}
pub(super) fn reference(x:QM31)->QM31{
 let a=x.c0.square();let b=x.c1.square();
 QM31{c0:a.add(mul_by_r(b)),c1:x.c0.mul(x.c1).double()}
}
#[kani::proof_for_contract(QM31::square)]
#[kani::unwind(80)]
#[kani::stub(CM31::square,square)]
#[kani::stub(CM31::mul,product)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn actual_contract(){let x=any_q();kani::assume(canonical(x));x.square();}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn copy_positive(){let src=any_q();let mut dst=any_q();unsafe{core::ptr::copy_nonoverlapping(&src,&mut dst,1)};assert!(src==dst);}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn copy_negative(){let src=any_q();let mut dst=any_q();unsafe{core::ptr::copy_nonoverlapping(&src,&mut dst,1)};assert!(src!=dst);}
