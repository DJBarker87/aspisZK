#[cfg(kani)] mod tower {
use super::*;
fn limbs()->[u32;8] {let x:[u32;8]=kani::any(); for a in x {kani::assume(a<field::P);} x}
fn stub_add(a:u32,b:u32)->u32 {reference::M31(a).add(reference::M31(b)).0}
fn stub_sub(a:u32,b:u32)->u32 {reference::M31(a).sub(reference::M31(b)).0}
fn stub_neg(a:u32)->u32 {reference::M31(a).neg().0}
fn stub_zero(a:u32)->bool {reference::M31(a).is_zero()}
fn stub_reduce(x:u64)->u32 {reference::M31::reduce_u64(x).0}
#[kani::proof]
#[kani::unwind(40)]
#[kani::stub(field::ct::add, stub_add)]
#[kani::stub(field::ct::sub, stub_sub)]
#[kani::stub(field::ct::neg, stub_neg)]
#[kani::stub(field::ct::is_zero, stub_zero)]
#[kani::stub(field::ct::reduce64, stub_reduce)]
fn wide_add_composed() {let a=limbs();let b=limbs();let x=field::WideExact::from_limbs(a).unwrap();let y=field::WideExact::from_limbs(b).unwrap();let r=reference::WideExact::from_limbs(a).unwrap();let t=reference::WideExact::from_limbs(b).unwrap();assert_eq!(x.add(y).to_limbs(),r.add(t).to_limbs());}
#[kani::proof]
#[kani::unwind(40)]
#[kani::stub(field::ct::add, stub_add)]
#[kani::stub(field::ct::sub, stub_sub)]
#[kani::stub(field::ct::neg, stub_neg)]
#[kani::stub(field::ct::is_zero, stub_zero)]
#[kani::stub(field::ct::reduce64, stub_reduce)]
fn wide_sub_composed() {let a=limbs();let b=limbs();let x=field::WideExact::from_limbs(a).unwrap();let y=field::WideExact::from_limbs(b).unwrap();let r=reference::WideExact::from_limbs(a).unwrap();let t=reference::WideExact::from_limbs(b).unwrap();assert_eq!(x.sub(y).to_limbs(),r.sub(t).to_limbs());}
#[kani::proof]
#[kani::unwind(40)]
#[kani::stub(field::ct::add, stub_add)]
#[kani::stub(field::ct::sub, stub_sub)]
#[kani::stub(field::ct::neg, stub_neg)]
#[kani::stub(field::ct::is_zero, stub_zero)]
#[kani::stub(field::ct::reduce64, stub_reduce)]
fn wide_neg_composed() {let a=limbs();let b=limbs();let x=field::WideExact::from_limbs(a).unwrap();let y=field::WideExact::from_limbs(b).unwrap();let r=reference::WideExact::from_limbs(a).unwrap();let t=reference::WideExact::from_limbs(b).unwrap();assert_eq!(x.neg().to_limbs(),r.neg().to_limbs());}
#[kani::proof]
#[kani::unwind(40)]
#[kani::stub(field::ct::add, stub_add)]
#[kani::stub(field::ct::sub, stub_sub)]
#[kani::stub(field::ct::neg, stub_neg)]
#[kani::stub(field::ct::is_zero, stub_zero)]
#[kani::stub(field::ct::reduce64, stub_reduce)]
fn wide_is_zero_composed() {let a=limbs();let b=limbs();let x=field::WideExact::from_limbs(a).unwrap();let y=field::WideExact::from_limbs(b).unwrap();let r=reference::WideExact::from_limbs(a).unwrap();let t=reference::WideExact::from_limbs(b).unwrap();assert_eq!(x.is_zero(),r.is_zero());}
#[kani::proof]
#[kani::unwind(40)]
#[kani::stub(field::ct::add, stub_add)]
#[kani::stub(field::ct::sub, stub_sub)]
#[kani::stub(field::ct::neg, stub_neg)]
#[kani::stub(field::ct::is_zero, stub_zero)]
#[kani::stub(field::ct::reduce64, stub_reduce)]
fn wide_mul_composed() {let a=limbs();let b=limbs();let x=field::WideExact::from_limbs(a).unwrap();let y=field::WideExact::from_limbs(b).unwrap();let r=reference::WideExact::from_limbs(a).unwrap();let t=reference::WideExact::from_limbs(b).unwrap();assert_eq!(x.mul(y).to_limbs(),r.mul(t).to_limbs());}
#[kani::proof]
#[kani::unwind(40)]
#[kani::stub(field::ct::add, stub_add)]
#[kani::stub(field::ct::sub, stub_sub)]
#[kani::stub(field::ct::neg, stub_neg)]
#[kani::stub(field::ct::is_zero, stub_zero)]
#[kani::stub(field::ct::reduce64, stub_reduce)]
fn wide_square_composed() {let a=limbs();let b=limbs();let x=field::WideExact::from_limbs(a).unwrap();let y=field::WideExact::from_limbs(b).unwrap();let r=reference::WideExact::from_limbs(a).unwrap();let t=reference::WideExact::from_limbs(b).unwrap();assert_eq!(x.square().to_limbs(),r.square().to_limbs());}
#[kani::proof]
#[kani::unwind(40)]
#[kani::stub(field::ct::add, stub_add)]
#[kani::stub(field::ct::sub, stub_sub)]
#[kani::stub(field::ct::neg, stub_neg)]
#[kani::stub(field::ct::is_zero, stub_zero)]
#[kani::stub(field::ct::reduce64, stub_reduce)]
fn wide_mul_qm31_composed() {let a=limbs();let b=limbs();let x=field::WideExact::from_limbs(a).unwrap();let y=field::WideExact::from_limbs(b).unwrap();let r=reference::WideExact::from_limbs(a).unwrap();let t=reference::WideExact::from_limbs(b).unwrap();assert_eq!(x.mul_qm31(y.c0()).to_limbs(),r.mul_qm31(t.c0()).to_limbs());}
#[kani::proof]
#[kani::unwind(40)]
#[kani::stub(field::ct::add, stub_add)]
#[kani::stub(field::ct::sub, stub_sub)]
#[kani::stub(field::ct::neg, stub_neg)]
#[kani::stub(field::ct::is_zero, stub_zero)]
#[kani::stub(field::ct::reduce64, stub_reduce)]
fn wide_mul_m31_composed() {let a=limbs();let b=limbs();let x=field::WideExact::from_limbs(a).unwrap();let y=field::WideExact::from_limbs(b).unwrap();let r=reference::WideExact::from_limbs(a).unwrap();let t=reference::WideExact::from_limbs(b).unwrap();assert_eq!(x.mul_m31(y.c0().c0.a).to_limbs(),r.mul_m31(t.c0().c0.a).to_limbs());}
}
