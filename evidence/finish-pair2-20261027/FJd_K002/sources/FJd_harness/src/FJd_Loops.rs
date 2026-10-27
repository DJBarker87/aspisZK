//! Owned safe references. All shipped callees execute without stubs.
use super::*;
fn any_k()->K {
 let v:[u32;4]=kani::any();
 for x in v {kani::assume(x<aspis_core::field::P);}
 K{c0:aspis_core::field::CM31{a:M31(v[0]),b:M31(v[1])},
 c1:aspis_core::field::CM31{a:M31(v[2]),b:M31(v[3])}}
}
fn any_e()->E {
 let v:[u32;8]=kani::any();
 for x in v {kani::assume(x<aspis_core::field::P);}
 E::from_limbs(v).unwrap()
}
fn empty()->Weights {Weights{variant:Variant::S2,factors:[[[K::ZERO;4];5];5],points:[[K::ZERO;10];3],extra:[K::ZERO;2]}}
fn tensor_reference(f:&[[K;4];5])->[K;64] {
 core::array::from_fn(|j|K::ONE.mul(f[2][j%4]).mul(f[3][(j/4)%4]).mul(f[4][j/16]))
}
#[kani::proof] #[kani::unwind(65)]
fn FJd_tensor64() {
 let mut w=empty();
 for d in 2..5 {for s in 0..4 {w.factors[0][d][s]=any_k();}}
 let mut out=[K::ZERO;64];w.tensor(0,2,&mut out);
 assert_eq!(out,tensor_reference(&w.factors[0]));
 kani::cover!(true,"canonical tensor domain is inhabited");
}
fn point_factors(p:&[K;10])->[[K;4];5] {
 core::array::from_fn(|d| {
 let a=p[9-2*TAU[d]];let b=p[8-2*TAU[d]];
 [K::ONE.sub(a).mul(K::ONE.sub(b)),a.mul(K::ONE.sub(b)),K::ONE.sub(a).mul(b),a.mul(b)] })
}
#[kani::proof] #[kani::unwind(11)]
fn FJd_point1_factors() {
 let alpha=core::array::from_fn(|_|any_k());
 let z=[SecureCirclePoint{x:K::ZERO,y:K::ONE};2];
 let w=Weights::new(Variant::S2,&alpha,&z).unwrap();
 assert_eq!(w.factors[0],point_factors(&alpha));
 kani::cover!(true,"all canonical original point coordinates");
}
fn successor_reference(z:&[K;10])->[K;10] {
 // Explicit reverse-coordinate fold. Each step consumes the original bit.
 let (_,out)=(0..10).rev().fold((K::ONE,*z),|(carry,mut out),i| {
 let bc=z[i].mul(carry);out[i]=z[i].add(carry).sub(bc.add(bc));(bc,out)
 });out
}
#[kani::proof] #[kani::unwind(11)]
fn FJd_successor10() {
 let alpha=core::array::from_fn(|_|any_k());
 let points=aspis_core::state_only_prefix::r0::statement_points(&alpha);
 assert_eq!(points[1],successor_reference(&alpha));
 kani::cover!(true,"all ten canonical coordinates");
}
fn circle_reference(z:SecureCirclePoint)->[[K;4];5] {
 let mut f=[[K::ZERO;4];5];f[0]=[K::ONE,z.y,z.x,z.x.mul(z.y)];
 let step=|x:K|x.mul(x).add(x.mul(x)).sub(K::ONE);
 let _=(1..5).fold(step(z.x),|x,d|{let y=step(x);f[d]=[K::ONE,x,y,x.mul(y)];step(y)});f
}
#[kani::proof] #[kani::unwind(11)]
fn FJd_circle4() {
 let alpha=[K::ZERO;10];let z=core::array::from_fn(|_|SecureCirclePoint{x:any_k(),y:any_k()});
 let w=Weights::new(Variant::S2,&alpha,&z).unwrap();
 assert_eq!(w.factors[3],circle_reference(z[0]));assert_eq!(w.factors[4],circle_reference(z[1]));
 kani::cover!(true,"both canonical endpoint coordinates");
}
fn dot_reference<const N:usize>(a:&[E;N],b:&[K;N])->E {
 (0..N).fold(E::ZERO,|v,i|v.add(a[i].mul_qm31(b[i])))
}
#[kani::proof] #[kani::unwind(65)]
fn FJd_dot64() {
 let a:[E;64]=core::array::from_fn(|_|any_e());let b:[K;64]=core::array::from_fn(|_|any_k());
 let mut dot=crate::fast_pairing::EbyKDot::new();
 for i in 0..64 {assert!(dot.push(a[i],b[i]).is_ok());}
 assert_eq!(dot.finish(),dot_reference(&a,&b));
 kani::cover!(true,"all 64 canonical E by K operands");
}

// Split of timed-out K001: fixed original-point digit and component, all ten
// original alpha coordinates remain symbolic and the entire constructor runs.
#[kani::proof] #[kani::unwind(11)]
fn FJd_point1_d0_s0() {
 let alpha=core::array::from_fn(|_|any_k());
 let z=[SecureCirclePoint{x:K::ZERO,y:K::ONE};2];
 let w=Weights::new(Variant::S2,&alpha,&z).unwrap();
 let a=alpha[9-2*TAU[0]];let b=alpha[8-2*TAU[0]];
 assert_eq!(w.factors[0][0][0],K::ONE.sub(a).mul(K::ONE.sub(b)));
 kani::cover!(true,"canonical original alpha, digit0 entry0");
}
