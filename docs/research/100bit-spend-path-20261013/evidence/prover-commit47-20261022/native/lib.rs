#![allow(unexpected_cfgs)]
pub mod field;
#[cfg(kani)] mod checks {
use super::field::{M31,CM31,QM31,WideExact as E,P};
fn qm() -> QM31 {
 let a:[u32;4]=kani::any();
 kani::assume(a[0]<P && a[1]<P && a[2]<P && a[3]<P);
 QM31{c0:CM31{a:M31(a[0]),b:M31(a[1])},c1:CM31{a:M31(a[2]),b:M31(a[3])}}
}
#[kani::proof]
#[kani::unwind(34)]
fn embedded_codec() {
 let q=qm();let e=E::from_qm31(q);let b=e.to_le_bytes();
 assert_eq!(e.c0(),q); assert_eq!(e.c1(),QM31::ZERO);
 assert_eq!(QM31::from_le_bytes(&b[..16]),Some(q));
 assert_eq!(E::from_le_bytes(&b),Some(e));
 for i in 16..32 {assert_eq!(b[i],0);}
}
#[kani::proof]
fn embedded_add() {
 let q=qm();let r=qm();let e=E::from_qm31(q).add(E::from_qm31(r));
 assert_eq!(e.c0(),q.add(r));assert_eq!(e.c1(),QM31::ZERO);
 let d=e.to_limbs(); for i in 0..8 {assert!(d[i]<P);}
}
#[kani::proof]
fn embedded_mul() {
 let q=qm();let r=qm();let e=E::from_qm31(q).mul(E::from_qm31(r));
 assert_eq!(e.c0(),q.mul(r));assert_eq!(e.c1(),QM31::ZERO);
 let d=e.to_limbs(); for i in 0..8 {assert!(d[i]<P);}
}
#[kani::proof]
#[kani::unwind(34)]
fn embedded_byte_order() {
 let q=qm();let e=E::from_qm31(q);let b=e.to_le_bytes();
 let words=[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0,0,0,0,0];
 for limb in 0..8 {
  for byte in 0..4 {assert_eq!(b[4*limb+byte],words[limb].to_le_bytes()[byte]);}
 }
}

}
