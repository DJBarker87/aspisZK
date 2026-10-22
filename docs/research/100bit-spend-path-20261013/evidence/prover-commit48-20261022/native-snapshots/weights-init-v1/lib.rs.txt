#![allow(unexpected_cfgs)]
pub mod field;
#[cfg(kani)] mod proofs {
 use super::field::{M31,CM31,QM31,WideExact as E,P};
 fn qm()->QM31 {
  let a:[u32;4]=kani::any();
  kani::assume(a[0]<P && a[1]<P && a[2]<P && a[3]<P);
  QM31{c0:CM31{a:M31(a[0]),b:M31(a[1])},c1:CM31{a:M31(a[2]),b:M31(a[3])}}
 }
 #[kani::proof] #[kani::unwind(34)]
 fn full_width_serializer() {
  let a=qm();let b=qm();let value=E::new(a,b);
  let bytes=value.to_le_bytes();
  let words=[a.c0.a.0,a.c0.b.0,a.c1.a.0,a.c1.b.0,b.c0.a.0,b.c0.b.0,b.c1.a.0,b.c1.b.0];
  for limb in 0..8 {
   for byte in 0..4 {assert_eq!(bytes[4*limb+byte],words[limb].to_le_bytes()[byte]);}
  }
  assert_eq!(E::from_le_bytes(&bytes),Some(value));
 }
 #[kani::proof]
 fn base_column_embedding() {
  let raw:u32=kani::any();
  // Exact scalar.rs CodeField::from_m31 chain, with each helper body
  // copied unchanged from its trait implementation below.
  let native=wide_from_m31(M31(raw));
  let semantic_lift=QM31::from_cm31(CM31::from_m31(M31(raw)));
  assert_eq!(native,E::from_qm31(semantic_lift));
 }
 fn base_from_m31(value:M31)->M31 {M31(value.0%P)}
 fn cm_from_m31(value:M31)->CM31 {CM31::from_m31(base_from_m31(value))}
 fn qm_from_m31(value:M31)->QM31 {QM31::from_cm31(cm_from_m31(value))}
 fn wide_from_m31(value:M31)->E {E::from_qm31(qm_from_m31(value))}
}
include!("weights-init.rs");
