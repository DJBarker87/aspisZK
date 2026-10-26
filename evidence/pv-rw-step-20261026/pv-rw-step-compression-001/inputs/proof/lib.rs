pub mod generated;
#[cfg(kani)]
mod checks {
 use super::generated::*;
 use aspis_core::field::{M31,CM31,QM31};
 fn q()->QM31 {let r:[u32;4]=kani::any();QM31{c0:CM31{a:M31(r[0]),b:M31(r[1])},c1:CM31{a:M31(r[2]),b:M31(r[3])}}}
 #[kani::proof]
 #[kani::unwind(2)]
 fn compression_state_step() {
  let out=q();let power=q();let value=M31(kani::any());let lambda=q();
  let a=shipped_step(out,power,&value,lambda);let b=reference_step(out,power,value,lambda);
  assert_eq!(a.0.c0.a.0,b.0.c0.a.0);assert_eq!(a.0.c0.b.0,b.0.c0.b.0);
  assert_eq!(a.0.c1.a.0,b.0.c1.a.0);assert_eq!(a.0.c1.b.0,b.0.c1.b.0);
  assert_eq!(a.1.c0.a.0,b.1.c0.a.0);assert_eq!(a.1.c0.b.0,b.1.c0.b.0);
  assert_eq!(a.1.c1.a.0,b.1.c1.a.0);assert_eq!(a.1.c1.b.0,b.1.c1.b.0);
 }
}
