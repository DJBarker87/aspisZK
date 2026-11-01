// Proof-local full-width transition gates; no shipped implementation changes.
#[cfg(kani)]
#[path="../../pv-rw-step/proof/iterator_state_step.rs"]
mod combined;
#[cfg(kani)]
mod gates {
 use aspis_core::field::{M31,CM31,QM31};
 use super::combined;
 fn q()->QM31 {let r:[u32;4]=kani::any();QM31{c0:CM31{a:M31(r[0]),b:M31(r[1])},c1:CM31{a:M31(r[2]),b:M31(r[3])}}}
 // This is the exact P6 indexed update, with arbitrary entering accumulator
 // and power. It does not assume either arithmetic kernel's output.
 fn step()->(QM31,QM31,QM31,QM31) {
  let raw:[u32;16]=kani::any();let values=raw.map(M31);
  let offset:usize=kani::any();kani::assume(offset<=16);
  let out=q();let power=q();let lambda=q();
  let (live,tail,a,b)=combined::iterator_state_step(values[offset..].iter(),out,power,lambda);
  let (expected_out,expected_power)=if offset<16 {
   (out.add(power.mul_m31(values[offset])),power.mul(lambda))
  } else {(out,power)};
  assert_eq!(live,offset<16);
  assert_eq!(tail.as_slice().len(),16-offset-usize::from(live));
  (a,b,expected_out,expected_power)
 }
 #[kani::proof] #[kani::unwind(18)]
 fn step_out_c0a() {let(a,b,c,d)=step();assert_eq!(a.c0.a.0,c.c0.a.0);}
 #[kani::proof] #[kani::unwind(18)]
 fn step_out_c0b() {let(a,b,c,d)=step();assert_eq!(a.c0.b.0,c.c0.b.0);}
 #[kani::proof] #[kani::unwind(18)]
 fn step_out_c1a() {let(a,b,c,d)=step();assert_eq!(a.c1.a.0,c.c1.a.0);}
 #[kani::proof] #[kani::unwind(18)]
 fn step_out_c1b() {let(a,b,c,d)=step();assert_eq!(a.c1.b.0,c.c1.b.0);}
 #[kani::proof] #[kani::unwind(18)]
 fn step_power_c0a() {let(a,b,c,d)=step();assert_eq!(b.c0.a.0,d.c0.a.0);}
 #[kani::proof] #[kani::unwind(18)]
 fn step_power_c0b() {let(a,b,c,d)=step();assert_eq!(b.c0.b.0,d.c0.b.0);}
 #[kani::proof] #[kani::unwind(18)]
 fn step_power_c1a() {let(a,b,c,d)=step();assert_eq!(b.c1.a.0,d.c1.a.0);}
 #[kani::proof] #[kani::unwind(18)]
 fn step_power_c1b() {let(a,b,c,d)=step();assert_eq!(b.c1.b.0,d.c1.b.0);}
}
