#[cfg(kani)]
#[path="../../pv-rw19/proof/lib.rs"]
mod inherited;
#[cfg(kani)]
mod whole {
 use aspis_core::field::{M31,CM31,QM31};
 fn q()->QM31 {let r:[u32;4]=kani::any();QM31{c0:CM31{a:M31(r[0]),b:M31(r[1])},c1:CM31{a:M31(r[2]),b:M31(r[3])}}}
 fn indexed(tag:M31,values:&[M31],lambda:QM31)->QM31 {
  let mut out=QM31::from_cm31(CM31::from_m31(tag));let mut power=lambda;let mut i=0;
  while i<values.len() {out=out.add(power.mul_m31(values[i]));power=power.mul(lambda);i+=1;}
  out
 }
 #[kani::proof] #[kani::unwind(18)]
 fn source_p6_arity16() {
  let tag=M31(kani::any());let raw:[u32;16]=kani::any();let values=raw.map(M31);let lambda=q();
  let source=aspis_statement::logup::compress_tagged_tuple(tag,&values,lambda);
  assert_eq!(source,indexed(tag,&values,lambda));
 }
 #[kani::proof] #[kani::unwind(18)]
 fn source_p6_all_suffixes16() {
  let tag=M31(kani::any());let raw:[u32;16]=kani::any();let values=raw.map(M31);let lambda=q();
  let n:usize=kani::any();kani::assume(n<=16);
  assert_eq!(aspis_statement::logup::compress_tagged_tuple(tag,&values[n..],lambda),indexed(tag,&values[n..],lambda));
 }
}

#[cfg(kani)]
mod small;

#[cfg(kani)]
#[path="../../pv-rw-step/proof/generated.rs"]
mod literal;
