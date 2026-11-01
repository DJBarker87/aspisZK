// Smaller whole-source cases after the full arity16 gate timed out.
use aspis_core::field::{M31,CM31,QM31};
fn q()->QM31 {let r:[u32;4]=kani::any();QM31{c0:CM31{a:M31(r[0]),b:M31(r[1])},c1:CM31{a:M31(r[2]),b:M31(r[3])}}}
fn indexed(tag:M31,values:&[M31],lambda:QM31)->QM31 {
 let mut out=QM31::from_cm31(CM31::from_m31(tag));let mut power=lambda;let mut i=0;
 while i<values.len() {out=out.add(power.mul_m31(values[i]));power=power.mul(lambda);i+=1;}
 out
}
#[kani::proof] #[kani::unwind(18)]
fn source_p6_arity0() {
 let tag=M31(kani::any());let raw:[u32;0]=kani::any();let values=raw.map(M31);let lambda=q();
 assert_eq!(aspis_statement::logup::compress_tagged_tuple(tag,&values,lambda),indexed(tag,&values,lambda));
}
#[kani::proof] #[kani::unwind(18)]
fn source_p6_arity1() {
 let tag=M31(kani::any());let raw:[u32;1]=kani::any();let values=raw.map(M31);let lambda=q();
 assert_eq!(aspis_statement::logup::compress_tagged_tuple(tag,&values,lambda),indexed(tag,&values,lambda));
}
#[kani::proof] #[kani::unwind(18)]
fn source_p6_arity2() {
 let tag=M31(kani::any());let raw:[u32;2]=kani::any();let values=raw.map(M31);let lambda=q();
 assert_eq!(aspis_statement::logup::compress_tagged_tuple(tag,&values,lambda),indexed(tag,&values,lambda));
}
#[kani::proof] #[kani::unwind(18)]
fn source_p6_arity3() {
 let tag=M31(kani::any());let raw:[u32;3]=kani::any();let values=raw.map(M31);let lambda=q();
 assert_eq!(aspis_statement::logup::compress_tagged_tuple(tag,&values,lambda),indexed(tag,&values,lambda));
}
#[kani::proof] #[kani::unwind(18)]
fn source_p6_arity4() {
 let tag=M31(kani::any());let raw:[u32;4]=kani::any();let values=raw.map(M31);let lambda=q();
 assert_eq!(aspis_statement::logup::compress_tagged_tuple(tag,&values,lambda),indexed(tag,&values,lambda));
}
#[kani::proof] #[kani::unwind(18)]
fn source_p6_arity5() {
 let tag=M31(kani::any());let raw:[u32;5]=kani::any();let values=raw.map(M31);let lambda=q();
 assert_eq!(aspis_statement::logup::compress_tagged_tuple(tag,&values,lambda),indexed(tag,&values,lambda));
}
#[kani::proof] #[kani::unwind(18)]
fn source_p6_arity6() {
 let tag=M31(kani::any());let raw:[u32;6]=kani::any();let values=raw.map(M31);let lambda=q();
 assert_eq!(aspis_statement::logup::compress_tagged_tuple(tag,&values,lambda),indexed(tag,&values,lambda));
}
#[kani::proof] #[kani::unwind(18)]
fn source_p6_arity8() {
 let tag=M31(kani::any());let raw:[u32;8]=kani::any();let values=raw.map(M31);let lambda=q();
 assert_eq!(aspis_statement::logup::compress_tagged_tuple(tag,&values,lambda),indexed(tag,&values,lambda));
}

// Different reference after the indexed arity16 timeout: preserve the literal
// iterator/borrow shape and factor only the two arithmetic state assignments.
#[kani::proof] #[kani::unwind(18)]
fn source_fission_arity16() {
 let tag=M31(kani::any());let raw:[u32;16]=kani::any();let values=raw.map(M31);let lambda=q();
 assert_eq!(aspis_statement::logup::compress_tagged_tuple(tag,&values,lambda),super::literal::compress_fission(tag,&values,lambda));
}

#[kani::proof] #[kani::unwind(3)]
fn source_single_c0a() {
 let tag=M31(kani::any());let value=M31(kani::any());let lambda=q();
 let actual=aspis_statement::logup::compress_tagged_tuple(tag,&[value],lambda);
 let expected=tag.add(lambda.c0.a.mul(value));
 assert_eq!(actual.c0.a.0,expected.0);
}

#[kani::proof] #[kani::unwind(3)]
fn source_single_c0b() {
 let tag=M31(kani::any());let value=M31(kani::any());let lambda=q();
 let actual=aspis_statement::logup::compress_tagged_tuple(tag,&[value],lambda);
 let expected=M31(0).add(lambda.c0.b.mul(value));
 assert_eq!(actual.c0.b.0,expected.0);
}

#[kani::proof] #[kani::unwind(3)]
fn source_single_c1a() {
 let tag=M31(kani::any());let value=M31(kani::any());let lambda=q();
 let actual=aspis_statement::logup::compress_tagged_tuple(tag,&[value],lambda);
 let expected=M31(0).add(lambda.c1.a.mul(value));
 assert_eq!(actual.c1.a.0,expected.0);
}

#[kani::proof] #[kani::unwind(3)]
fn source_single_c1b() {
 let tag=M31(kani::any());let value=M31(kani::any());let lambda=q();
 let actual=aspis_statement::logup::compress_tagged_tuple(tag,&[value],lambda);
 let expected=M31(0).add(lambda.c1.b.mul(value));
 assert_eq!(actual.c1.b.0,expected.0);
}

#[kani::proof] #[kani::unwind(18)]
fn source_p6_zero_lambda16() {
 let tag=M31(kani::any());let raw:[u32;16]=kani::any();let values=raw.map(M31);
 let lambda=QM31::from_cm31(CM31::from_m31(M31(0)));
 assert_eq!(aspis_statement::logup::compress_tagged_tuple(tag,&values,lambda),indexed(tag,&values,lambda));
}

fn canonical(q:QM31) { let p=2147483647u32;
 kani::assume(q.c0.a.0<p);kani::assume(q.c0.b.0<p);kani::assume(q.c1.a.0<p);kani::assume(q.c1.b.0<p);
}
#[kani::proof] #[kani::unwind(18)]
fn source_p6_arity16_canonical() {
 let tag=M31(kani::any());kani::assume(tag.0<2147483647);
 let raw:[u32;16]=kani::any();let values=raw.map(M31);let lambda=q();canonical(lambda);
 for v in values {kani::assume(v.0<2147483647);}
 assert_eq!(aspis_statement::logup::compress_tagged_tuple(tag,&values,lambda),indexed(tag,&values,lambda));
}
#[kani::proof] #[kani::unwind(18)]
fn source_fission_arity16_canonical() {
 let tag=M31(kani::any());kani::assume(tag.0<2147483647);
 let raw:[u32;16]=kani::any();let values=raw.map(M31);let lambda=q();canonical(lambda);
 for v in values {kani::assume(v.0<2147483647);}
 assert_eq!(aspis_statement::logup::compress_tagged_tuple(tag,&values,lambda),super::literal::compress_fission(tag,&values,lambda));
}
