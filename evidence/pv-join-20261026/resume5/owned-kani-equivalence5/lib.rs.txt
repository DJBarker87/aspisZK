#![allow(unexpected_cfgs)]
use aspis_core::field::{QM31, CM31, M31, PreparedQm31Multiplier};
pub fn parts(q:QM31)->[[M31;3];3] {
    let sum=q.c0.add(q.c1);
    [[q.c0.a,q.c0.b,q.c0.a.add(q.c0.b)],
     [q.c1.a,q.c1.b,q.c1.a.add(q.c1.b)],
     [sum.a,sum.b,sum.a.add(sum.b)]]
}
pub fn reconstruct(a:u64,b:u64,c:u64)->CM31 {
    let m0=M31::reduce_u64(a);let m1=M31::reduce_u64(b);let m2=M31::reduce_u64(c);
    CM31{a:m0.sub(m1),b:m2.sub(m0).sub(m1)}
}
pub fn sum3(left:[QM31;3],right:[QM31;3])->QM31 {
    let l0=parts(left[0]);let r0=parts(right[0]);
    let l1=parts(left[1]);let r1=parts(right[1]);
    let l2=parts(left[2]);let r2=parts(right[2]);
    let m0=reconstruct((l0[0][0].0 as u64)*(r0[0][0].0 as u64)+(l1[0][0].0 as u64)*(r1[0][0].0 as u64)+(l2[0][0].0 as u64)*(r2[0][0].0 as u64),(l0[0][1].0 as u64)*(r0[0][1].0 as u64)+(l1[0][1].0 as u64)*(r1[0][1].0 as u64)+(l2[0][1].0 as u64)*(r2[0][1].0 as u64),(l0[0][2].0 as u64)*(r0[0][2].0 as u64)+(l1[0][2].0 as u64)*(r1[0][2].0 as u64)+(l2[0][2].0 as u64)*(r2[0][2].0 as u64));
    let m1=reconstruct((l0[1][0].0 as u64)*(r0[1][0].0 as u64)+(l1[1][0].0 as u64)*(r1[1][0].0 as u64)+(l2[1][0].0 as u64)*(r2[1][0].0 as u64),(l0[1][1].0 as u64)*(r0[1][1].0 as u64)+(l1[1][1].0 as u64)*(r1[1][1].0 as u64)+(l2[1][1].0 as u64)*(r2[1][1].0 as u64),(l0[1][2].0 as u64)*(r0[1][2].0 as u64)+(l1[1][2].0 as u64)*(r1[1][2].0 as u64)+(l2[1][2].0 as u64)*(r2[1][2].0 as u64));
    let m2=reconstruct((l0[2][0].0 as u64)*(r0[2][0].0 as u64)+(l1[2][0].0 as u64)*(r1[2][0].0 as u64)+(l2[2][0].0 as u64)*(r2[2][0].0 as u64),(l0[2][1].0 as u64)*(r0[2][1].0 as u64)+(l1[2][1].0 as u64)*(r1[2][1].0 as u64)+(l2[2][1].0 as u64)*(r2[2][1].0 as u64),(l0[2][2].0 as u64)*(r0[2][2].0 as u64)+(l1[2][2].0 as u64)*(r1[2][2].0 as u64)+(l2[2][2].0 as u64)*(r2[2][2].0 as u64));
    let rb=CM31{a:m1.a.double().sub(m1.b),b:m1.a.add(m1.b.double())};
    QM31{c0:m0.add(rb),c1:m2.sub(m0).sub(m1)}
}
pub fn block(polynomial: &[QM31;28], powers:[QM31;3], block: usize) -> QM31 {
    let start=4*block;
    polynomial[start].add(sum3(powers,
        [polynomial[start+1],polynomial[start+2],polynomial[start+3]]))
}
pub fn evaluate(polynomial: &[QM31;28], challenge: QM31) -> QM31 {
    let x2=challenge.square();
    let x3=challenge.mul(x2);
    let x4=x2.square();
    let powers=[challenge,x2,x3];
    let prepared=PreparedQm31Multiplier::new(x4);
    let acc=block(polynomial,powers,6);
    let acc=prepared.mul(acc).add(block(polynomial,powers,5));
    let acc=prepared.mul(acc).add(block(polynomial,powers,4));
    let acc=prepared.mul(acc).add(block(polynomial,powers,3));
    let acc=prepared.mul(acc).add(block(polynomial,powers,2));
    let acc=prepared.mul(acc).add(block(polynomial,powers,1));
    let acc=prepared.mul(acc).add(block(polynomial,powers,0));

    acc
}
#[cfg(all(kani, not(pv_join_extract)))]
mod checks {
    use super::*;
    use aspis_core::field::{M31,CM31,P};
    fn canonical(q:QM31)->bool { q.c0.a.0<P && q.c0.b.0<P && q.c1.a.0<P && q.c1.b.0<P }
    fn anyq()->QM31 {QM31{c0:CM31{a:M31(kani::any()),b:M31(kani::any())},c1:CM31{a:M31(kani::any()),b:M31(kani::any())}}}
    #[kani::proof]
    #[kani::unwind(30)]
    fn canonical_reference_equivalence() {
        let mut polynomial=[QM31::ZERO;28];
        let mut i=0;
        while i<28 { let q=anyq();kani::assume(canonical(q));polynomial[i]=q;i+=1; }
        let x=anyq();kani::assume(canonical(x));
        assert_eq!(aspis_core::state_only_sumcheck::evaluate_state_only_polynomial(&polynomial,x),evaluate(&polynomial,x));
    }
    #[kani::proof]
    fn reduce64_canonical() { let x:u64=kani::any();assert!(M31::reduce_u64(x).0<P); }
    #[kani::proof]
    fn add_sub_canonical() {
        let a:u32=kani::any();let b:u32=kani::any();kani::assume(a<P);kani::assume(b<P);
        assert!(M31(a).add(M31(b)).0<P);assert!(M31(a).sub(M31(b)).0<P);
    }
    #[kani::proof]
    fn mul_canonical() {
        let a:u32=kani::any();let b:u32=kani::any();kani::assume(a<P);kani::assume(b<P);
        assert!(M31(a).mul(M31(b)).0<P);
    }
}
