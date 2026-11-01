#![allow(unexpected_cfgs)]
use aspis_core::field::{QM31, PreparedQm31Multiplier, qm31_sum_products3};
pub fn block(polynomial: &[QM31;28], powers:[QM31;3], block: usize) -> QM31 {
    let start=4*block;
    polynomial[start].add(qm31_sum_products3(powers,
        [polynomial[start+1],polynomial[start+2],polynomial[start+3]]))
}
pub fn evaluate(polynomial: &[QM31;28], challenge: QM31) -> QM31 {
    let x2=challenge.square();
    let x3=challenge.mul(x2);
    let x4=x2.square();
    let powers=[challenge,x2,x3];
    let prepared=PreparedQm31Multiplier::new(x4);
    let mut acc=block(polynomial,powers,6);
    let mut index=6usize;
    while index>0 {
        index-=1;
        acc=prepared.mul(acc).add(block(polynomial,powers,index));
    }
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
