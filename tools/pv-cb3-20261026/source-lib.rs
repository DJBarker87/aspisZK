//! Extraction-only entry points; shipped modules imported without edits.
extern crate alloc;
#[cfg(kani)]
#[path = "../source/crates/aspis-r1-cost-probe/src/ct_pole.rs"]
pub mod ct_pole;
#[cfg(kani)]
#[path = "../source/crates/aspis-r1-cost-probe/src/multiproof.rs"]
pub mod multiproof;
#[cfg(kani)]
#[path = "../source/crates/aspis-r1-cost-probe/src/sampler.rs"]
pub mod sampler;
#[cfg(kani)]
pub fn all_slots_clear(values:&[[[aspis_core::field::QM31;2];2]], masks:&[u16;64],chi:aspis_core::field::QM31)->bool {
    ct_pole::all_slots_clear(values,masks,chi)
}
#[cfg(kani)]
pub fn binary_parent<H:aspis_core::Digest32>(hash:H,left:&[u8;32],right:&[u8;32])->[u8;32] {
    multiproof::binary_parent(hash,left,right)
}
#[cfg(kani)]
pub fn gamma_sample(block:&[u8;32])->aspis_core::field::WideExact { sampler::gamma_sample(block) }

#[cfg(kani)]
pub fn raw(weights:&aspis_r1_cost_probe::weights::Weights,kind:usize,j:usize)->aspis_core::field::QM31 {
    weights.raw(kind,j)
}
#[cfg(kani)]
pub fn new_weights(variant:aspis_r1_cost_probe::transport::Variant,alpha:&[aspis_core::field::QM31;10],z:&[aspis_core::circle::SecureCirclePoint;2])->Result<alloc::boxed::Box<aspis_r1_cost_probe::weights::Weights>,aspis_r1_cost_probe::verifier::Error> {
    aspis_r1_cost_probe::weights::Weights::new(variant,alpha,z)
}
#[cfg(kani)]
pub fn materialize(weights:&aspis_r1_cost_probe::weights::Weights,kappa:aspis_core::field::WideExact)->Result<alloc::vec::Vec<aspis_core::field::WideExact>,aspis_r1_cost_probe::verifier::Error> {
    weights.materialize(kappa)
}
#[cfg(kani)]
pub fn helper_sum(h1:&[aspis_core::field::QM31])->Option<aspis_core::field::QM31> {
    aspis_statement::state_only_semantic::state_only_copy_helper_sum(h1)
}
#[cfg(kani)]
pub fn statement_eq(a:&aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLatePublicStatementV1,b:&aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLatePublicStatementV1)->bool {
    a==b
}
#[cfg(kani)]
pub fn copy_registry()->Result<alloc::vec::Vec<aspis_statement::pool_v1::pair_trace::PoolV1PairCopyLinkV1>,aspis_statement::pool_v1::pair_trace::PoolV1PairTraceErrorV1> {
    aspis_statement::pool_v1::pair_forest_trace::build_pool_v1_pair_forest_copy_registry_v1()
}
#[cfg(kani)]
pub fn transition(public:aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public<'_>)->&aspis_statement::pool_v1::pair_tree_profile::PoolV1PairLatePublicStatementV1 {
    public.transition()
}
#[cfg(kani)]
pub fn public_bytes(public:aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public<'_>)->Result<alloc::vec::Vec<u8>,aspis_core::state_only_prefix::r0::Error> {
    public.public_bytes()
}
#[cfg(kani)]
pub fn terminal(public:aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public<'_>,claims:&[[aspis_core::field::QM31;29];3],alpha:&[aspis_core::field::QM31;10],c:&aspis_core::state_only_prefix::r0::Challenges)->Result<aspis_core::field::QM31,aspis_core::state_only_prefix::r0::Error> {
    public.terminal_qm31(claims,alpha,c)
}

#[cfg(kani)]
pub fn evaluate_polynomial(p:&[aspis_core::field::QM31;28],challenge:aspis_core::field::QM31)->aspis_core::field::QM31 {
 aspis_core::state_only_sumcheck::evaluate_state_only_polynomial(p,challenge)
}
// Resume op223: extract the unchanged function as current-crate built MIR.
#[cfg(kani)]
#[path = "../source/crates/aspis-statement/src/logup.rs"]
pub mod logup;
#[cfg(kani)]
pub fn compress_tagged_tuple(tag:aspis_core::field::M31,values:&[aspis_core::field::M31],lambda:aspis_core::field::QM31)->aspis_core::field::QM31 {
    logup::compress_tagged_tuple(tag,values,lambda)
}

#[cfg(kani)]
#[path = "../kani-proof/reference_split.rs"]
pub mod staged_reference;

#[cfg(kani)]
pub use aspis_r1_cost_probe::{transport,verifier,fast_pairing,trace};
#[cfg(kani)]
#[path = "../source/crates/aspis-r1-cost-probe/src/weights.rs"]
pub mod current_weights;
#[cfg(kani)]
pub fn current_raw(w:&current_weights::Weights,kind:usize,j:usize)->aspis_core::field::QM31 {
    w.raw(kind,j)
}
#[cfg(kani)]
pub fn vec_empty<T>(v:&alloc::vec::Vec<T>)->bool {v.is_empty()}
#[cfg(kani)]
pub fn vec_default<T>()->alloc::vec::Vec<T> {alloc::vec::Vec::default()}

#[cfg(kani)]
pub mod resume6_weights;
#[cfg(all(kani,not(pv_cb_extract)))]
mod resume6_weight_checks {
    use aspis_core::field::{QM31,CM31,M31,P};
    use aspis_r1_cost_probe::{weights::Weights,transport::Variant};
    fn q()->QM31 {let r:[u32;4]=kani::any();QM31{c0:CM31{a:M31(r[0]),b:M31(r[1])},c1:CM31{a:M31(r[2]),b:M31(r[3])}}}
    fn canonical(q:QM31) {kani::assume(q.c0.a.0<P);kani::assume(q.c0.b.0<P);kani::assume(q.c1.a.0<P);kani::assume(q.c1.b.0<P);}
    fn weights()->Weights {
        let v:u8=kani::any();kani::assume(v<3);let variant=match v {0=>Variant::S1,1=>Variant::S2,_=>Variant::D};
        let mut factors=[[[QM31::ZERO;4];5];5];let mut points=[[QM31::ZERO;10];3];
        for k in 0..5 {for d in 0..5 {for s in 0..4 {factors[k][d][s]=q();}}}
        for k in 0..3 {for d in 0..10 {points[k][d]=q();}}
        Weights{variant,factors,points,extra:[q(),q()]}
    }
    fn equal(a:QM31,b:QM31) {assert_eq!(a.c0.a.0,b.c0.a.0);assert_eq!(a.c0.b.0,b.c0.b.0);assert_eq!(a.c1.a.0,b.c1.a.0);assert_eq!(a.c1.b.0,b.c1.b.0);}
    #[kani::proof]
    #[kani::unwind(1026)]
    fn zero_kind() {
        let w=weights();let j:usize=kani::any();kani::assume(j<1024);
        equal(w.raw(0,j),super::resume6_weights::raw(&w,0,j));
    }
    #[kani::proof]
    #[kani::unwind(65)]
    fn extra_kind() {
        let w=weights();canonical(w.extra[0]);canonical(w.extra[1]);let j:usize=kani::any();
        equal(w.raw(4,j),super::resume6_weights::raw(&w,4,j));
    }
    #[kani::proof]
    #[kani::unwind(65)]
    fn tensor_kind() {
        let w=weights();let kind:usize=kani::any();let j:usize=kani::any();
        kani::assume(kind>=1 && kind<=6 && kind!=4);kani::assume(j<1024);
        kani::assume(kind>=5 || w.variant!=Variant::D);
        for k in 0..5 {for d in 0..5 {for s in 0..4 {canonical(w.factors[k][d][s]);}}}
        equal(w.raw(kind,j),super::resume6_weights::raw(&w,kind,j));
    }
    #[kani::proof]
    #[kani::unwind(1026)]
    fn dense_kind() {
        let w=weights();let kind:usize=kani::any();let j:usize=kani::any();
        kani::assume(kind>=1 && kind<=3);kani::assume(j<1024);kani::assume(w.variant==Variant::D);
        for k in 0..3 {for d in 0..10 {canonical(w.points[k][d]);}}
        equal(w.raw(kind,j),super::resume6_weights::raw(&w,kind,j));
    }
    #[kani::proof]
    #[kani::unwind(1026)]
    fn mixed_kind() {
        let w=weights();let kind:usize=kani::any();let j:usize=kani::any();
        kani::assume(kind>=1 && kind<=6 && kind!=4);kani::assume(j<1024);
        for k in 0..5 {for d in 0..5 {for s in 0..4 {canonical(w.factors[k][d][s]);}}}
        for k in 0..3 {for d in 0..10 {canonical(w.points[k][d]);}}
        equal(w.raw(kind,j),super::resume6_weights::raw(&w,kind,j));
    }

}
