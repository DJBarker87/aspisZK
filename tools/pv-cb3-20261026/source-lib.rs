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
