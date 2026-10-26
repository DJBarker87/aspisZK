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
