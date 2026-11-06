use super::*;
pub(super) fn reference(leaf:&PoolV1PairLeafWitnessV1)->M31 { leaf.second_commitment[7] }
#[cfg(kani)]
#[kani::proof_for_contract(PoolV1PairLeafWitnessV1::second_sentinel)]
fn small_contract(){let p:PoolV1PairLeafWitnessV1=kani::any();let _=p.second_sentinel();}
