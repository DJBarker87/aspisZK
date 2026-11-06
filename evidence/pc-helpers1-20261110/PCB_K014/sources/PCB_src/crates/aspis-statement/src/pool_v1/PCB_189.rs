use super::*;
pub(super) fn reference(error:PoolV1TreeError)->PoolV1PairForestAccountErrorV1 { PoolV1PairForestAccountErrorV1::Tree(error) }
#[cfg(kani)]
#[kani::proof_for_contract(<PoolV1PairForestAccountErrorV1 as core::convert::From<PoolV1TreeError>>::from)]
fn error_contract() {let _=<PoolV1PairForestAccountErrorV1 as core::convert::From<PoolV1TreeError>>::from(kani::any());}
