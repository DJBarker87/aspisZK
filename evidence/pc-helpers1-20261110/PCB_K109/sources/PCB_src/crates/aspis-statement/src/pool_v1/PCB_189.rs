use super::*;
pub(super) fn reference(error:PoolV1TreeError)->PoolV1PairForestAccountErrorV1 { PoolV1PairForestAccountErrorV1::Tree(error) }
#[cfg(kani)] #[kani::proof]
fn error_contract() {let e:PoolV1TreeError=kani::any();let r=<PoolV1PairForestAccountErrorV1 as core::convert::From<PoolV1TreeError>>::from(e);
 #[cfg(not(PCB_NEG_189))] assert_eq!(r,reference(e));
 #[cfg(PCB_NEG_189)] assert_ne!(r,reference(e));
}
