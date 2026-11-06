use super::*;
pub(super) fn reference(error:PoolV1AuthorizationReceiptError)->PoolV1AuthorizationReceiptAccountErrorV1 { PoolV1AuthorizationReceiptAccountErrorV1::Receipt(error) }
#[cfg(kani)]
#[kani::proof_for_contract(<PoolV1AuthorizationReceiptAccountErrorV1 as core::convert::From<PoolV1AuthorizationReceiptError>>::from)]
fn error_contract() {let _=<PoolV1AuthorizationReceiptAccountErrorV1 as core::convert::From<PoolV1AuthorizationReceiptError>>::from(kani::any());}
