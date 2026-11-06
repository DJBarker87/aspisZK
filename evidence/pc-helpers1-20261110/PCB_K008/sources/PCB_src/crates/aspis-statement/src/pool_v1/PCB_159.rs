use super::*;
pub(super) fn reference(error:PoolV1VerifierDispatchFormatError)->PoolV1AuthorizationReceiptError { PoolV1AuthorizationReceiptError::Dispatch(error) }
#[cfg(kani)]
#[kani::proof_for_contract(<PoolV1AuthorizationReceiptError as From<PoolV1VerifierDispatchFormatError>>::from)]
fn error_contract() {let _=<PoolV1AuthorizationReceiptError as From<PoolV1VerifierDispatchFormatError>>::from(kani::any());}
