use super::*;
pub(super) fn reference(error:PoolV1VerifierDispatchFormatError)->PoolV1AuthorizationReceiptError { PoolV1AuthorizationReceiptError::Dispatch(error) }
#[cfg(kani)] #[kani::proof]
fn error_contract() {let e:PoolV1VerifierDispatchFormatError=kani::any();let r=<PoolV1AuthorizationReceiptError as core::convert::From<PoolV1VerifierDispatchFormatError>>::from(e);
 #[cfg(not(PCB_NEG_159))] assert_eq!(r,reference(e));
 #[cfg(PCB_NEG_159)] assert_ne!(r,reference(e));
}
