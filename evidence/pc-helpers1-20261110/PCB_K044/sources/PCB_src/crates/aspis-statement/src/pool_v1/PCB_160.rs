use super::*;
pub(super) fn reference(error:PoolV1AuthorizationReceiptError)->PoolV1AuthorizationReceiptAccountErrorV1 { PoolV1AuthorizationReceiptAccountErrorV1::Receipt(error) }
#[cfg(kani)] #[kani::proof]
fn error_contract() {let e:PoolV1AuthorizationReceiptError=kani::any();let r=<PoolV1AuthorizationReceiptAccountErrorV1 as core::convert::From<PoolV1AuthorizationReceiptError>>::from(e);
 #[cfg(not(PCB_NEG_160))] assert_eq!(r,reference(e));
 #[cfg(PCB_NEG_160)] assert_ne!(r,reference(e));
}
