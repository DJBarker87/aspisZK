#![allow(dead_code,unexpected_cfgs)]
#[cfg(kani)] mod proofs {
 use aspis_s126_owned_sdk::{OwnedSdk,owned_stage1};
 fn scan(_:Vec<u8>)->bool {false}
 #[kani::proof]
 #[kani::stub(aspis_s126_owned_sdk::owned_checkpoint_nonzero,scan)]
 fn private_source_stub_resolution() {
  let sdk=OwnedSdk{accounts:vec![],data_cells:vec![],lamports_cells:vec![]};
  assert!(owned_stage1([0;32],sdk,vec![3,10]).0.is_err());
 }
}
