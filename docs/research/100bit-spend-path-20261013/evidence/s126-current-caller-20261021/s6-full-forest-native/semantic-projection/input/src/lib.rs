#![allow(unexpected_cfgs)]
#[cfg(kani)]
mod proofs {
 use aspis_statement::pool_v1::{pair_forest_terminal::*,payment_relation::*,pair_forest_semantic_terminal::r0::Public};
 #[kani::proof]
 fn semantic_public_same_complete_fields() {
  // All three native payload types contain plain integers/arrays only.
  // No enum discriminant, pointer, Box or reference is fabricated.
  let common:PoolV1PairForestTerminalCommonV1=unsafe {core::mem::transmute(kani::any::<[u8;core::mem::size_of::<PoolV1PairForestTerminalCommonV1>()]>())};
  let transfer:PoolV1PrivateTransferPublicV1=unsafe {core::mem::transmute(kani::any::<[u8;core::mem::size_of::<PoolV1PrivateTransferPublicV1>()]>())};
  let withdrawal:PoolV1WithdrawalPublicV1=unsafe {core::mem::transmute(kani::any::<[u8;core::mem::size_of::<PoolV1WithdrawalPublicV1>()]>())};
  let which:bool=kani::any();
  let statement=if which {PoolV1PairForestTerminalStatementV1::PrivateTransfer{common,public:transfer}}
                else {PoolV1PairForestTerminalStatementV1::Withdrawal{common,public:withdrawal}};
  let selected=statement.semantic_public();
  match (&statement,selected) {
   (PoolV1PairForestTerminalStatementV1::PrivateTransfer{common,public},Public::Transfer(payment,transition))=>{
    assert!(core::ptr::eq(public,payment));
    assert!(core::ptr::eq(&common.lane_transition,transition));
    kani::cover!(true);
   },
   (PoolV1PairForestTerminalStatementV1::Withdrawal{common,public},Public::Withdrawal(payment,transition))=>{
    assert!(core::ptr::eq(public,payment));
    assert!(core::ptr::eq(&common.lane_transition,transition));
    kani::cover!(true);
   },
   _=>panic!("semantic variant changed"),
  }
 }
}
