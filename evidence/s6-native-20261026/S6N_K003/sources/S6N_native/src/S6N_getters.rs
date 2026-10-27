use aspis_core::field::M31;
use aspis_statement::poseidon2::Digest;
use aspis_statement::pool_v1::{pair_forest_terminal::*,payment_relation::*,pair_tree_profile::*,pair_terminal::*,pair_forest_semantic_terminal::r0::Public};
use std::boxed::Box;
fn digest() -> Digest { let raw:[u32;8]=kani::any(); raw.map(M31) }
fn common() -> PoolV1PairForestTerminalCommonV1 {
 PoolV1PairForestTerminalCommonV1 {
  master_account:kani::any(), checkpoint_account:kani::any(), selected_lane_account:kani::any(),
  output_lane:kani::any(), checkpoint_sequence:kani::any(), historical_global_anchor:digest(),
  lane_transition:PoolV1PairLatePublicStatementV1 {
   live_snapshot:PoolV1PairLiveSnapshotV1 {pool:kani::any(),deployment_domain:kani::any(),sequence:kani::any(),next_pair_index:kani::any(),current_root:digest(),frontier:std::array::from_fn(|_|digest())},
   candidate_afterstate:PoolV1PairVerifiedAfterstateV1 {next_pair_index:kani::any(),next_root:digest(),next_frontier:std::array::from_fn(|_|digest())}
  }
 }
}
fn transfer()->PoolV1PrivateTransferPublicV1 {PoolV1PrivateTransferPublicV1 {pool:kani::any(),deployment_domain:kani::any(),anchor_sequence:kani::any(),anchor_root:digest(),nullifier:digest(),asset_id:M31(kani::any()),recipient_commitment:digest(),change_commitment:digest()}}
fn withdrawal()->PoolV1WithdrawalPublicV1 {PoolV1WithdrawalPublicV1 {pool:kani::any(),deployment_domain:kani::any(),anchor_sequence:kani::any(),anchor_root:digest(),nullifier:digest(),asset_id:M31(kani::any()),amount:kani::any(),destination_token_account:kani::any(),change_commitment:digest()}}
#[kani::proof] #[kani::unwind(32)]
fn S6N_transfer_getter_owned_cleanup() {
 let c=common(); let p=transfer();
 let owned=Box::new(PoolV1PairForestTerminalStatementV1::PrivateTransfer{common:c,public:p});
 let before=*owned;
 assert!(owned.common()==&c);
 match owned.semantic_public() {
  Public::Transfer(public,transition)=>{
   assert!(public==&p);assert!(transition==&c.lane_transition);
   match &*owned {PoolV1PairForestTerminalStatementV1::PrivateTransfer{common,public:p}=>{
    assert!(std::ptr::eq(public,p));assert!(std::ptr::eq(transition,&common.lane_transition));assert!(std::ptr::eq(owned.common(),common));
   }, _=>unreachable!()}
  }, _=>unreachable!()
 }
 assert!(*owned==before); drop(owned);
 kani::cover!(true,"transfer real getters and ownership cleanup reached");
}
#[kani::proof] #[kani::unwind(32)]
fn S6N_withdrawal_getter_owned_cleanup() {
 let c=common(); let p=withdrawal();
 let owned=Box::new(PoolV1PairForestTerminalStatementV1::Withdrawal{common:c,public:p});
 let before=*owned;
 assert!(owned.common()==&c);
 match owned.semantic_public() {
  Public::Withdrawal(public,transition)=>{
   assert!(public==&p);assert!(transition==&c.lane_transition);
   match &*owned {PoolV1PairForestTerminalStatementV1::Withdrawal{common,public:p}=>{
    assert!(std::ptr::eq(public,p));assert!(std::ptr::eq(transition,&common.lane_transition));assert!(std::ptr::eq(owned.common(),common));
   }, _=>unreachable!()}
  }, _=>unreachable!()
 }
 assert!(*owned==before); drop(owned);
 kani::cover!(true,"withdrawal real getters and ownership cleanup reached");
}
