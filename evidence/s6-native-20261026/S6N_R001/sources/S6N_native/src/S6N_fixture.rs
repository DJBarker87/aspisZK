use aspis_core::field::M31;
use aspis_statement::pool_v1::{pair_forest_terminal::*,payment_relation::*,pair_tree_profile::*,pair_terminal::*,pair_forest_semantic_terminal::r0::Public};
fn main(){
 let z=[M31::ZERO;8];
 let common=PoolV1PairForestTerminalCommonV1{master_account:[1;32],checkpoint_account:[3;32],selected_lane_account:[4;32],output_lane:0,checkpoint_sequence:0,historical_global_anchor:z,lane_transition:PoolV1PairLatePublicStatementV1{live_snapshot:PoolV1PairLiveSnapshotV1{pool:[1;32],deployment_domain:[2;32],sequence:0,next_pair_index:0,current_root:z,frontier:[z;20]},candidate_afterstate:PoolV1PairVerifiedAfterstateV1{next_pair_index:1,next_root:z,next_frontier:[z;20]}}};
 let transfer=PoolV1PairForestTerminalStatementV1::PrivateTransfer{common,public:PoolV1PrivateTransferPublicV1{pool:[1;32],deployment_domain:[2;32],anchor_sequence:0,anchor_root:z,nullifier:z,asset_id:M31::ZERO,recipient_commitment:z,change_commitment:z}};
 let withdrawal=PoolV1PairForestTerminalStatementV1::Withdrawal{common,public:PoolV1WithdrawalPublicV1{pool:[1;32],deployment_domain:[2;32],anchor_sequence:0,anchor_root:z,nullifier:z,asset_id:M31::ZERO,amount:1,destination_token_account:[9;32],change_commitment:z}};
 for statement in [transfer,withdrawal] {
  let encoded=encode_pool_v1_pair_forest_terminal_statement_v1(&statement).unwrap();
  let before=encoded;
  let owned=Box::new(decode_pool_v1_pair_forest_terminal_statement_v1(&encoded).unwrap());
  assert!(*owned==statement);assert!(*owned.common()==common);
  match (owned.semantic_public(),&*owned) {
   (Public::Transfer(p,t),PoolV1PairForestTerminalStatementV1::PrivateTransfer{common,public})=>{assert!(std::ptr::eq(p,public));assert!(std::ptr::eq(t,&common.lane_transition));},
   (Public::Withdrawal(p,t),PoolV1PairForestTerminalStatementV1::Withdrawal{common,public})=>{assert!(std::ptr::eq(p,public));assert!(std::ptr::eq(t,&common.lane_transition));}, _=>panic!("wrong variant")
  }
  drop(owned); assert!(encoded==before);
  let mut rejected=encoded;rejected[0]=0;
  assert!(matches!(decode_pool_v1_pair_forest_terminal_statement_v1(&rejected),Err(PoolV1PairForestTerminalFormatErrorV1::WrongMagic)));
  println!("1880-byte real decoder, exact contents, getters, drop and rejection passed");
 }
}
