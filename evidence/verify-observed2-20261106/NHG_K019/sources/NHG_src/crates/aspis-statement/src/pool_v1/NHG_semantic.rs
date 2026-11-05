use super::*;
fn digest()->Digest{let w:[u32;8]=kani::any();core::array::from_fn(|i|M31(w[i]))}
#[kani::proof] #[kani::unwind(200)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::pool_v1::pair_forest_semantic_terminal::r0::NHG_semantic::KMX_copy_nonoverlapping)]
fn NHG_semantic_source(){
 let p=PoolV1PrivateTransferPublicV1{pool:kani::any(),deployment_domain:kani::any(),anchor_sequence:kani::any(),anchor_root:digest(),nullifier:digest(),asset_id:M31(kani::any()),recipient_commitment:digest(),change_commitment:digest()};
 let w=PoolV1WithdrawalPublicV1{pool:kani::any(),deployment_domain:kani::any(),anchor_sequence:kani::any(),anchor_root:digest(),nullifier:digest(),asset_id:M31(kani::any()),amount:kani::any(),destination_token_account:kani::any(),change_commitment:digest()};
 // Fully arbitrary typed transition: no zero/sparse prestate restriction.
 let t=PoolV1PairLatePublicStatementV1{
  live_snapshot:crate::pool_v1::pair_tree_profile::PoolV1PairLiveSnapshotV1{
   pool:kani::any(),deployment_domain:kani::any(),sequence:kani::any(),next_pair_index:kani::any(),current_root:digest(),frontier:core::array::from_fn(|_|digest())},
  candidate_afterstate:crate::pool_v1::PoolV1PairVerifiedAfterstateV1{
   next_pair_index:kani::any(),next_root:digest(),next_frontier:core::array::from_fn(|_|digest())}};
 let withdrawal:bool=kani::any();let public=if withdrawal{Public::Withdrawal(&w,&t)}else{Public::Transfer(&p,&t)};
 let result=public.semantic();let j:usize=kani::any();kani::assume(j<8);let b:usize=kani::any();kani::assume(b<32);
 assert!(core::ptr::eq(result.transition,&t));
 let good=if withdrawal {
  matches!(result.variant,CompiledVariant::Withdrawal)&&result.pool[b]==w.pool[b]&&result.deployment_domain[b]==w.deployment_domain[b]&&result.anchor[j]==w.anchor_root[j]&&result.nullifier[j]==w.nullifier[j]&&result.asset_id==w.asset_id&&result.recipient.is_none()&&result.change[j]==w.change_commitment[j]&&result.withdrawal_amount==Some(w.amount)
 }else{
  matches!(result.variant,CompiledVariant::PrivateTransfer)&&result.pool[b]==p.pool[b]&&result.deployment_domain[b]==p.deployment_domain[b]&&result.anchor[j]==p.anchor_root[j]&&result.nullifier[j]==p.nullifier[j]&&result.asset_id==p.asset_id&&result.recipient.unwrap()[j]==p.recipient_commitment[j]&&result.change[j]==p.change_commitment[j]&&result.withdrawal_amount.is_none()
 };
 assert!(good!=cfg!(NHG_invert));
}
// Exact KMX patch, unchanged. This file defines no substitute copy operation.
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
