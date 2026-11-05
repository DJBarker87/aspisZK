use super::*;
include!("NHU_transition_step_body.rs");
#[test]
fn NIH_transition_witness(){
 let raw=[141619947,1448060902,524379093,1944458907,1832113773,579270723,752346270,1038346536];
 let selected=raw.map(M31);
 let mut next_frontier=[[M31(0);8];20];next_frontier[1]=selected;
 let transition=PoolV1PairLatePublicStatementV1{
  live_snapshot:crate::pool_v1::pair_tree_profile::PoolV1PairLiveSnapshotV1{
   pool:[0;32],deployment_domain:[0;32],sequence:3,next_pair_index:3,
   current_root:[M31(0);8],frontier:[[M31(0);8];20]},
  candidate_afterstate:crate::pool_v1::PoolV1PairVerifiedAfterstateV1{
   next_pair_index:4,next_root:[M31(0);8],next_frontier}};
 let public=SemanticPublic{variant:CompiledVariant::PrivateTransfer,pool:[0;32],deployment_domain:[0;32],anchor:[M31(0);8],nullifier:[M31(0);8],asset_id:M31(0),recipient:None,change:[M31(0);8],withdrawal_amount:None,transition:&transition};
 let should_reject=transition.candidate_afterstate.next_frontier[1]!=empty_root(1);
 let source_after=public.transition.candidate_afterstate;
 assert_eq!(source_after.next_frontier[1],selected);
 assert_eq!(selected,empty_root(1));
 let out=NHU_transition_step_cut(public,2,1);
 println!("NIH_WITNESS reject={} actual={:?}",should_reject,out);
 assert!(!should_reject);
 assert_eq!(out,Ok(2));
}
