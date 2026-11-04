use aspis_core::{Digest32,field::M31};
use aspis_statement::pool_v1::{payment_relation::{PoolV1PrivateTransferPublicV1 as Transfer,PoolV1WithdrawalPublicV1 as Withdrawal},pair_tree_profile::{PoolV1PairLiveSnapshotV1 as Live,PoolV1PairLatePublicStatementV1 as Transition},pair_terminal::PoolV1PairVerifiedAfterstateV1 as After};
pub(crate) struct Inputs{pub(crate) t:Transfer,pub(crate) w:Withdrawal,pub(crate) x:Transition}
fn digest()->aspis_statement::poseidon2::Digest{let mut d=[M31::ZERO;8];let mut i=0;while i<8{d[i]=M31(kani::any());i+=1;}d}
impl Inputs{pub(crate) fn new()->Self{let mut frontier=[digest();aspis_statement::pool_v1::POOL_V1_PAIR_TREE_DEPTH];let mut i=0;while i<frontier.len(){frontier[i]=digest();i+=1;}
 Self{t:Transfer{pool:kani::any(),deployment_domain:kani::any(),anchor_sequence:kani::any(),anchor_root:digest(),nullifier:digest(),asset_id:M31(kani::any()),recipient_commitment:digest(),change_commitment:digest()},
 w:Withdrawal{pool:kani::any(),deployment_domain:kani::any(),anchor_sequence:kani::any(),anchor_root:digest(),nullifier:digest(),asset_id:M31(kani::any()),amount:kani::any(),destination_token_account:kani::any(),change_commitment:digest()},
 x:Transition{live_snapshot:Live{pool:kani::any(),deployment_domain:kani::any(),sequence:kani::any(),next_pair_index:kani::any(),current_root:digest(),frontier},candidate_afterstate:After{next_pair_index:kani::any(),next_root:digest(),next_frontier:frontier}}}}
 pub(crate) fn public(&self,withdraw:bool)->aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public<'_>{use aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public;if withdraw{Public::Withdrawal(&self.w,&self.x)}else{Public::Transfer(&self.t,&self.x)}}
}
#[derive(Clone,Copy)]pub(crate) struct Hash;
impl Digest32 for Hash{fn digest(&self,_:&[&[u8]])->[u8;32]{assert!(false,"digest reached before selected early return");[0;32]}}
