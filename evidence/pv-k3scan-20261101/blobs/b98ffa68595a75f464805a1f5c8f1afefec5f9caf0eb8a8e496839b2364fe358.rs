use aspis_core::field::{QM31,M31};
use aspis_statement::{poseidon2::Digest,pool_v1::{pair_tree_profile::{PoolV1PairLatePublicStatementV1,PoolV1PairLiveSnapshotV1},pair_terminal::PoolV1PairVerifiedAfterstateV1}};
#[derive(Clone,Copy)]
pub struct Public16 {pub variant:bool,pub pool:[u8;32],pub domain:[u8;32],pub anchor:Digest,pub nullifier:Digest,pub asset:M31,pub recipient:Option<Digest>,pub change:Digest,pub amount:Option<u32>,pub transition:PoolV1PairLatePublicStatementV1}
#[cfg(kani)]
pub fn digest()->Digest {let a:[u32;8]=kani::any();let mut d=[M31(0);8];let mut i=0;while i<8 {d[i]=M31(a[i]);i+=1;}d}
#[cfg(kani)]
pub fn public()->Public16 {let mut before=[[M31(0);8];20];let mut after=before;let mut i=0;while i<20 {before[i]=digest();after[i]=digest();i+=1;}
 Public16{variant:kani::any(),pool:kani::any(),domain:kani::any(),anchor:digest(),nullifier:digest(),asset:M31(kani::any()),recipient:if kani::any(){Some(digest())}else{None},change:digest(),amount:kani::any(),transition:PoolV1PairLatePublicStatementV1{live_snapshot:PoolV1PairLiveSnapshotV1{pool:kani::any(),deployment_domain:kani::any(),sequence:kani::any(),next_pair_index:kani::any(),current_root:digest(),frontier:before},candidate_afterstate:PoolV1PairVerifiedAfterstateV1{next_pair_index:kani::any(),next_root:digest(),next_frontier:after}}}}
#[allow(dead_code)] fn type_anchor(_:QM31){}
