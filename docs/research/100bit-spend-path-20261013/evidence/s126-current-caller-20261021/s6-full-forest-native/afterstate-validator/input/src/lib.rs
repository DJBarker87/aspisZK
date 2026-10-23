#![allow(unexpected_cfgs)]
#[cfg(kani)]
mod proofs {
 use aspis_statement::pool_v1::{
  pair_tree_profile::{PoolV1PairLiveSnapshotV1,PoolV1PairLiveSnapshotErrorV1,kani_validate_snapshot,kani_digest_canonical as digest_is_canonical},
  pair_terminal::{PoolV1PairVerifiedAfterstateV1,PoolV1PairVerifierTransportErrorV1,kani_validate_afterstate},
  POOL_V1_PAIR_CAPACITY};
fn reference_snapshot(
    snapshot: &PoolV1PairLiveSnapshotV1,
) -> Result<(), PoolV1PairLiveSnapshotErrorV1> {
    if snapshot.pool == [0u8; 32] || snapshot.deployment_domain == [0u8; 32] {
        return Err(PoolV1PairLiveSnapshotErrorV1::ZeroRequiredBinding);
    }
    if snapshot.sequence != snapshot.next_pair_index {
        return Err(PoolV1PairLiveSnapshotErrorV1::SequenceIndexMismatch);
    }
    if snapshot.next_pair_index >= POOL_V1_PAIR_CAPACITY {
        return Err(PoolV1PairLiveSnapshotErrorV1::TreeFull);
    }
    if !digest_is_canonical(&snapshot.current_root) {
        return Err(PoolV1PairLiveSnapshotErrorV1::NonCanonicalDigest);
    }
    if !digest_is_canonical(&snapshot.frontier[0]) {return Err(PoolV1PairLiveSnapshotErrorV1::NonCanonicalDigest);}
    if !digest_is_canonical(&snapshot.frontier[1]) {return Err(PoolV1PairLiveSnapshotErrorV1::NonCanonicalDigest);}
    if !digest_is_canonical(&snapshot.frontier[2]) {return Err(PoolV1PairLiveSnapshotErrorV1::NonCanonicalDigest);}
    if !digest_is_canonical(&snapshot.frontier[3]) {return Err(PoolV1PairLiveSnapshotErrorV1::NonCanonicalDigest);}
    if !digest_is_canonical(&snapshot.frontier[4]) {return Err(PoolV1PairLiveSnapshotErrorV1::NonCanonicalDigest);}
    if !digest_is_canonical(&snapshot.frontier[5]) {return Err(PoolV1PairLiveSnapshotErrorV1::NonCanonicalDigest);}
    if !digest_is_canonical(&snapshot.frontier[6]) {return Err(PoolV1PairLiveSnapshotErrorV1::NonCanonicalDigest);}
    if !digest_is_canonical(&snapshot.frontier[7]) {return Err(PoolV1PairLiveSnapshotErrorV1::NonCanonicalDigest);}
    if !digest_is_canonical(&snapshot.frontier[8]) {return Err(PoolV1PairLiveSnapshotErrorV1::NonCanonicalDigest);}
    if !digest_is_canonical(&snapshot.frontier[9]) {return Err(PoolV1PairLiveSnapshotErrorV1::NonCanonicalDigest);}
    if !digest_is_canonical(&snapshot.frontier[10]) {return Err(PoolV1PairLiveSnapshotErrorV1::NonCanonicalDigest);}
    if !digest_is_canonical(&snapshot.frontier[11]) {return Err(PoolV1PairLiveSnapshotErrorV1::NonCanonicalDigest);}
    if !digest_is_canonical(&snapshot.frontier[12]) {return Err(PoolV1PairLiveSnapshotErrorV1::NonCanonicalDigest);}
    if !digest_is_canonical(&snapshot.frontier[13]) {return Err(PoolV1PairLiveSnapshotErrorV1::NonCanonicalDigest);}
    if !digest_is_canonical(&snapshot.frontier[14]) {return Err(PoolV1PairLiveSnapshotErrorV1::NonCanonicalDigest);}
    if !digest_is_canonical(&snapshot.frontier[15]) {return Err(PoolV1PairLiveSnapshotErrorV1::NonCanonicalDigest);}
    if !digest_is_canonical(&snapshot.frontier[16]) {return Err(PoolV1PairLiveSnapshotErrorV1::NonCanonicalDigest);}
    if !digest_is_canonical(&snapshot.frontier[17]) {return Err(PoolV1PairLiveSnapshotErrorV1::NonCanonicalDigest);}
    if !digest_is_canonical(&snapshot.frontier[18]) {return Err(PoolV1PairLiveSnapshotErrorV1::NonCanonicalDigest);}
    if !digest_is_canonical(&snapshot.frontier[19]) {return Err(PoolV1PairLiveSnapshotErrorV1::NonCanonicalDigest);}
    Ok(())
}
fn reference_afterstate(
    afterstate: &PoolV1PairVerifiedAfterstateV1,
) -> Result<(), PoolV1PairVerifierTransportErrorV1> {
    if afterstate.next_pair_index == 0 || afterstate.next_pair_index > POOL_V1_PAIR_CAPACITY
    {
        return Err(PoolV1PairVerifierTransportErrorV1::InvalidAfterstateIndex);
    }
    if !digest_is_canonical(&afterstate.next_root) {
        return Err(PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate);
    }
    if !digest_is_canonical(&afterstate.next_frontier[0]) {return Err(PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate);}
    if !digest_is_canonical(&afterstate.next_frontier[1]) {return Err(PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate);}
    if !digest_is_canonical(&afterstate.next_frontier[2]) {return Err(PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate);}
    if !digest_is_canonical(&afterstate.next_frontier[3]) {return Err(PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate);}
    if !digest_is_canonical(&afterstate.next_frontier[4]) {return Err(PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate);}
    if !digest_is_canonical(&afterstate.next_frontier[5]) {return Err(PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate);}
    if !digest_is_canonical(&afterstate.next_frontier[6]) {return Err(PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate);}
    if !digest_is_canonical(&afterstate.next_frontier[7]) {return Err(PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate);}
    if !digest_is_canonical(&afterstate.next_frontier[8]) {return Err(PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate);}
    if !digest_is_canonical(&afterstate.next_frontier[9]) {return Err(PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate);}
    if !digest_is_canonical(&afterstate.next_frontier[10]) {return Err(PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate);}
    if !digest_is_canonical(&afterstate.next_frontier[11]) {return Err(PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate);}
    if !digest_is_canonical(&afterstate.next_frontier[12]) {return Err(PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate);}
    if !digest_is_canonical(&afterstate.next_frontier[13]) {return Err(PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate);}
    if !digest_is_canonical(&afterstate.next_frontier[14]) {return Err(PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate);}
    if !digest_is_canonical(&afterstate.next_frontier[15]) {return Err(PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate);}
    if !digest_is_canonical(&afterstate.next_frontier[16]) {return Err(PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate);}
    if !digest_is_canonical(&afterstate.next_frontier[17]) {return Err(PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate);}
    if !digest_is_canonical(&afterstate.next_frontier[18]) {return Err(PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate);}
    if !digest_is_canonical(&afterstate.next_frontier[19]) {return Err(PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate);}
    Ok(())
}
 #[kani::proof]
 #[kani::unwind(128)]
 fn snapshot_validator_matches_unrolled() {
  let value:PoolV1PairLiveSnapshotV1=unsafe{core::mem::transmute(kani::any::<[u8;core::mem::size_of::<PoolV1PairLiveSnapshotV1>()]>())};
  assert_eq!(kani_validate_snapshot(&value),reference_snapshot(&value));
 }
 #[kani::proof]
 #[kani::unwind(128)]
 fn afterstate_validator_matches_unrolled() {
  let value:PoolV1PairVerifiedAfterstateV1=unsafe{core::mem::transmute(kani::any::<[u8;core::mem::size_of::<PoolV1PairVerifiedAfterstateV1>()]>())};
  assert_eq!(kani_validate_afterstate(&value),reference_afterstate(&value));
 }
}
