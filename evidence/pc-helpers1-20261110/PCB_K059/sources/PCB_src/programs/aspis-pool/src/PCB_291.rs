use super::*;
const WRONG:[u8;32]=[0;32];
fn correct(x:&PlannedPairForestNullifierMarkerV1)->&[u8;32] {&x.seed}
fn wrong(_:&PlannedPairForestNullifierMarkerV1)->&[u8;32] {&WRONG}
#[kani::proof] #[kani::stub(PlannedPairForestNullifierMarkerV1::seed,correct)]
fn seed_correct(){let x=PlannedPairForestNullifierMarkerV1 {preparation:NullifierMarkerPreparationV1::PopulateProgramOwnedZeroed,seed:kani::any(),encoded_marker:[0;POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES]};assert!(core::ptr::eq(x.seed(),&x.seed));}
#[kani::proof] #[kani::stub(PlannedPairForestNullifierMarkerV1::seed,wrong)]
fn seed_wrong(){let x=PlannedPairForestNullifierMarkerV1 {preparation:NullifierMarkerPreparationV1::PopulateProgramOwnedZeroed,seed:kani::any(),encoded_marker:[0;POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES]};assert!(core::ptr::eq(x.seed(),&x.seed));}
