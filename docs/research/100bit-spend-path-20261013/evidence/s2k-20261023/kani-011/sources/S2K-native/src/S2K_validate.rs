fn validate_verified_afterstate(
    afterstate: &PoolV1PairVerifiedAfterstateV1,
) -> Result<(), PoolV1PairVerifierTransportErrorV1> {
    if afterstate.next_pair_index == 0 || afterstate.next_pair_index > super::POOL_V1_PAIR_CAPACITY
    {
        return Err(PoolV1PairVerifierTransportErrorV1::InvalidAfterstateIndex);
    }
    if !super::pair_tree_profile::digest_is_canonical(&afterstate.next_root) {
        return Err(PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate);
    }
    let mut level = 0;
    while level < afterstate.next_frontier.len() {
        if !super::pair_tree_profile::digest_is_canonical(&afterstate.next_frontier[level]) {
            return Err(PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate);
        }
        level += 1;
    }
    Ok(())
}

