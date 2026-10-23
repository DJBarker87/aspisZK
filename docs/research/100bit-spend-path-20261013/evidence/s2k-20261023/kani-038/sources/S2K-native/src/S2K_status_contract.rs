// Pure native afterstate encoder, exact status contract; payload bytes remain
// unconstrained here. All native errors are retained, not replaced by success.
#[kani::requires(expected == validator_parent::inner::run(afterstate))]
#[kani::ensures(|reply| reply.map(|_| ()) == expected)]
fn S2K_encode_status(afterstate: &PoolV1PairVerifiedAfterstateV1,
    expected: Result<(),PoolV1PairVerifierTransportErrorV1>)
    -> Result<[u8;688],PoolV1PairVerifierTransportErrorV1> {
    encode_pool_v1_pair_verified_afterstate_v1(afterstate)
}
#[kani::proof_for_contract(S2K_encode_status)]
#[kani::unwind(34)]
fn S2K_encode_status_contract() {
    let a=PoolV1PairVerifiedAfterstateV1 {
        next_pair_index:kani::any(),next_root:digest(),
        next_frontier:core::array::from_fn(|_|digest()),
    };
    let expected=validator_parent::inner::run(&a);
    let reply=S2K_encode_status(&a,expected);
    kani::cover!(reply.is_ok());
}
