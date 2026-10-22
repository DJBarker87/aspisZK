// Verbatim shipped function; type/callee substitutes are in lib.rs.
pub fn prove_masked_retrying_with(
    public:Public<'_>,
    compiled:&PoolV1PairForestMergedC1CompilationV1,
    variant:Variant,
    hash:HashFn,
    nonce_store:&mut DurableStateOnlyMaskNonceStore,
    mut next_attempt:impl FnMut(usize)->Result<StateOnlyAttemptSecrets,Error>,
)->Result<RetriedProof,Error> {
    if variant!=Variant::S2 { return Err(Error::Semantic); }
    for k in 0..ATTEMPT_CAP {
        let attempt=next_attempt(k)?;
        match prove_masked_attempt(public,compiled,variant,hash,attempt,nonce_store) {
            Ok((proof,audit))=>return Ok(RetriedProof{proof,audit,attempts:k+1}),
            Err(Error::Rejected)=>continue,
            Err(e)=>return Err(e),
        }
    }
    Err(Error::AttemptsExhausted)
}
