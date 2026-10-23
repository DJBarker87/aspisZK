pub fn prove_for_proof_accounts(
    public: Public<'_>,
    compiled: &PoolV1PairForestMergedC1CompilationV1,
    hash: HashFn,
    nonce_store: &mut DurableStateOnlyMaskNonceStore,
    mut proof_account: impl FnMut(usize) -> [u8; 32],
) -> Result<RetriedProof, Error> {
    prover::prove_masked_retrying_with(public, compiled, Variant::S2, hash, nonce_store, |k| {
        StateOnlyAttemptSecrets::generate_for_mask_nonce(proof_account(k)).map_err(|_| Error::Entropy)
    })
}
