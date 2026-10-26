//! Host-side proof-account caller selected in LOG D162.
use aspis_core::HashFn;
use aspis_prover::state_only_entropy::{DurableStateOnlyMaskNonceStore, StateOnlyAttemptSecrets};
use aspis_statement::pool_v1::{
    pair_forest_semantic_terminal::r0::Public,
    pair_forest_trace::PoolV1PairForestMergedC1CompilationV1,
};
use crate::{prover::{self, RetriedProof}, transport::Variant, verifier::Error};

/// Request the public key of a retained proof account for each entered attempt.
/// The client keeps the keys, including rejected attempts, and uses the key at
/// `result.attempts - 1` for the published proof account. This function handles
/// public keys only; it never creates, funds, deletes or uploads an account.
///
/// Keys may be chosen after prior attempts. The supplied durable ledger is
/// shared across calls; duplicate keys fail closed, even after rejection.
/// Only the two private 32-byte seeds come from the OS (E1); reservation uses
/// the existing atomic, persistent ledger (E2). Errors and the eight-attempt
/// cap are exactly those of `prove_masked_retrying_with`.
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

#[cfg(test)]
#[path = "RealR1_client_tests.rs"]
mod tests;
