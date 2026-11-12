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

/// pv-aspis-rw: first-order form of `prove_for_proof_accounts`, for callers
/// that fix the eight proof-account keys before proving. `nonces[k]` is the
/// public key of the proof account of attempt `k`. It behaves as
/// `prove_for_proof_accounts` does when given a `proof_account` that returns
/// `nonces[k]` and has no other effect: the same retry loop, the same
/// reservation in the durable ledger before any mask or salt is derived, the
/// same errors and the same eight-attempt cap; attempt `k` reads `nonces[k]`
/// only when it is entered, and its two private seeds are drawn from the OS at
/// that moment, as before. `prove_for_proof_accounts` itself is unchanged: it
/// asks its callback for a key only when an attempt is entered, which a
/// callback can observe, so it is not defined through this function
/// (evidence/pv-aspis-rewrite-20261111/notes/08-prove_for_proof_accounts.md).
pub fn prove_for_proof_account_nonces(
    public: Public<'_>,
    compiled: &PoolV1PairForestMergedC1CompilationV1,
    hash: HashFn,
    nonce_store: &mut DurableStateOnlyMaskNonceStore,
    nonces: &[[u8; 32]; prover::ATTEMPT_CAP],
) -> Result<RetriedProof, Error> {
    // Shell: the check times of the call reach this thread's store when
    // `times` is dropped, as with every other public entry point.
    let mut times = prover::CheckTimesShell::default();
    prove_for_proof_account_nonces_timed(public, compiled, hash, nonce_store, nonces, &mut times.log)
}

/// pv-aspis-rw: `prove_for_proof_account_nonces` without thread-local state and
/// without a function-typed argument; the durations of the P_R1 checks are
/// appended to `times`.
pub fn prove_for_proof_account_nonces_timed(
    public: Public<'_>,
    compiled: &PoolV1PairForestMergedC1CompilationV1,
    hash: HashFn,
    nonce_store: &mut DurableStateOnlyMaskNonceStore,
    nonces: &[[u8; 32]; prover::ATTEMPT_CAP],
    times: &mut prover::CheckTimesLog,
) -> Result<RetriedProof, Error> {
    let mut provider = ProofAccountNonces { nonces: *nonces };
    prover::prove_masked_retrying_from_timed(public, compiled, Variant::S2, hash, nonce_store, &mut provider, times)
}

/// pv-aspis-rw: the secrets provider of `prove_for_proof_account_nonces`.
/// The retry loop calls it only for `k < ATTEMPT_CAP`.
struct ProofAccountNonces {
    nonces: [[u8; 32]; prover::ATTEMPT_CAP],
}
impl prover::AttemptSecretsProvider for ProofAccountNonces {
    fn attempt_secrets(&mut self, k: usize) -> Result<StateOnlyAttemptSecrets, Error> {
        StateOnlyAttemptSecrets::generate_for_mask_nonce(self.nonces[k]).map_err(|_| Error::Entropy)
    }
}

#[cfg(test)]
#[path = "RealR1_client_tests.rs"]
mod tests;
