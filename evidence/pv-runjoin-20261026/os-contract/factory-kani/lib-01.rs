include!("selected.rs");

#[cfg(kani)]
mod proofs {
    use super::*;

    // Actual whole selected factory and real dependencies, no replacement
    // getrandom function or stub. This branch must stop before native IO.
    #[kani::proof]
    #[kani::unwind(34)]
    fn zero_nonce_stops_before_os() {
        let result = StateOnlyAttemptSecrets::generate_for_mask_nonce([0; 32]);
        assert!(matches!(result, Err(StateOnlyAttemptEntropyError::RepeatedZeroBlock)));
    }
}
