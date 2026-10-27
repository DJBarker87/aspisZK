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

    #[kani::proof]
    #[kani::unwind(67)]
    fn native_success_postconditions() {
        let nonce: [u8; 32] = kani::any();
        kani::assume(entropy_nonzero32(&nonce));
        if let Ok(secret) = StateOnlyAttemptSecrets::generate_for_mask_nonce(nonce) {
            assert_eq!(secret.mask_nonce, nonce);
            assert!(entropy_nonzero32(&secret.field_mask_entropy));
            assert!(entropy_nonzero32(&secret.leaf_salt_seed));
        }
    }
}
