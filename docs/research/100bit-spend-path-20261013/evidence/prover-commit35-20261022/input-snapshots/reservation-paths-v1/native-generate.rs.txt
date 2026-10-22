impl StateOnlyAttemptSecrets {
pub fn generate() -> Result<Self, StateOnlyAttemptEntropyError> {
        for _ in 0..ENTROPY_RETRY_LIMIT {
            let mut bytes = Zeroizing::new([0u8; 96]);
            getrandom::fill(bytes.as_mut())?;

            let mut mask_nonce = [0u8; 32];
            let mut field_mask_entropy = Zeroizing::new([0u8; 32]);
            let mut leaf_salt_seed = Zeroizing::new([0u8; 32]);
            mask_nonce.copy_from_slice(&bytes[..32]);
            field_mask_entropy.copy_from_slice(&bytes[32..64]);
            leaf_salt_seed.copy_from_slice(&bytes[64..]);

            if mask_nonce != [0; 32] && *field_mask_entropy != [0; 32] && *leaf_salt_seed != [0; 32]
            {
                return Ok(Self {
                    mask_nonce,
                    field_mask_entropy,
                    leaf_salt_seed,
                });
            }
        }
        Err(StateOnlyAttemptEntropyError::RepeatedZeroBlock)
    }
}
