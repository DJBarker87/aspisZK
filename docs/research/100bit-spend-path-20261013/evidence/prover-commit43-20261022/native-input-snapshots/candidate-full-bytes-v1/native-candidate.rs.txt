impl StateOnlyAttemptSecrets {
fn candidate(mask_nonce:[u8;32])->Option<Result<Self,StateOnlyAttemptEntropyError>> {
            let mut bytes = Zeroizing::new([0u8; 64]);
            if getrandom::fill(bytes.as_mut()).is_err() { return Some(Err(StateOnlyAttemptEntropyError::Os)); }

            let mut field_mask_entropy = Zeroizing::new([0u8; 32]);
            let mut leaf_salt_seed = Zeroizing::new([0u8; 32]);
            field_mask_entropy.copy_from_slice(&bytes[..32]);
            leaf_salt_seed.copy_from_slice(&bytes[32..]);
            if *field_mask_entropy != [0; 32] && *leaf_salt_seed != [0; 32] {
                return Some(Ok(Self {
                    mask_nonce,
                    field_mask_entropy,
                    leaf_salt_seed,
                }));
            }
 None
}
}
