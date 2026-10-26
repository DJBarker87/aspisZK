use zeroize::Zeroizing;
const ENTROPY_RETRY_LIMIT: usize = 16;
pub enum StateOnlyAttemptEntropyError {
    Os(getrandom::Error),
    RepeatedZeroBlock,
}
pub struct StateOnlyAttemptSecrets {
    mask_nonce: [u8; 32],
    field_mask_entropy: Zeroizing<[u8; 32]>,
    leaf_salt_seed: Zeroizing<[u8; 32]>,
}
fn entropy_nonzero32(bytes:&[u8;32])->bool {
    let mut combined=0u8;let mut i=0;
    while i<32 {combined|=bytes[i];i+=1;}
    combined!=0
}
impl StateOnlyAttemptSecrets {
    pub fn generate_for_mask_nonce(
        mask_nonce: [u8; 32],
    ) -> Result<Self, StateOnlyAttemptEntropyError> {
        let limit=ENTROPY_RETRY_LIMIT;

        if !entropy_nonzero32(&mask_nonce) {
            return Err(StateOnlyAttemptEntropyError::RepeatedZeroBlock);
        }
        let mut retry=0;
        while retry<limit {
            let mut bytes = Zeroizing::new([0u8; 64]);
            getrandom::fill(bytes.as_mut())?;

            let mut field_mask_entropy = Zeroizing::new([0u8; 32]);
            let mut leaf_salt_seed = Zeroizing::new([0u8; 32]);
            field_mask_entropy.copy_from_slice(&bytes[..32]);
            leaf_salt_seed.copy_from_slice(&bytes[32..]);
            if entropy_nonzero32(&field_mask_entropy) && entropy_nonzero32(&leaf_salt_seed) {
                return Ok(Self {
                    mask_nonce,
                    field_mask_entropy,
                    leaf_salt_seed,
                });
            }
            retry+=1;
        }
        Err(StateOnlyAttemptEntropyError::RepeatedZeroBlock)
    }
}
impl From<getrandom::Error> for StateOnlyAttemptEntropyError {
    fn from(value: getrandom::Error) -> Self {
        Self::Os(value)
    }
}
fn main() {
    // A public, fixed non-wallet nonce. No account or key is created.
    let nonce = [1u8; 32];
    let first = match StateOnlyAttemptSecrets::generate_for_mask_nonce(nonce) {
        Ok(value) => value, Err(_) => panic!("native first call failed") };
    let second = match StateOnlyAttemptSecrets::generate_for_mask_nonce(nonce) {
        Ok(value) => value, Err(_) => panic!("native second call failed") };
    assert_eq!(first.mask_nonce, nonce);
    assert_eq!(second.mask_nonce, nonce);
    let distinct = first.field_mask_entropy != second.field_mask_entropy ||
        first.leaf_salt_seed != second.leaf_salt_seed;
    assert!(distinct, "native successive successful outputs coincided");
    println!("same_public_nonce=true native_successes=2 private_output_distinct=true");
    // Zeroizing owns both private seeds. No entropy bytes or hashes are logged.
}
