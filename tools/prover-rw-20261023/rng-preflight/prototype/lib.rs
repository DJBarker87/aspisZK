// Source-derived extraction prototype; not a native provider installation.
use zeroize::Zeroizing;
const ENTROPY_RETRY_LIMIT: usize = 16;
#[derive(Debug, PartialEq, Eq)]
pub enum StateOnlyAttemptEntropyError { Os(u8), RepeatedZeroBlock }
pub struct StateOnlyAttemptSecrets {
    pub mask_nonce: [u8;32],
    pub field_mask_entropy: Zeroizing<[u8;32]>,
    pub leaf_salt_seed: Zeroizing<[u8;32]>,
}
pub trait Draw64: Sized {
    fn fill(self, bytes: &mut [u8;64]) -> (Self, Result<(),u8>);
}
// Finite tape consumption is explicit, also on OS error with partial writes.
pub struct Tape { pub replies: Vec<([u8;64], Result<(),u8>)>, pub used: usize }
impl Draw64 for Tape {
    fn fill(mut self, bytes: &mut [u8;64]) -> (Self, Result<(),u8>) {
        assert!(self.used < self.replies.len()); // tape exhaustion is outside admitted executions
        let (block, result) = self.replies[self.used];
        self.used += 1;
        *bytes = block;
        (self, result)
    }
}
pub fn owner(nonce: [u8;32], tape: Tape) -> (Tape, Result<StateOnlyAttemptSecrets,StateOnlyAttemptEntropyError>) {
    StateOnlyAttemptSecrets::generate_with(nonce, tape)
}
#[inline(always)]
fn entropy_nonzero32(bytes:&[u8;32])->bool {
    let mut combined=0u8;let mut i=0;
    while i<32 {combined|=bytes[i];i+=1;}
    combined!=0
}

impl StateOnlyAttemptSecrets {
    pub fn generate_with<P: Draw64>(
        mask_nonce: [u8; 32],
        mut provider: P,
    ) -> (P, Result<Self, StateOnlyAttemptEntropyError>) {
        let limit=ENTROPY_RETRY_LIMIT;

        if !entropy_nonzero32(&mask_nonce) {
            return (provider, Err(StateOnlyAttemptEntropyError::RepeatedZeroBlock));
        }
        let mut retry=0;
        while retry<limit {
            let mut bytes = Zeroizing::new([0u8; 64]);
            let (after, result) = provider.fill(&mut bytes);
            provider = after;
            if let Err(e) = result { return (provider, Err(StateOnlyAttemptEntropyError::Os(e))); }

            let mut field_mask_entropy = Zeroizing::new([0u8; 32]);
            let mut leaf_salt_seed = Zeroizing::new([0u8; 32]);
            field_mask_entropy.copy_from_slice(&bytes[..32]);
            leaf_salt_seed.copy_from_slice(&bytes[32..]);
            if entropy_nonzero32(&field_mask_entropy) && entropy_nonzero32(&leaf_salt_seed) {
                return (provider, Ok(Self {
                    mask_nonce,
                    field_mask_entropy,
                    leaf_salt_seed,
                }));
            }
            retry+=1;
        }
        (provider, Err(StateOnlyAttemptEntropyError::RepeatedZeroBlock))
    }

}
