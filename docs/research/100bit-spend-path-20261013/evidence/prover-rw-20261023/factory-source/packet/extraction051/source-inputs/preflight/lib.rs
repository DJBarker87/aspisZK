// Immutable selected source items; see source-map.json.
use zeroize::Zeroizing;
const ENTROPY_RETRY_LIMIT: usize = 16;

#[derive(Debug)]
pub enum StateOnlyAttemptEntropyError {
    Os(getrandom::Error),
    RepeatedZeroBlock,
}

impl From<getrandom::Error> for StateOnlyAttemptEntropyError {
    fn from(value: getrandom::Error) -> Self {
        Self::Os(value)
    }
}

pub struct StateOnlyAttemptSecrets {
    mask_nonce: [u8; 32],
    field_mask_entropy: Zeroizing<[u8; 32]>,
    leaf_salt_seed: Zeroizing<[u8; 32]>,
}

#[inline(always)]
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
            let (next_retry, owner) = Self::one_draw(mask_nonce, retry)?;
            match owner {
                Some(owner) => return Ok(owner),
                None => retry = next_retry,
            }
        }
        Err(StateOnlyAttemptEntropyError::RepeatedZeroBlock)
    }

    fn one_draw(
        mask_nonce: [u8;32], mut retry: usize,
    ) -> Result<(usize, Option<Self>), StateOnlyAttemptEntropyError> {
        {
            let mut bytes = Zeroizing::new([0u8; 64]);
            getrandom::fill(bytes.as_mut())?;

            let mut field_mask_entropy = Zeroizing::new([0u8; 32]);
            let mut leaf_salt_seed = Zeroizing::new([0u8; 32]);
            field_mask_entropy.copy_from_slice(&bytes[..32]);
            leaf_salt_seed.copy_from_slice(&bytes[32..]);
            if entropy_nonzero32(&field_mask_entropy) && entropy_nonzero32(&leaf_salt_seed) {
                return Ok((retry, Some(Self {
                    mask_nonce,
                    field_mask_entropy,
                    leaf_salt_seed,
                })));
            }
            retry+=1;
        }
        Ok((retry, None))
    }
}
