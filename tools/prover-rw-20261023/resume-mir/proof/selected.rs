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

// Prospective native request/resume implementation, not installed.
struct ProverRwResumeScalarRequest {
    mask_nonce: [u8; 32],
    retry: usize,
}

struct ProverRwResumeScalarDraw {
    request: ProverRwResumeScalarRequest,
    bytes: Zeroizing<[u8; 64]>,
    outcome: Result<(), getrandom::Error>,
}

enum ProverRwResumeScalarControl {
    More(ProverRwResumeScalarRequest),
    Done,
}

impl ProverRwResumeScalarRequest {
    fn start(mask_nonce: [u8; 32]) -> Result<Self, StateOnlyAttemptEntropyError> {
        if !entropy_nonzero32(&mask_nonce) {
            return Err(StateOnlyAttemptEntropyError::RepeatedZeroBlock);
        }
        Ok(Self { mask_nonce, retry: 0 })
    }

    // Native effect producer. Never interpret this as a fixed pure dictionary.
    fn draw(self) -> ProverRwResumeScalarDraw {
        let mut bytes = Zeroizing::new([0u8; 64]);
        let outcome = getrandom::fill(bytes.as_mut());
        ProverRwResumeScalarDraw { request: self, bytes, outcome }
    }
}

impl ProverRwResumeScalarDraw {
    fn resume(self) -> (
        ProverRwResumeScalarControl,
        Result<Option<StateOnlyAttemptSecrets>, StateOnlyAttemptEntropyError>,
    ) {
        let Self { mut request, bytes, outcome } = self;
        match outcome {
            Err(error) => return (
                ProverRwResumeScalarControl::Done,
                Err(StateOnlyAttemptEntropyError::from(error)),
            ),
            Ok(()) => (),
        }
        let mut field_mask_entropy = Zeroizing::new([0u8; 32]);
        let mut leaf_salt_seed = Zeroizing::new([0u8; 32]);
        field_mask_entropy.copy_from_slice(&bytes[..32]);
        leaf_salt_seed.copy_from_slice(&bytes[32..]);
        if entropy_nonzero32(&field_mask_entropy) && entropy_nonzero32(&leaf_salt_seed) {
            return (
                ProverRwResumeScalarControl::Done,
                Ok(Some(StateOnlyAttemptSecrets {
                    mask_nonce: request.mask_nonce,
                    field_mask_entropy,
                    leaf_salt_seed,
                })),
            );
        }
        request.retry += 1;
        if request.retry < ENTROPY_RETRY_LIMIT {
            (ProverRwResumeScalarControl::More(request), Ok(None))
        } else {
            (
                ProverRwResumeScalarControl::Done,
                Err(StateOnlyAttemptEntropyError::RepeatedZeroBlock),
            )
        }
    }
}

impl StateOnlyAttemptSecrets {
    pub fn generate_for_mask_nonce(
        mask_nonce: [u8; 32],
    ) -> Result<Self, StateOnlyAttemptEntropyError> {
        let mut request = ProverRwResumeScalarRequest::start(mask_nonce)?;
        loop {
            let (control, result) = request.draw().resume();
            match result {
                Err(error) => return Err(error),
                Ok(Some(owner)) => return Ok(owner),
                Ok(None) => match control {
                    ProverRwResumeScalarControl::More(next) => request = next,
                    ProverRwResumeScalarControl::Done => {
                        return Err(StateOnlyAttemptEntropyError::RepeatedZeroBlock);
                    }
                },
            }
        }
    }
}
