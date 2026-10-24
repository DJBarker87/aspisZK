// Source-derived extraction prototype; not a native provider installation.
use zeroize::Zeroizing;
const ENTROPY_RETRY_LIMIT: usize = 16;
#[derive(Debug, PartialEq, Eq)]
pub enum StateOnlyAttemptEntropyError { Os(getrandom::Error), RepeatedZeroBlock }
pub struct StateOnlyAttemptSecrets {
    pub mask_nonce: [u8;32],
    pub field_mask_entropy: Zeroizing<[u8;32]>,
    pub leaf_salt_seed: Zeroizing<[u8;32]>,
}
pub trait Draw64: Sized {
    fn fill(self, bytes: &mut [u8;64]) -> (Self, Result<(),getrandom::Error>);
}
// Finite tape consumption is explicit, also on OS error with partial writes.
pub struct Tape { pub replies: Vec<([u8;64], Result<(),getrandom::Error>)>, pub used: usize }
impl Draw64 for Tape {
    fn fill(mut self, bytes: &mut [u8;64]) -> (Self, Result<(),getrandom::Error>) {
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
            if let Err(e) = result { return (provider, Err(StateOnlyAttemptEntropyError::from(e))); }

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

impl From<getrandom::Error> for StateOnlyAttemptEntropyError {
    fn from(value: getrandom::Error) -> Self { Self::Os(value) }
}
#[derive(Debug,Clone,Copy,PartialEq,Eq)]
pub enum Error { Parse,Semantic,Transcript,Relation,Merkle,Query,Checkpoint,Allocation,
    Rejected,AttemptsExhausted,Entropy }
pub struct RetriedProof { pub proof:Vec<u8>, pub audit:u64, pub attempts:usize }
pub const ATTEMPT_CAP:usize=8;
// The actual body and durable store remain a local interface, not a refinement premise.
pub fn selected_callback<N: FnMut(usize)->[u8;32]>(
    tape:Tape, mut proof_account:N, k:usize,
)->(Tape,N,Result<StateOnlyAttemptSecrets,Error>) {
    let nonce=proof_account(k);
    let (tape,status)=StateOnlyAttemptSecrets::generate_with(nonce,tape);
    (tape,proof_account,status.map_err(|_|Error::Entropy))
}
pub fn retry_attempt<N,L,B>(tape:Tape, proof_account:N, mut nonce_store:L, mut body:B,k:usize)
 ->(Tape,N,L,B,Result<RetriedProof,Error>)
 where N:FnMut(usize)->[u8;32],
 B:FnMut(StateOnlyAttemptSecrets,L)->(L,Result<(Vec<u8>,u64),Error>) {
    if k>=ATTEMPT_CAP { return (tape,proof_account,nonce_store,body,Err(Error::AttemptsExhausted)); }
    let (tape,proof_account,status)=selected_callback(tape,proof_account,k);
    let attempt=match status {Ok(a)=>a,Err(e)=>return (tape,proof_account,nonce_store,body,Err(e))};
    let (after_store,result)=body(attempt,nonce_store);
    nonce_store=after_store;
    match result {
        Ok((proof,audit))=>(tape,proof_account,nonce_store,body,Ok(RetriedProof{proof,audit,attempts:k+1})),
        Err(Error::Rejected)=>retry_attempt(tape,proof_account,nonce_store,body,k+1),
        Err(e)=>(tape,proof_account,nonce_store,body,Err(e)),
    }
}
pub fn prove_masked_retrying_with<N,L,B>(is_s2:bool,tape:Tape,proof_account:N,nonce_store:L,body:B)
 ->(Tape,N,L,B,Result<RetriedProof,Error>)
 where N:FnMut(usize)->[u8;32],
 B:FnMut(StateOnlyAttemptSecrets,L)->(L,Result<(Vec<u8>,u64),Error>) {
    if !is_s2 { return (tape,proof_account,nonce_store,body,Err(Error::Semantic)); }
    retry_attempt(tape,proof_account,nonce_store,body,0)
}
