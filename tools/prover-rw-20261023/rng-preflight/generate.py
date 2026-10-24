"""Derive isolated owner directly from the actual H5-aligned source."""
from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parents[3]
D=Path(__file__).resolve().parent
p=R/'crates/aspis-prover/src/state_only_entropy.rs';s=p.read_text()
a=s.index('    pub fn generate_for_mask_nonce(');b=s.index('    pub fn mask_nonce(',a)
body=s[a:b]; old=body
body=body.replace('pub fn generate_for_mask_nonce(', 'pub fn generate_with<P: Draw64>(')
body=body.replace('mask_nonce: [u8; 32],\n    ) -> Result<Self, StateOnlyAttemptEntropyError>', 'mask_nonce: [u8; 32],\n        mut provider: P,\n    ) -> (P, Result<Self, StateOnlyAttemptEntropyError>)')
body=body.replace('return Err(StateOnlyAttemptEntropyError::RepeatedZeroBlock);','return (provider, Err(StateOnlyAttemptEntropyError::RepeatedZeroBlock));')
body=body.replace('getrandom::fill(bytes.as_mut())?;', '''let (after, result) = provider.fill(&mut bytes);
            provider = after;
            if let Err(e) = result { return (provider, Err(StateOnlyAttemptEntropyError::Os(e))); }''')
body=body.replace('return Ok(Self {', 'return (provider, Ok(Self {').replace('                });','                }));')
body=body.replace('        Err(StateOnlyAttemptEntropyError::RepeatedZeroBlock)','        (provider, Err(StateOnlyAttemptEntropyError::RepeatedZeroBlock))')
start=s.index('#[inline(always)]\nfn entropy_nonzero32');end=s.index('impl StateOnlyAttemptSecrets',start)
helpers=s[start:end]
header='''// Source-derived extraction prototype; not a native provider installation.
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
'''
(D/'prototype/lib.rs').write_text(header+helpers+'impl StateOnlyAttemptSecrets {\n'+body+'}\n')
def pin(x):return {'sha256':hashlib.sha256(x.encode()).hexdigest(),'bytes':len(x.encode())}
(D/'source-map.json').write_text(json.dumps({'source_revision':'71100fccbd960c13cc43ba03fd4aacf39e510b34','qualified_owner':'aspis_prover::state_only_entropy::StateOnlyAttemptSecrets::generate_for_mask_nonce','source_path':str(p.relative_to(R)),'whole_source':pin(s),'source_owner':pin(old),'prototype_owner':pin(body),'source_helper':pin(helpers),'edits':['owned provider parameter and return on all exits','replace single fill by provider.fill, retain returned provider on OS failure','OS error carrier u8 in prototype only; no claim about native error representation'],'native_source_changed':False},indent=2)+'\n')
