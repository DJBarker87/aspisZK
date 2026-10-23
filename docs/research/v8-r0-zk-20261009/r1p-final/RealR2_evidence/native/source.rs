// Exact function bodies copied by harness/source_check.py; no shipped file edit.
const STATE_ONLY_HIDING_CONTEXT_BYTES:usize=81;
const STATE_ONLY_HIDING_CONTEXT_VERSION:u8=1;
const MASK_SEED_DOMAIN:&[u8]=b"aspis:state-only:private-mask-seed:v1";
type HashFn=fn(&[&[u8]])->[u8;32];
#[derive(Clone,Copy)]
struct StateOnlyHidingContext {
statement_digest:[u8;32], mask_nonce:[u8;32], mask_layout_fingerprint:u64, layout_factor_fingerprint:u64,
}
#[derive(Debug,PartialEq)]
enum StateOnlyMaskBuildError {ZeroPrivateEntropy}
impl StateOnlyHidingContext {
    pub fn encode(self) -> [u8; STATE_ONLY_HIDING_CONTEXT_BYTES] {
        let mut encoded = [0u8; STATE_ONLY_HIDING_CONTEXT_BYTES];
        encoded[0] = STATE_ONLY_HIDING_CONTEXT_VERSION;
        encoded[1..33].copy_from_slice(&self.statement_digest);
        encoded[33..65].copy_from_slice(&self.mask_nonce);
        encoded[65..73].copy_from_slice(&self.mask_layout_fingerprint.to_le_bytes());
        encoded[73..81].copy_from_slice(&self.layout_factor_fingerprint.to_le_bytes());
        encoded
    }
}
fn derive_state_only_mask_seed_from_entropy_ref(
    hash: HashFn,
    precommit_binding: [u8; 32],
    context: StateOnlyHidingContext,
    private_entropy: &[u8; 32],
) -> Result<[u8; 32], StateOnlyMaskBuildError> {
    if *private_entropy == [0; 32] {
        return Err(StateOnlyMaskBuildError::ZeroPrivateEntropy);
    }
    Ok(hash(&[
        MASK_SEED_DOMAIN,
        &precommit_binding,
        &context.encode(),
        private_entropy,
    ]))
}
