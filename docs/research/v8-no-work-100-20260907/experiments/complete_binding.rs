//! Research-only profile/attempt binding; no production registration.
pub const V7_POOL_PAIR_FOREST_TAG73_STATEMENT_DIGEST_DOMAIN: &[u8] = b"aspis/research/v8/asf8-statement-digest/v1";
pub const V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING_PREIMAGE: &[u8] = b"aspis:research:v8:pool-v1:qm31-q22:asq8-asf8-asr8:v1";
pub const V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING: [u8;32] = [121,147,51,56,96,194,205,16,170,24,62,117,31,39,16,186,39,155,51,42,187,191,221,206,119,59,50,23,103,240,1,186];
pub const V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING_PREIMAGE: &[u8] = b"aspis:research:v8:40282:log20:canonical697:image:shifted-rows:structured-v2:no-work-credit:complete-v1";
pub const V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING: [u8;32] = [151,98,227,119,25,209,243,34,243,255,11,167,44,210,163,48,184,241,130,119,107,226,91,66,45,195,131,11,66,206,145,255];
pub fn bind_attempt(hash:aspis_core::HashFn,statement_digest:&[u8;32],verifier:&[u8;32],proof_account:&[u8;32])->[u8;32]{
    hash(&[b"aspis/research/v8/complete-attempt/v1",&V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING,&V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING,verifier,proof_account,statement_digest])
}
