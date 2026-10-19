/// Fresh R0 state, separate from Transcript's legacy all-zero IV. The
/// C1-time binding is exactly SPEC §9: public bytes and the C1 root in one
/// hash, with no profile/basis/nonce/registry pre-absorbs. Row 0 is empty.
#[derive(Clone)]
pub struct SemanticTranscript {
    state: [u8; 32],
    hash: HashFn,
    next_row: u8,
}
