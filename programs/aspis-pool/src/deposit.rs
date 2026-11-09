//! Shared pair-forest initialization/request data.

use aspis_statement::poseidon2::Digest;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DepositRequestV1<'a> {
    pub owner_key: Digest,
    pub amount: u32,
    pub salt: Digest,
    pub encrypted_note_payload: &'a [u8],
}
