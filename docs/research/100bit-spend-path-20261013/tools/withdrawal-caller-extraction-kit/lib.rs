// Exact declaration cuts; namespace layout only.
#![no_std]
#![allow(dead_code)]
pub mod aspis_core { pub mod field {
/// The Mersenne prime 2^31 - 1.
pub const P: u32 = 0x7fff_ffff;
/// M31 base field element, canonical representation in [0, P).
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct M31(pub u32);
impl M31 {
    pub fn to_le_bytes(self) -> [u8; 4] {
        self.0.to_le_bytes()
    }
}
}}
pub mod poseidon2 { use crate::aspis_core::field::M31;
pub const DIGEST_ELEMS: usize = 8;
pub type Digest = [M31; DIGEST_ELEMS];
}
use poseidon2::Digest;
pub const VALUE_LIMIT: u32 = 1 << 30;
#[inline]
pub fn encode_digest_canonical(digest: &Digest) -> [u8; 32] {
    let mut bytes = [0u8; 32];
    for (index, value) in digest.iter().enumerate() {
        bytes[index * 4..index * 4 + 4].copy_from_slice(&value.to_le_bytes());
    }
    bytes
}
pub mod pool_v1 {
pub const POOL_V1_TREE_DEPTH: usize = 20;
pub const POOL_V1_LEAF_CAPACITY: u64 = 1u64 << POOL_V1_TREE_DEPTH;
/// Eight canonical little-endian M31 limbs in 32 bytes.
pub const POOL_V1_DIGEST_ENCODING_VERSION: u8 = 1;
pub mod historical_anchor {
/// Spend shapes that consume an authenticated historical anchor.
///
/// Zero is deliberately invalid.  Deposit is absent because it consumes no
/// private input and therefore must never authorize through this envelope.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum PoolV1TransitionKind {
    PrivateTransfer = 1,
    Withdrawal = 2,
}
}
pub mod payment_relation {
use crate::aspis_core::field::{M31, P};
use crate::{poseidon2::Digest, VALUE_LIMIT, encode_digest_canonical};
use super::{POOL_V1_LEAF_CAPACITY, POOL_V1_DIGEST_ENCODING_VERSION, historical_anchor::PoolV1TransitionKind};
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1WithdrawalPublicV1 {
    pub pool: [u8; 32],
    pub deployment_domain: [u8; 32],
    pub anchor_sequence: u64,
    pub anchor_root: Digest,
    pub nullifier: Digest,
    pub asset_id: M31,
    pub amount: u32,
    pub destination_token_account: [u8; 32],
    pub change_commitment: Digest,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1PaymentStatementFormatError {
    WrongLength,
    WrongMagic,
    WrongVersion,
    WrongTransitionKind,
    WrongDigestEncoding,
    NonZeroReserved,
    ZeroRequiredBinding,
    InvalidAnchorSequence,
    NonCanonicalDigest,
    NonCanonicalAssetId,
    InvalidWithdrawalAmount,
    InvalidDestination,
    InvalidEnvelope,
    EnvelopeMismatch,
}
#[derive(Clone, Copy)]
struct CommonPublicV1 {
    pool: [u8; 32],
    deployment_domain: [u8; 32],
    anchor_sequence: u64,
    anchor_root: Digest,
    nullifier: Digest,
    asset_id: M31,
}
#[inline]
fn digest_is_canonical(digest: &Digest) -> bool {
    digest[0].0 < P
        && digest[1].0 < P
        && digest[2].0 < P
        && digest[3].0 < P
        && digest[4].0 < P
        && digest[5].0 < P
        && digest[6].0 < P
        && digest[7].0 < P
}
fn validate_common(common: CommonPublicV1) -> Result<(), PoolV1PaymentStatementFormatError> {
    if common.pool == [0u8; 32] || common.deployment_domain == [0u8; 32] {
        return Err(PoolV1PaymentStatementFormatError::ZeroRequiredBinding);
    }
    if common.anchor_sequence > POOL_V1_LEAF_CAPACITY {
        return Err(PoolV1PaymentStatementFormatError::InvalidAnchorSequence);
    }
    if !digest_is_canonical(&common.anchor_root) || !digest_is_canonical(&common.nullifier) {
        return Err(PoolV1PaymentStatementFormatError::NonCanonicalDigest);
    }
    if common.asset_id.0 >= P {
        return Err(PoolV1PaymentStatementFormatError::NonCanonicalAssetId);
    }
    Ok(())
}
fn withdrawal_common(public: &PoolV1WithdrawalPublicV1) -> CommonPublicV1 {
    CommonPublicV1 {
        pool: public.pool,
        deployment_domain: public.deployment_domain,
        anchor_sequence: public.anchor_sequence,
        anchor_root: public.anchor_root,
        nullifier: public.nullifier,
        asset_id: public.asset_id,
    }
}
pub fn validate_pool_v1_withdrawal_public_v1(
    public: &PoolV1WithdrawalPublicV1,
) -> Result<(), PoolV1PaymentStatementFormatError> {
    validate_common(withdrawal_common(public))?;
    if public.amount == 0 || public.amount >= VALUE_LIMIT {
        return Err(PoolV1PaymentStatementFormatError::InvalidWithdrawalAmount);
    }
    if public.destination_token_account == [0u8; 32] {
        return Err(PoolV1PaymentStatementFormatError::InvalidDestination);
    }
    if !digest_is_canonical(&public.change_commitment) {
        return Err(PoolV1PaymentStatementFormatError::NonCanonicalDigest);
    }
    Ok(())
}
pub const POOL_V1_PAYMENT_STATEMENT_BYTES: usize = 216;
pub const POOL_V1_PAYMENT_STATEMENT_VERSION: u8 = 1;
pub const POOL_V1_WITHDRAWAL_STATEMENT_MAGIC: [u8; 4] = *b"ASWP";
const POOL_OFFSET: usize = 8;
const DEPLOYMENT_DOMAIN_OFFSET: usize = 40;
const ANCHOR_SEQUENCE_OFFSET: usize = 72;
const ANCHOR_ROOT_OFFSET: usize = 80;
const NULLIFIER_OFFSET: usize = 112;
const ASSET_ID_OFFSET: usize = 144;
const AMOUNT_OR_RESERVED_OFFSET: usize = 148;
const FIRST_OUTPUT_OR_DESTINATION_OFFSET: usize = 152;
const SECOND_OUTPUT_OFFSET: usize = 184;
fn encode_common(
    output: &mut [u8; POOL_V1_PAYMENT_STATEMENT_BYTES],
    magic: [u8; 4],
    kind: PoolV1TransitionKind,
    common: CommonPublicV1,
) {
    output[..4].copy_from_slice(&magic);
    output[4] = POOL_V1_PAYMENT_STATEMENT_VERSION;
    output[5] = kind as u8;
    output[6] = POOL_V1_DIGEST_ENCODING_VERSION;
    output[POOL_OFFSET..DEPLOYMENT_DOMAIN_OFFSET].copy_from_slice(&common.pool);
    output[DEPLOYMENT_DOMAIN_OFFSET..ANCHOR_SEQUENCE_OFFSET]
        .copy_from_slice(&common.deployment_domain);
    output[ANCHOR_SEQUENCE_OFFSET..ANCHOR_ROOT_OFFSET]
        .copy_from_slice(&common.anchor_sequence.to_le_bytes());
    output[ANCHOR_ROOT_OFFSET..NULLIFIER_OFFSET]
        .copy_from_slice(&encode_digest_canonical(&common.anchor_root));
    output[NULLIFIER_OFFSET..ASSET_ID_OFFSET]
        .copy_from_slice(&encode_digest_canonical(&common.nullifier));
    output[ASSET_ID_OFFSET..AMOUNT_OR_RESERVED_OFFSET]
        .copy_from_slice(&common.asset_id.to_le_bytes());
}
pub fn encode_pool_v1_withdrawal_public_v1(
    public: &PoolV1WithdrawalPublicV1,
) -> Result<[u8; POOL_V1_PAYMENT_STATEMENT_BYTES], PoolV1PaymentStatementFormatError> {
    validate_pool_v1_withdrawal_public_v1(public)?;
    let mut output = [0u8; POOL_V1_PAYMENT_STATEMENT_BYTES];
    encode_common(
        &mut output,
        POOL_V1_WITHDRAWAL_STATEMENT_MAGIC,
        PoolV1TransitionKind::Withdrawal,
        withdrawal_common(public),
    );
    output[AMOUNT_OR_RESERVED_OFFSET..FIRST_OUTPUT_OR_DESTINATION_OFFSET]
        .copy_from_slice(&public.amount.to_le_bytes());
    output[FIRST_OUTPUT_OR_DESTINATION_OFFSET..SECOND_OUTPUT_OFFSET]
        .copy_from_slice(&public.destination_token_account);
    output[SECOND_OUTPUT_OFFSET..]
        .copy_from_slice(&encode_digest_canonical(&public.change_commitment));
    Ok(output)
}
}}
