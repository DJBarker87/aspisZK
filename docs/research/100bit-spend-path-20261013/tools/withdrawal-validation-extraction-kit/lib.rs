// Namespace-only extraction layout. Every recorded declaration is inserted verbatim.
#![no_std]
#![allow(dead_code)]
pub mod aspis_core {
    pub mod field {
/// The Mersenne prime 2^31 - 1.
pub const P: u32 = 0x7fff_ffff;
/// M31 base field element, canonical representation in [0, P).
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct M31(pub u32);
    }
}
pub mod poseidon2 {
    use crate::aspis_core::field::M31;
pub const DIGEST_ELEMS: usize = 8;
pub type Digest = [M31; DIGEST_ELEMS];
}
pub const VALUE_LIMIT: u32 = 1 << 30;
pub mod pool_v1 {
pub const POOL_V1_TREE_DEPTH: usize = 20;
pub const POOL_V1_LEAF_CAPACITY: u64 = 1u64 << POOL_V1_TREE_DEPTH;
    pub mod payment_relation {
        use crate::aspis_core::field::{M31, P};
        use crate::{poseidon2::Digest, VALUE_LIMIT};
        use super::POOL_V1_LEAF_CAPACITY;
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
    }
}
