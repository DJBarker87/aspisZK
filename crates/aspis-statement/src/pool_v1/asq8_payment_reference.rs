//! Extraction-only payment serialization. Validation stays the shipped validation.
//! The only arithmetic rewrite is the fixed-eight-word digest serialization.
use super::*;
use crate::pool_v1::{validate_pool_v1_private_transfer_public_v1,
    validate_pool_v1_withdrawal_public_v1};
use crate::pool_v1::payment_relation::{POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC,
    POOL_V1_WITHDRAWAL_STATEMENT_MAGIC, POOL_V1_PAYMENT_STATEMENT_VERSION,
    POOL_V1_CANONICAL_FEE};
const POOL_OFFSET: usize = 8;
const DEPLOYMENT_DOMAIN_OFFSET: usize = 40;
const ANCHOR_SEQUENCE_OFFSET: usize = 72;
const ANCHOR_ROOT_OFFSET: usize = 80;
const NULLIFIER_OFFSET: usize = 112;
const ASSET_ID_OFFSET: usize = 144;
const AMOUNT_OR_RESERVED_OFFSET: usize = 148;
const FIRST_OUTPUT_OR_DESTINATION_OFFSET: usize = 152;
const SECOND_OUTPUT_OFFSET: usize = 184;

#[derive(Clone, Copy)]
struct CommonPublicV1 {
    pool: [u8; 32],
    deployment_domain: [u8; 32],
    anchor_sequence: u64,
    anchor_root: Digest,
    nullifier: Digest,
    asset_id: M31,
}

fn transfer_common(public: &PoolV1PrivateTransferPublicV1) -> CommonPublicV1 {
    CommonPublicV1 {
        pool: public.pool,
        deployment_domain: public.deployment_domain,
        anchor_sequence: public.anchor_sequence,
        anchor_root: public.anchor_root,
        nullifier: public.nullifier,
        asset_id: public.asset_id,
    }
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
        .copy_from_slice(&digest_reference(&common.anchor_root));
    output[NULLIFIER_OFFSET..ASSET_ID_OFFSET]
        .copy_from_slice(&digest_reference(&common.nullifier));
    output[ASSET_ID_OFFSET..AMOUNT_OR_RESERVED_OFFSET]
        .copy_from_slice(&common.asset_id.to_le_bytes());
}

pub fn encode_pool_v1_private_transfer_public_v1(
    public: &PoolV1PrivateTransferPublicV1,
) -> Result<[u8; POOL_V1_PAYMENT_STATEMENT_BYTES], PoolV1PaymentStatementFormatError> {
    validate_pool_v1_private_transfer_public_v1(public)?;
    let mut output = [0u8; POOL_V1_PAYMENT_STATEMENT_BYTES];
    encode_common(
        &mut output,
        POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC,
        PoolV1TransitionKind::PrivateTransfer,
        transfer_common(public),
    );
    // Bytes 148..152 remain the canonical zero fee/reserved word.
    debug_assert_eq!(
        output[AMOUNT_OR_RESERVED_OFFSET..FIRST_OUTPUT_OR_DESTINATION_OFFSET],
        POOL_V1_CANONICAL_FEE.to_le_bytes()
    );
    output[FIRST_OUTPUT_OR_DESTINATION_OFFSET..SECOND_OUTPUT_OFFSET]
        .copy_from_slice(&digest_reference(&public.recipient_commitment));
    output[SECOND_OUTPUT_OFFSET..]
        .copy_from_slice(&digest_reference(&public.change_commitment));
    Ok(output)
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
        .copy_from_slice(&digest_reference(&public.change_commitment));
    Ok(output)
}


fn digest_reference(digest: &Digest) -> [u8; 32] {
    let b0 = digest[0].0.to_le_bytes();
    let b1 = digest[1].0.to_le_bytes();
    let b2 = digest[2].0.to_le_bytes();
    let b3 = digest[3].0.to_le_bytes();
    let b4 = digest[4].0.to_le_bytes();
    let b5 = digest[5].0.to_le_bytes();
    let b6 = digest[6].0.to_le_bytes();
    let b7 = digest[7].0.to_le_bytes();
    [
        b0[0], b0[1], b0[2], b0[3],
        b1[0], b1[1], b1[2], b1[3],
        b2[0], b2[1], b2[2], b2[3],
        b3[0], b3[1], b3[2], b3[3],
        b4[0], b4[1], b4[2], b4[3],
        b5[0], b5[1], b5[2], b5[3],
        b6[0], b6[1], b6[2], b6[3],
        b7[0], b7[1], b7[2], b7[3],
    ]
}
