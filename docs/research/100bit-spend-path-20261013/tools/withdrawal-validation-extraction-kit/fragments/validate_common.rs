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