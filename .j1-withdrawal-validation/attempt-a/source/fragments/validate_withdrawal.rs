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