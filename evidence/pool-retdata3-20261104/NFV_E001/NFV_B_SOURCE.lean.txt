use aspis_statement::pool_v1::*;
pub fn encode_ref(
    request: &PoolV1PairForestTerminalRequestV1,
) -> Result<[u8; POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES], PoolV1PairForestTerminalFormatErrorV1>
{
    if request.verifier_profile == [0u8; 32]
        || request.verifier_release == [0u8; 32]
        || request.pool_program == [0u8; 32]
    {
        return Err(PoolV1PairForestTerminalFormatErrorV1::NonZeroBinding);
    }
    let payment = match request.public {
        PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public) => {
            encode_pool_v1_private_transfer_public_v1(&public)
        }
        PoolV1PairForestTerminalPaymentV1::Withdrawal(public) => {
            encode_pool_v1_withdrawal_public_v1(&public)
        }
    }
    .map_err(|e| PoolV1PairForestTerminalFormatErrorV1::Payment(e))?;
    let mut output = [0u8; POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES];
    output[..4].copy_from_slice(&POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC);
    output[4] = POOL_V1_PAIR_FOREST_TERMINAL_VERSION;
    output[5] = match request.public { PoolV1PairForestTerminalPaymentV1::PrivateTransfer(_) => 1, PoolV1PairForestTerminalPaymentV1::Withdrawal(_) => 2 };
    output[6] = POOL_V1_DIGEST_ENCODING_VERSION;
    output[8..40]
        .copy_from_slice(&request.verifier_profile);
    output[40..72]
        .copy_from_slice(&request.verifier_release);
    output[72..104]
        .copy_from_slice(&request.pool_program);
    output[104..].copy_from_slice(&payment);
    Ok(output)
}
