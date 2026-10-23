fn validate_result(
    result: &PoolV1PairForestTerminalResultV1,
) -> Result<(), PoolV1PairForestTerminalFormatErrorV1> {
    if result.master_account == [0u8; 32] || result.selected_lane_account == [0u8; 32] {
        return Err(PoolV1PairForestTerminalFormatErrorV1::NonZeroBinding);
    }
    let expected = pool_v1_pair_forest_output_lane_v1(&result.nullifier)
        .map_err(|error| PoolV1PairForestTerminalFormatErrorV1::Account(error))?;
    if result.output_lane != expected {
        return Err(PoolV1PairForestTerminalFormatErrorV1::OutputLaneMismatch);
    }
    encode_pool_v1_pair_verified_afterstate_v1(&result.verified_afterstate)
        .map_err(|error| PoolV1PairForestTerminalFormatErrorV1::Afterstate(error))?;
    Ok(())
}

