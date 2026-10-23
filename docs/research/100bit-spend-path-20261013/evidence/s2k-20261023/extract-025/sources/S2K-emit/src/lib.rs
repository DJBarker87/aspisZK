#![allow(non_snake_case)]
use aspis_statement::pool_v1::*;
use solana_program_error::ProgramError;

pub fn S2K_probe_prefix(statement: &PoolV1PairForestTerminalStatementV1) -> Result<[u8;792],ProgramError> {
    let result = PoolV1PairForestTerminalResultV1 {
        transition_kind: statement.transition_kind(),
        master_account: statement.common().master_account,
        selected_lane_account: statement.common().selected_lane_account,
        output_lane: statement.common().output_lane,
        nullifier: *statement.nullifier(),
        verified_afterstate: statement.common().lane_transition.candidate_afterstate,
    };
    validate_pool_v1_pair_forest_terminal_result_against_statement_v1(statement, &result)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    let encoded = encode_pool_v1_pair_forest_terminal_result_v1(&result)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    if encoded.len() != POOL_V1_PAIR_FOREST_TERMINAL_RESULT_BYTES
        || encoded[..4] != POOL_V1_PAIR_FOREST_TERMINAL_RESULT_MAGIC
    {
        return Err(ProgramError::InvalidInstructionData);
    }
    Ok(encoded)
}

pub fn S2K_verifier_prefix(statement: &PoolV1PairForestTerminalStatementV1) -> Result<[u8;792],ProgramError> {
    let result = PoolV1PairForestTerminalResultV1 {
        transition_kind: statement.transition_kind(),
        master_account: statement.common().master_account,
        selected_lane_account: statement.common().selected_lane_account,
        output_lane: statement.common().output_lane,
        nullifier: *statement.nullifier(),
        verified_afterstate: statement.common().lane_transition.candidate_afterstate,
    };
    validate_pool_v1_pair_forest_terminal_result_against_statement_v1(statement, &result)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    let encoded = encode_pool_v1_pair_forest_terminal_result_v1(&result)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    Ok(encoded)
}
