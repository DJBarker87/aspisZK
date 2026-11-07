use solana_program::program_error::ProgramError;
pub fn request_ref(bytes: &[u8]) -> Result<aspis_statement::pool_v1::PoolV1PairForestTerminalRequestV1, ProgramError> {
    match aspis_statement::pool_v1::decode_pool_v1_pair_forest_terminal_request_v1(bytes) {
        Ok(value) => Ok(value),
        Err(_) => Err(ProgramError::InvalidInstructionData),
    }
}
