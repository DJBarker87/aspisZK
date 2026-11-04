use aspis_statement::pool_v1::{encode_pool_v1_pair_forest_terminal_result_v1,POOL_V1_PAIR_FOREST_TERMINAL_RESULT_BYTES};
use aspis_pool::error::PoolV1ProgramError;
use solana_program::program_error::ProgramError;
#[inline(never)]
fn terminal_result_bytes_box_v1(
    result: &aspis_statement::pool_v1::PoolV1PairForestTerminalResultV1,
) -> Result<Box<[u8; POOL_V1_PAIR_FOREST_TERMINAL_RESULT_BYTES]>, ProgramError> {
    Ok(Box::new(
        encode_pool_v1_pair_forest_terminal_result_v1(result)
            .map_err(|_| PoolV1ProgramError::InvalidVerifierReturnData)?,
    ))
}

pub fn terminal_ref(result:&aspis_statement::pool_v1::PoolV1PairForestTerminalResultV1)->Result<Box<[u8;POOL_V1_PAIR_FOREST_TERMINAL_RESULT_BYTES]>,ProgramError>{terminal_result_bytes_box_v1(result)}
