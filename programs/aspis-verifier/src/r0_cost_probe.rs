//! Unproved COST PROBE; B instrumentation, no checks removed.
//! Never-production R0 diagnostic, tag 241. Both accounts are read-only:
//! [sealed ASPU proof, canonical ASF8 public context]. No checks are disabled.
use aspis_statement::{
    pool_v1::{
        decode_pool_v1_pair_forest_terminal_statement_v1,
        pair_forest_semantic_terminal::r0::Public, PoolV1PairForestTerminalStatementV1,
    },
    r0_probe::{r0_verify, Phase},
};
use solana_program::{
    account_info::AccountInfo, entrypoint::ProgramResult, hash::hashv, log::sol_log_compute_units,
    msg, program_error::ProgramError, pubkey::Pubkey,
};

/// Matched by request_heap_frame(256 KiB) in the local measurement harness.
#[cfg(target_os = "solana")]
#[global_allocator]
static ALLOCATOR: solana_program::entrypoint::BumpAllocator =
    solana_program::entrypoint::BumpAllocator {
        start: solana_program::entrypoint::HEAP_START_ADDRESS as usize,
        len: 256 * 1024,
    };

pub const R0_CU_PROBE_TAG: u8 = 241;
#[cfg(not(feature = "no-entrypoint"))]
solana_program::entrypoint!(process_r0_cu_probe_instruction);

#[inline(never)]
fn trace(phase: Phase) {
    match phase {
        Phase::Parsed => msg!("r0:parsed"),
        Phase::Semantic => msg!("r0:semantic"),
        Phase::ChordClaims => msg!("r0:chord-claims"),
        Phase::V2 => msg!("r0:v2"),
        Phase::Merkle(i) => msg!("r0:merkle:{}", i),
        Phase::V1(i) => msg!("r0:v1:{}", i),
    }
    sol_log_compute_units();
}
pub fn process_r0_cu_probe_instruction(
    program_id: &Pubkey,
    accounts: &[AccountInfo],
    data: &[u8],
) -> ProgramResult {
    if data != [R0_CU_PROBE_TAG] {
        return Err(ProgramError::InvalidInstructionData);
    }
    if accounts.len() != 2 {
        return Err(ProgramError::NotEnoughAccountKeys);
    }
    for account in accounts {
        if account.owner != program_id || account.is_writable || account.executable {
            return Err(ProgramError::InvalidAccountData);
        }
    }
    let bytes = accounts[0].try_borrow_data()?;
    if !crate::lifecycle::proof_account_finalized(&bytes) {
        return Err(ProgramError::InvalidAccountData);
    }
    let (start, end) = crate::lifecycle::uploaded_proof_bounds(&bytes)?;
    if end != bytes.len() {
        return Err(ProgramError::InvalidAccountData);
    }
    let public_bytes = accounts[1].try_borrow_data()?;
    let statement = decode_pool_v1_pair_forest_terminal_statement_v1(&public_bytes)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    let public = match &statement {
        PoolV1PairForestTerminalStatementV1::PrivateTransfer { common, public } => {
            Public::Transfer(public, &common.lane_transition)
        }
        PoolV1PairForestTerminalStatementV1::Withdrawal { common, public } => {
            Public::Withdrawal(public, &common.lane_transition)
        }
    };
    msg!("r0:begin");
    sol_log_compute_units();
    r0_verify(
        public,
        &bytes[start..end],
        |p| hashv(p).to_bytes(),
        Some(trace),
    )
    .map_err(|e| {
        msg!("r0:error:{:?}", e);
        ProgramError::InvalidInstructionData
    })?;
    #[cfg(target_os = "solana")]
    unsafe {
        let cursor = *(solana_program::entrypoint::HEAP_START_ADDRESS as *const usize);
        // Non-allocating logging preserves the final bump high-water mark.
        msg!("r0:heap-high-water");
        solana_program::log::sol_log_64(
            (solana_program::entrypoint::HEAP_START_ADDRESS as usize + 256 * 1024 - cursor
                + core::mem::size_of::<usize>()) as u64,
            0,
            0,
            0,
            0,
        );
    }
    msg!("r0:done");
    sol_log_compute_units();
    Ok(())
}
