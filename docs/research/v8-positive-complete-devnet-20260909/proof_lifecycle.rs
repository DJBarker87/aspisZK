//! Research entrypoint adapter for the existing authenticated ASPU lifecycle.
//! The handlers, authority checks, sealing and refund rules are unchanged.
use solana_program::{account_info::AccountInfo, entrypoint::ProgramResult,
    program_error::ProgramError, pubkey::Pubkey};

pub fn process(id: &Pubkey, accounts: &[AccountInfo], data: &[u8]) -> ProgramResult {
    let bad = ProgramError::InvalidInstructionData;
    match data.first().copied() {
        Some(0) if data.len() == 5 => {
            crate::lifecycle::init_proof(id, accounts, u32::from_le_bytes(data[1..5].try_into().unwrap()))
        }
        Some(1) if data.len() >= 9 => {
            let offset = u32::from_le_bytes(data[1..5].try_into().unwrap());
            let len = u32::from_le_bytes(data[5..9].try_into().unwrap()) as usize;
            if data.len() - 9 != len { return Err(bad); }
            crate::lifecycle::upload_chunk(id, accounts, offset, &data[9..])
        }
        Some(62) if data.len() == 1 => crate::lifecycle::finalize_proof(id, accounts),
        Some(64) if data.len() == 1 => crate::lifecycle::close_proof(id, accounts),
        _ => Err(bad),
    }
}
