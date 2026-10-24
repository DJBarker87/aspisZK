#![allow(dead_code)]
pub mod indexed {
use solana_program_error::{ProgramError, ProgramResult};
fn require_zero(bytes: &[u8]) -> ProgramResult {
    let mut index = 0;
    while index < bytes.len() {
        if bytes[index] != 0 { return Err(ProgramError::AccountAlreadyInitialized); }
        index += 1;
    }
    Ok(())
}
pub fn entry(bytes: &[u8]) -> ProgramResult { require_zero(bytes) }
}
pub mod tail {
use solana_program_error::{ProgramError, ProgramResult};
fn require_zero(mut remaining: &[u8]) -> ProgramResult {
    while !remaining.is_empty() {
        if remaining[0] != 0 { return Err(ProgramError::AccountAlreadyInitialized); }
        remaining = &remaining[1..];
    }
    Ok(())
}
pub fn entry(bytes: &[u8]) -> ProgramResult { require_zero(bytes) }
}
