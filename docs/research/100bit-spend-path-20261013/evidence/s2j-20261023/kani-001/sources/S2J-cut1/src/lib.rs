#![cfg(kani)]
#![allow(dead_code)]
use solana_program_error::ProgramError;
type ProgramResult = Result<(), ProgramError>;

// Native stage1:947-949, with ONLY accounts.len() projected to slice metadata.
// No native whole-function call, account indexing, SDK borrow or child is reached.
fn native_cut1(data: &[u8], accounts_len: usize) -> ProgramResult {
    if !(data == &[3, 10] || data == &[3, 11]) || accounts_len != 3 {
        return Err(ProgramError::InvalidInstructionData);
    }
    Ok(())
}
// S2E owned shape1: verbatim, apart from function name.
fn owned_cut1(data: &[u8], accounts: usize) -> ProgramResult {
 if !(data == &[3,10] || data == &[3,11]) || accounts != 3 {
  Err(ProgramError::InvalidInstructionData)
 } else { Ok(()) }
}

// Smallest relation diagnostic. Full heap/SDK fields can be identical and
// untouched; the inherited CutRelated contains no native invocation observation.
// This is deliberately NOT an admitted same-external-input execution pair.
#[kani::proof]
fn S2J_cut1_unbound_invocation() {
    assert_eq!(native_cut1(&[], 3), owned_cut1(&[3,10], 3));
}
