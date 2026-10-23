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

// Same original bytes, slice length, count; all heap/SDK state untouched.
// Bounded native source check (lengths 0..3). Lean shape1_port is unbounded.
#[kani::proof]
#[kani::unwind(5)]
fn S2J_cut1_bound_invocation() {
    let bytes: [u8; 3] = kani::any();
    let len: usize = kani::any();
    kani::assume(len <= 3);
    let count: usize = kani::any();
    let data = &bytes[..len];
    let native = native_cut1(data, count);
    let owned = owned_cut1(data, count);
    assert_eq!(native, owned);
    assert_eq!(data == &[3,10], data == &[3,10][..]);
    assert_eq!(data == &[3,11], data == &[3,11][..]);
    kani::cover!(native.is_ok());
    kani::cover!(native.is_err());
}
