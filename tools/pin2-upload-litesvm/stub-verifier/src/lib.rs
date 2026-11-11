//! TEST FIXTURE ONLY, never deployed. Stands in for the PIN2 verifier in the
//! LiteSVM upload/close test so the client's close transaction can run
//! end to end before W1's verifier close instruction exists.
//!
//! * `[3, 10]`, accounts `[proof, statement, checkpoint (writable, owned)]`:
//!   writes a non-zero pattern into the checkpoint (stage-1 stand-in; no proof check).
//! * `[7, seed_len, seed]`, accounts `[checkpoint (writable, owned), base (signer)]`:
//!   mirrors W1's close_checkpoint (fix/pin2-verifier-20261110 271869c946d):
//!   `create_with_seed(base, seed, program_id)` must equal the checkpoint;
//!   zero all data and move all lamports to base (no shrink, no reassign).
#![allow(unexpected_cfgs)]
use solana_program::{account_info::AccountInfo, entrypoint::ProgramResult, program_error::ProgramError, pubkey::Pubkey};
solana_program::entrypoint!(process);
pub fn process(id: &Pubkey, accounts: &[AccountInfo], data: &[u8]) -> ProgramResult {
    if data == [3, 10] {
        let [_, _, cp] = accounts else { return Err(ProgramError::NotEnoughAccountKeys) };
        if cp.owner != id || !cp.is_writable { return Err(ProgramError::InvalidAccountData) }
        cp.try_borrow_mut_data()?.fill(0x5a);
        return Ok(());
    }
    let [7, len, rest @ ..] = data else { return Err(ProgramError::InvalidInstructionData) };
    let len = *len as usize;
    if len == 0 || len > 32 || rest.len() != len { return Err(ProgramError::InvalidInstructionData) }
    let seed = core::str::from_utf8(rest).map_err(|_| ProgramError::InvalidInstructionData)?;
    let [cp, base] = accounts else { return Err(ProgramError::NotEnoughAccountKeys) };
    if cp.key == base.key || !base.is_signer || !cp.is_writable || cp.executable || cp.owner != id {
        return Err(ProgramError::InvalidAccountData);
    }
    if Pubkey::create_with_seed(base.key, seed, id).map_err(|_| ProgramError::InvalidSeeds)? != *cp.key {
        return Err(ProgramError::InvalidSeeds);
    }
    let total = base.lamports().checked_add(cp.lamports()).ok_or(ProgramError::ArithmeticOverflow)?;
    cp.try_borrow_mut_data()?.fill(0);
    **cp.try_borrow_mut_lamports()? = 0;
    **base.try_borrow_mut_lamports()? = total;
    Ok(())
}
