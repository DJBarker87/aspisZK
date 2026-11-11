//! Aspis upload program: header-free raw buffers for proof and statement bytes.
//!
//! The verifier reads a proof or statement buffer as raw bytes from offset 0,
//! so an upload account carries no header. Its only identity is its address:
//! the client creates it with the system program's `CreateAccountWithSeed`
//! (`base`, `seed`, owner = this program), and every instruction re-derives
//! `Pubkey::create_with_seed(base, seed, program_id)` and requires the `base`
//! signature. Whoever holds `base` controls the account; nobody else can write
//! or close it.
//!
//! Instructions (all integers little-endian):
//!
//! * WRITE `[0x01, seed_len u8, seed[seed_len], offset u32, bytes..]`,
//!   accounts `[target (writable), base (signer)]`. Copies `bytes` to
//!   `target.data[offset..offset + bytes.len()]`; `bytes` must be non-empty
//!   and the range must lie inside the account.
//! * CLOSE `[0x02, seed_len u8, seed[seed_len]]`, accounts
//!   `[target (writable), base (signer, writable)]`. Zeroes every data byte,
//!   shrinks the data to zero length, assigns the account to the system
//!   program and moves every lamport to `base`, all in this one instruction.
//!   After it, the account is a zero-lamport system account that the runtime
//!   deletes at the end of the transaction; a later WRITE or CLOSE in the same
//!   transaction fails the owner check.
//!
//! `seed` must be 1..=32 bytes of valid UTF-8 (the system program only accepts
//! UTF-8 `String` seeds, so no other seed can name an account created through
//! it; `create_with_seed` itself rejects more than 32 bytes). Any other tag,
//! length, account count or account flag is rejected. There is no CPI, no
//! sysvar read and no allocation.

#![no_std]
#![allow(unexpected_cfgs)]

#[cfg(test)]
extern crate std;

#[cfg(not(feature = "no-entrypoint"))]
extern crate alloc;
#[cfg(not(feature = "no-entrypoint"))]
#[allow(unused_imports)]
use alloc::format;

use solana_program::{
    account_info::AccountInfo,
    entrypoint::ProgramResult,
    program_error::ProgramError,
    pubkey::{Pubkey, MAX_SEED_LEN},
};
use solana_sdk_ids::system_program;

/// WRITE instruction tag.
pub const WRITE_TAG: u8 = 0x01;
/// CLOSE instruction tag.
pub const CLOSE_TAG: u8 = 0x02;

#[cfg(not(feature = "no-entrypoint"))]
solana_program::entrypoint!(process_instruction);

/// A decoded instruction. `seed` is checked UTF-8 of length 1..=32.
#[derive(Debug, PartialEq, Eq)]
pub enum UploadInstruction<'a> {
    Write {
        seed: &'a str,
        offset: u32,
        bytes: &'a [u8],
    },
    Close {
        seed: &'a str,
    },
}

/// Split `[seed_len, seed.., rest..]` into a checked seed and the rest.
fn split_seed(data: &[u8]) -> Result<(&str, &[u8]), ProgramError> {
    let (&len, rest) = data
        .split_first()
        .ok_or(ProgramError::InvalidInstructionData)?;
    let len = len as usize;
    if len == 0 || len > MAX_SEED_LEN || rest.len() < len {
        return Err(ProgramError::InvalidInstructionData);
    }
    let (seed, rest) = rest.split_at(len);
    let seed = core::str::from_utf8(seed).map_err(|_| ProgramError::InvalidInstructionData)?;
    Ok((seed, rest))
}

/// Decode instruction data. Rejects every byte string that is not exactly one
/// of the two formats above.
pub fn decode(data: &[u8]) -> Result<UploadInstruction<'_>, ProgramError> {
    let (&tag, rest) = data
        .split_first()
        .ok_or(ProgramError::InvalidInstructionData)?;
    match tag {
        WRITE_TAG => {
            let (seed, rest) = split_seed(rest)?;
            if rest.len() < 4 {
                return Err(ProgramError::InvalidInstructionData);
            }
            let (offset, bytes) = rest.split_at(4);
            if bytes.is_empty() {
                return Err(ProgramError::InvalidInstructionData);
            }
            let offset = u32::from_le_bytes([offset[0], offset[1], offset[2], offset[3]]);
            Ok(UploadInstruction::Write {
                seed,
                offset,
                bytes,
            })
        }
        CLOSE_TAG => {
            let (seed, rest) = split_seed(rest)?;
            if !rest.is_empty() {
                return Err(ProgramError::InvalidInstructionData);
            }
            Ok(UploadInstruction::Close { seed })
        }
        _ => Err(ProgramError::InvalidInstructionData),
    }
}

/// Common account checks: exactly `[target, base]`, distinct, base signed,
/// target writable, not executable, owned by this program, and at the address
/// derived from `(base, seed, program_id)`.
fn authenticate<'a, 'b>(
    program_id: &Pubkey,
    accounts: &'b [AccountInfo<'a>],
    seed: &str,
    base_writable: bool,
) -> Result<(&'b AccountInfo<'a>, &'b AccountInfo<'a>), ProgramError> {
    let [target, base] = accounts else {
        return Err(ProgramError::NotEnoughAccountKeys);
    };
    if target.key == base.key {
        return Err(ProgramError::InvalidArgument);
    }
    if !base.is_signer {
        return Err(ProgramError::MissingRequiredSignature);
    }
    if base_writable && !base.is_writable {
        return Err(ProgramError::InvalidAccountData);
    }
    if !target.is_writable || target.executable {
        return Err(ProgramError::InvalidAccountData);
    }
    if target.owner != program_id {
        return Err(ProgramError::IncorrectProgramId);
    }
    let expected =
        Pubkey::create_with_seed(base.key, seed, program_id).map_err(|_| ProgramError::InvalidSeeds)?;
    if target.key != &expected {
        return Err(ProgramError::InvalidSeeds);
    }
    Ok((target, base))
}

fn write(target: &AccountInfo<'_>, offset: u32, bytes: &[u8]) -> ProgramResult {
    let mut data = target.try_borrow_mut_data()?;
    let start = offset as usize;
    let end = start
        .checked_add(bytes.len())
        .ok_or(ProgramError::AccountDataTooSmall)?;
    data.get_mut(start..end)
        .ok_or(ProgramError::AccountDataTooSmall)?
        .copy_from_slice(bytes);
    Ok(())
}

fn close(target: &AccountInfo<'_>, base: &AccountInfo<'_>) -> ProgramResult {
    // Check the only fallible arithmetic before any mutation.
    let refunded = base
        .lamports()
        .checked_add(target.lamports())
        .ok_or(ProgramError::ArithmeticOverflow)?;
    {
        let mut data = target.try_borrow_mut_data()?;
        data.fill(0);
    }
    // Shrink to zero (allowed for the owner) and hand the account back to the
    // system program while its data is empty, so no later instruction in this
    // transaction can treat it as an upload account or read stale bytes.
    target.resize(0)?;
    target.assign(&system_program::ID);
    **target.try_borrow_mut_lamports()? = 0;
    **base.try_borrow_mut_lamports()? = refunded;
    Ok(())
}

/// Program entrypoint.
pub fn process_instruction(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'_>],
    data: &[u8],
) -> ProgramResult {
    match decode(data)? {
        UploadInstruction::Write {
            seed,
            offset,
            bytes,
        } => {
            let (target, _) = authenticate(program_id, accounts, seed, false)?;
            write(target, offset, bytes)
        }
        UploadInstruction::Close { seed } => {
            let (target, base) = authenticate(program_id, accounts, seed, true)?;
            close(target, base)
        }
    }
}

#[cfg(test)]
mod tests;
