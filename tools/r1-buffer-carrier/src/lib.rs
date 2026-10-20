//! Devnet raw-buffer transport. The account key must sign every bounded write.
//! No verifier logic, account closure, realloc or authority transfer.
#![allow(unexpected_cfgs)]
use solana_program::{account_info::AccountInfo,entrypoint::ProgramResult,program_error::ProgramError,pubkey::Pubkey};
solana_program::entrypoint!(process);
pub fn process(id:&Pubkey,accounts:&[AccountInfo],data:&[u8])->ProgramResult{
 let [target]=accounts else{return Err(ProgramError::InvalidArgument)};
 if target.owner!=id||!target.is_signer||!target.is_writable||target.executable{return Err(ProgramError::InvalidAccountData)}
 let offset=u32::from_le_bytes(data.get(..4).ok_or(ProgramError::InvalidInstructionData)?.try_into().unwrap()) as usize;
 let body=&data[4..];let end=offset.checked_add(body.len()).ok_or(ProgramError::InvalidInstructionData)?;
 let mut bytes=target.try_borrow_mut_data()?;
 bytes.get_mut(offset..end).ok_or(ProgramError::AccountDataTooSmall)?.copy_from_slice(body);Ok(())
}
