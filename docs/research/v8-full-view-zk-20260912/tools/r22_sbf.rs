//! Native arithmetic comparison only. No helper proof, no changed protocol.
mod r22_native;
use aspis_core::field::QM31 as K;
use solana_program::{account_info::AccountInfo,entrypoint::ProgramResult,program_error::ProgramError,pubkey::Pubkey};
solana_program::entrypoint!(entry);
#[cfg(target_os="solana")]
#[global_allocator]
static ALLOC:solana_program::entrypoint::BumpAllocator=solana_program::entrypoint::BumpAllocator{start:solana_program::entrypoint::HEAP_START_ADDRESS as usize,len:262144};
fn entry(program:&Pubkey,accounts:&[AccountInfo],instruction:&[u8])->ProgramResult{
    if accounts.len()!=1 || instruction.len()!=1 || instruction[0]>1 || accounts[0].owner!=program || accounts[0].is_writable || accounts[0].executable{return Err(ProgramError::InvalidArgument);}
    let data=accounts[0].try_borrow_data()?;if data.len()!=400{return Err(ProgramError::InvalidInstructionData);}
    let mut x=[K::ZERO;24];for(i,v)in x.iter_mut().enumerate(){*v=K::from_le_bytes(&data[16*i..16*i+16]).ok_or(ProgramError::InvalidInstructionData)?;}
    let expected=K::from_le_bytes(&data[384..400]).ok_or(ProgramError::InvalidInstructionData)?;
    let result=if instruction[0]==0{r22_native::compute(&x)}else{r22_native::compute_scalar(&x)};
    if result!=expected{return Err(ProgramError::Custom(22));}Ok(())
}
