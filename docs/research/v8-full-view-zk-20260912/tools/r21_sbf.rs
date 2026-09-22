//! Standalone ordinary+image arithmetic pilot, NOT an Aspis verifier.
mod r21_gkr;
mod r21_circuit;
#[cfg(r21_native_control)] mod r21_native;
use aspis_core::field::QM31 as K;
use solana_program::{account_info::AccountInfo,entrypoint::ProgramResult,program_error::ProgramError,pubkey::Pubkey};
solana_program::entrypoint!(entry);
#[cfg(target_os="solana")]
#[global_allocator]
static ALLOC:solana_program::entrypoint::BumpAllocator=solana_program::entrypoint::BumpAllocator{
    start:solana_program::entrypoint::HEAP_START_ADDRESS as usize,len:262144,
};
fn entry(program:&Pubkey,accounts:&[AccountInfo],instruction:&[u8])->ProgramResult{
    if accounts.len()!=1 || !instruction.is_empty() || accounts[0].owner!=program || accounts[0].is_writable || accounts[0].executable{return Err(ProgramError::InvalidArgument);}
    let data=accounts[0].try_borrow_data()?;
    if data.len()!=432+16*r21_gkr::proof_fields(&r21_circuit::CIRCUIT){return Err(ProgramError::InvalidInstructionData);}
    let mut input=[K::ZERO;24];
    for(i,v)in input.iter_mut().enumerate(){*v=K::from_le_bytes(&data[16*i..16*i+16]).ok_or(ProgramError::InvalidInstructionData)?;}
    let output=K::from_le_bytes(&data[384..400]).ok_or(ProgramError::InvalidInstructionData)?;
    let context:&[u8;32]=data[400..432].try_into().unwrap();
    #[cfg(r21_native_control)] {
        let _=context;
        if r21_native::compute(&input)!=output{return Err(ProgramError::Custom(21));}
    }
    #[cfg(not(r21_native_control))]
    r21_gkr::verify(&r21_circuit::CIRCUIT,context,&input,output,&data[432..]).map_err(|_|ProgramError::Custom(21))?;
    Ok(())
}
