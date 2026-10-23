#![allow(dead_code,unexpected_cfgs)]
use solana_program::{account_info::AccountInfo,pubkey::Pubkey,program_error::ProgramError,msg};
#[cfg_attr(kani,kani::requires(checkpoint_data.len()==1768))]
#[cfg_attr(kani,kani::requires(observed<1768))]
#[cfg_attr(kani,kani::modifies(&mut checkpoint_data[..],&mut checkpoint[..]))]
#[cfg_attr(kani,kani::ensures(move |result:&Result<(),ProgramError>| match result {
 Ok(()) => old(checkpoint.len())==1768 && Some(checkpoint_data[observed])==old(checkpoint.get(observed).copied()),
 Err(ProgramError::InvalidAccountData) => old(checkpoint.len())!=1768 && checkpoint_data[observed]==old(checkpoint_data[observed]),
 _ => false,
}))]
fn native_finish(checkpoint_data:&mut std::cell::RefMut<'_,&mut [u8]>,mut checkpoint:Vec<u8>,observed:usize)->Result<(),ProgramError> {
    if checkpoint.len() != checkpoint_data.len() {
        return Err(ProgramError::InvalidAccountData);
    }
    checkpoint_data.copy_from_slice(&checkpoint);
    #[cfg(feature="cu-profiling")]
    {
    msg!("r1:pool-adapter-stage1-checkpoint-written");
    solana_program::log::sol_log_compute_units();
    }
    Ok(())
}
#[cfg(kani)] mod proofs {
 use super::*;
 #[kani::proof_for_contract(native_finish)] #[kani::unwind(1772)]
 fn finish_byte_and_frame() {
  let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());
  let flags:[bool;3]=kani::any();let rent:u64=kani::any();let mut amount:u64=kani::any();
  let mut bytes:[u8;1768]=kani::any();let reply:[u8;1769]=kani::any();
  let length:usize=kani::any();kani::assume(length<=1769);
  let observed:usize=kani::any();kani::assume(observed<1768);
  let account=AccountInfo::new(&key,flags[0],flags[1],&mut amount,&mut bytes,&owner,flags[2],rent);
  let mut guard=account.try_borrow_mut_data().unwrap();
  let result=native_finish(&mut guard,reply[..length].to_vec(),observed);
  kani::cover!(result.is_ok(),"source copy postcondition");
  kani::cover!(matches!(result,Err(ProgramError::InvalidAccountData)),"source length rejection postcondition");
 }
}
