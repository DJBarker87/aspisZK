#![allow(dead_code,unexpected_cfgs)]
use solana_program::{account_info::AccountInfo,pubkey::Pubkey,program_error::ProgramError,msg};
#[cfg_attr(kani,kani::requires(checkpoint_data.len()==1768 && checkpoint.len()==1768))]
#[cfg_attr(kani,kani::requires(observed<1768))]
#[cfg_attr(kani,kani::requires(destination==checkpoint_data.as_mut_ptr().cast::<[u8;1768]>()))]
#[cfg_attr(kani,kani::requires(source==checkpoint.as_mut_ptr().cast::<[u8;1768]>()))]
#[cfg_attr(kani,kani::modifies(destination,source))]
#[cfg_attr(kani,kani::ensures(move |result:&Result<(),ProgramError>| result.is_ok() && checkpoint_data[observed]==old(checkpoint[observed])))]
fn native_finish(checkpoint_data:&mut std::cell::RefMut<'_,&mut [u8]>,mut checkpoint:Vec<u8>,observed:usize,destination:*mut [u8;1768],source:*mut [u8;1768])->Result<(),ProgramError> {
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
 fn exact_finish_fixed_frame() {
  let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());
  let flags:[bool;3]=kani::any();let rent:u64=kani::any();let mut amount:u64=kani::any();
  let mut bytes:[u8;1768]=kani::any();let reply:[u8;1768]=kani::any();let mut checkpoint=reply.to_vec();
  let observed:usize=kani::any();kani::assume(observed<1768);
  let account=AccountInfo::new(&key,flags[0],flags[1],&mut amount,&mut bytes,&owner,flags[2],rent);
  let mut guard=account.try_borrow_mut_data().unwrap();
  let destination=guard.as_mut_ptr().cast::<[u8;1768]>();let source=checkpoint.as_mut_ptr().cast::<[u8;1768]>();
  let result=native_finish(&mut guard,checkpoint,observed,destination,source);
  kani::cover!(result.is_ok()&&observed==0,"fixed-size native whole copy first byte");
  kani::cover!(result.is_ok()&&observed==1767,"fixed-size native whole copy last byte");
 }
}
