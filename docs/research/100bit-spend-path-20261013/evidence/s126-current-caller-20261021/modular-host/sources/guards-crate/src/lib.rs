#![allow(dead_code)]
use solana_program::{account_info::AccountInfo,program_error::ProgramError,entrypoint::ProgramResult,pubkey::Pubkey};
#[derive(Clone,Copy)] enum Variant {S2}
mod verifier {
 use super::*;
 // Exact frozen CHECKPOINT_FIXED and final_len(S2) arithmetic, not a free size.
 pub fn checkpoint_size(_:Variant)->usize {16+32*3+64+32*4+16+88+160+64+32*2+16+32+16*(1024>>(2*2))}
}
fn readonly_buffer_meta_ok(
    is_signer: bool,
    is_writable: bool,
    executable: bool,
) -> ProgramResult {
    if is_signer || is_writable || executable {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(())
}
fn require_readonly_buffer(account: &AccountInfo<'_>) -> ProgramResult {
    readonly_buffer_meta_ok(account.is_signer, account.is_writable, account.executable)
}
fn require_verifier_checkpoint(
    account: &AccountInfo<'_>,
    program_id: &Pubkey,
    writable: bool,
) -> ProgramResult {
    if account.owner != program_id || account.is_signer || account.executable
        || account.is_writable != writable
        || account.try_data_len()? != verifier::checkpoint_size(Variant::S2)
    {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(())
}
fn require_distinct_accounts<const N: usize>(accounts: &[&AccountInfo<'_>; N]) -> ProgramResult {
    for (index, account) in accounts.iter().enumerate() {
        if accounts[..index]
            .iter()
            .any(|previous| previous.key == account.key)
        {
            return Err(ProgramError::InvalidArgument);
        }
    }
    Ok(())
}
#[cfg(kani)] mod proofs {
use super::*;
#[kani::proof]
fn metadata_guards_actual_sdk() {
 let program=Pubkey::new_from_array(kani::any());let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());
 let signer:bool=kani::any();let writable:bool=kani::any();let executable:bool=kani::any();let required_write:bool=kani::any();
 let mut lamports=kani::any();let mut bytes=[0u8;1768];let length:usize=kani::any();kani::assume(length<=bytes.len());
 let account=AccountInfo::new(&key,signer,writable,&mut lamports,&mut bytes[..length],&owner,executable,kani::any());
 assert_eq!(require_readonly_buffer(&account),if signer||writable||executable {Err(ProgramError::InvalidAccountData)}else{Ok(())});
 let held=if kani::any(){Some(account.try_borrow_mut_data().unwrap())}else{None};
 let expected=if owner!=program||signer||executable||writable!=required_write {Err(ProgramError::InvalidAccountData)}
  else if held.is_some(){Err(ProgramError::AccountBorrowFailed)}
  else if length!=1768 {Err(ProgramError::InvalidAccountData)}else{Ok(())};
 assert_eq!(require_verifier_checkpoint(&account,&program,required_write),expected);
 drop(held);assert!(account.try_borrow_mut_data().is_ok());
}
#[kani::proof]
#[kani::unwind(5)]
fn distinct_actual_sdk() {
 let keys:[Pubkey;3]=core::array::from_fn(|_|Pubkey::new_from_array(kani::any()));let owner=Pubkey::new_from_array(kani::any());
 let mut lamports=[0u64;3];let [ref mut l0,ref mut l1,ref mut l2]=lamports;
 let mut b0=[];let mut b1=[];let mut b2=[];
 let a0=AccountInfo::new(&keys[0],kani::any(),kani::any(),l0,&mut b0,&owner,kani::any(),kani::any());
 let a1=AccountInfo::new(&keys[1],kani::any(),kani::any(),l1,&mut b1,&owner,kani::any(),kani::any());
 let a2=AccountInfo::new(&keys[2],kani::any(),kani::any(),l2,&mut b2,&owner,kani::any(),kani::any());
 assert_eq!(require_distinct_accounts(&[&a0,&a1,&a2]),if keys[0]==keys[1]||keys[0]==keys[2]||keys[1]==keys[2]{Err(ProgramError::InvalidArgument)}else{Ok(())});
 assert_eq!(require_distinct_accounts(&[&a0,&a0,&a2]),Err(ProgramError::InvalidArgument));
}
}
