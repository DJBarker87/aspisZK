#![allow(dead_code,unused_mut)]
use solana_program::{account_info::AccountInfo,program_error::ProgramError,entrypoint::ProgramResult,pubkey::Pubkey};
enum Variant {S2}
mod verifier {pub fn checkpoint_size(_:super::Variant)->usize{1768}}
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
fn stage1(program_id: &Pubkey, accounts: &[AccountInfo<'_>], data: &[u8]) -> ProgramResult {
    if !(data == &[3, 10] || data == &[3, 11]) || accounts.len() != 3 {
        return Err(ProgramError::InvalidInstructionData);
    }
    let proof_account = &accounts[0];
    let public_account = &accounts[1];
    let checkpoint_account = &accounts[2];
    require_distinct_accounts(&[proof_account, public_account, checkpoint_account])?;
    require_readonly_buffer(proof_account)?;
    require_readonly_buffer(public_account)?;
    require_verifier_checkpoint(checkpoint_account, program_id, true)?;
    let mut checkpoint_data = checkpoint_account.try_borrow_mut_data()?;
    drop(checkpoint_data);
    Ok(())
}

#[cfg(kani)] mod proofs {
use super::*;
#[kani::proof]
#[kani::unwind(40)]
fn actual_sdk_prefix_guard_order() {
 let program=Pubkey::new_from_array(kani::any());let keys:[Pubkey;3]=core::array::from_fn(|_|Pubkey::new_from_array(kani::any()));
 let owner=Pubkey::new_from_array(kani::any());let readonly0:bool=kani::any();let readonly1:bool=kani::any();
 let signer:bool=kani::any();let writable:bool=kani::any();let executable:bool=kani::any();
 let mut lamports=[0u64;3];let [ref mut l0,ref mut l1,ref mut l2]=lamports;
 let mut proof=[];let mut public=[];let mut cp=[0u8;1768];let cp_len:usize=kani::any();kani::assume(cp_len<=1768);
 let a0=AccountInfo::new(&keys[0],!readonly0,false,l0,&mut proof,&owner,false,0);
 let a1=AccountInfo::new(&keys[1],false,!readonly1,l1,&mut public,&owner,false,0);
 let a2=AccountInfo::new(&keys[2],signer,writable,l2,&mut cp[..cp_len],&owner,executable,0);
 let accounts=[a0,a1,a2];
 let held_shared=if kani::any(){Some(accounts[2].try_borrow_data().unwrap())}else{None};
 let held_exclusive=if held_shared.is_none() && kani::any(){Some(accounts[2].try_borrow_mut_data().unwrap())}else{None};
 let bytes:[u8;3]=kani::any();let data_len:usize=kani::any();kani::assume(data_len<=3);
 let accounts_len:usize=kani::any();kani::assume(accounts_len<=3);
 let data=&bytes[..data_len];
 let actual=stage1(&program,&accounts[..accounts_len],data);
 let expected=if !(data==[3,10]||data==[3,11]) || accounts_len!=3 {0}
  else if keys[0]==keys[1]||keys[0]==keys[2]||keys[1]==keys[2]{1}
  else if !readonly0||!readonly1||owner!=program||signer||executable||!writable{2}
  else if held_exclusive.is_some(){3}
  else if cp_len!=1768{2}
  else if held_shared.is_some(){3}
  else{4};
 assert!(matches!((&actual,expected),(Err(ProgramError::InvalidInstructionData),0)|(Err(ProgramError::InvalidArgument),1)|(Err(ProgramError::InvalidAccountData),2)|(Err(ProgramError::AccountBorrowFailed),3)|(Ok(()),4)));
 drop(held_shared);drop(held_exclusive);assert!(accounts[2].try_borrow_mut_data().is_ok());
 kani::cover!(expected==0,"instruction reject");kani::cover!(expected==1,"duplicate reject");kani::cover!(expected==2,"metadata reject");kani::cover!(expected==3,"borrow reject");kani::cover!(expected==4,"prefix succeeds");
}
}
