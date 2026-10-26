use solana_program::{account_info::AccountInfo,pubkey::Pubkey,program_error::ProgramError,entrypoint::ProgramResult,system_program};
#[path="../PoolM_slice/error.rs"] mod error;
use error::PoolV1ProgramError;
#[path="../PoolM_owned/PoolM_lib.rs"] mod reference;
fn require_prepared_plan_account_v1(
    account: &AccountInfo<'_>,
    program_id: &Pubkey,
    exact_data_len: usize,
) -> ProgramResult {
    if account.owner != program_id
        || account.executable
        || account.is_signer
        || !account.is_writable
        || account.data_len() != exact_data_len
    {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(())
}
fn close_program_account_v1(
    account: &AccountInfo<'_>,
    refund_authority: &AccountInfo<'_>,
    expected_owner: &Pubkey,
    expected_data_len: usize,
) -> ProgramResult {
    if account.owner != expected_owner
        || account.executable
        || account.is_signer
        || !account.is_writable
        || refund_authority.key == account.key
        || !refund_authority.is_writable
        || account.data_len() != expected_data_len
    {
        return Err(ProgramError::InvalidAccountData);
    }

    // A full tombstone precedes the zero-lamport state. If a later operation
    // in this instruction fails, transaction rollback restores the plan; if
    // settlement succeeds, resize+System assignment prevent same-transaction
    // account revival from restoring a decodable ASPS/ASRS image.
    account.try_borrow_mut_data()?.fill(0xff);
    let refund = account.lamports();
    {
        let mut destination_lamports = refund_authority.try_borrow_mut_lamports()?;
        let mut account_lamports = account.try_borrow_mut_lamports()?;
        let next = (**destination_lamports)
            .checked_add(refund)
            .ok_or(PoolV1ProgramError::ArithmeticOverflow)?;
        **destination_lamports = next;
        **account_lamports = 0;
    }
    account.assign(&system_program::id());
    account.resize(0)?;
    Ok(())
}

fn PoolM_authority_native(plan_authority:&AccountInfo)->ProgramResult {
if !plan_authority.is_signer
        || !plan_authority.is_writable
        || plan_authority.executable
        || plan_authority.owner != &system_program::id()
    {
        return Err(PoolV1ProgramError::InvalidPayer.into());
    }
Ok(())
}

#[cfg(kani)]
mod PoolM_proofs {
use super::*;
fn project(a:&AccountInfo,id:&Pubkey)->reference::Account {
 reference::Account {owner_matches:a.owner==id, system_owned:a.owner==&system_program::id(),executable:a.executable,signer:a.is_signer,writable:a.is_writable,len:a.data_len()}
}

#[kani::proof]
#[kani::unwind(34)]
fn PoolM_prepared_split_192() {
 let id=Pubkey::new_from_array([7;32]);let key=Pubkey::new_from_array([8;32]);
 let pool_owner:bool=kani::any();let owner=if pool_owner {id}else{Pubkey::new_from_array([9;32])};
 let mut data=[0u8;192];let mut balance=1;
 let a=AccountInfo::new(&key,kani::any(),kani::any(),&mut balance,&mut data,&owner,kani::any(),0);
 let size:usize=kani::any();
 let actual=require_prepared_plan_account_v1(&a,&id,size);
 let expected=if reference::prepared(project(&a,&id),size)==0 {Ok(())} else {Err(ProgramError::InvalidAccountData)};
 assert_eq!(actual,expected);
 kani::cover!(actual.is_ok(),"success arm reachable");kani::cover!(actual.is_err(),"rejection arm reachable");
}
}
