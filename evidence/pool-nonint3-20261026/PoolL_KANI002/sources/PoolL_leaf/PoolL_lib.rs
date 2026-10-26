use solana_program::{account_info::AccountInfo,pubkey::Pubkey,program_error::ProgramError,entrypoint::ProgramResult,system_program};
#[path="../PoolL_slice/error.rs"] mod error;
use error::PoolV1ProgramError;
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

#[kani::proof]
#[kani::unwind(40)]
fn PoolL_close_192() {
 let id=Pubkey::new_from_array(kani::any());
 let key=Pubkey::new_from_array(kani::any());
 let other=Pubkey::new_from_array(kani::any());
 let owner=Pubkey::new_from_array(kani::any());
 let mut bytes:[u8;192]=kani::any();
 let p:usize=kani::any(); kani::assume(p<bytes.len()); let before=bytes[p];
 let mut lamports:u64=kani::any(); let initial=lamports;
 let mut refund_bytes=[]; let mut refund_balance:u64=kani::any();let old_refund=refund_balance;
 let a=AccountInfo::new(&key,kani::any(),kani::any(),&mut lamports,&mut bytes,&owner,kani::any(),0);
 let r=AccountInfo::new(&other,kani::any(),kani::any(),&mut refund_balance,&mut refund_bytes,&owner,kani::any(),0);
 let size=if kani::any(){10000}else{8504};
 let result=close_program_account_v1(&a,&r,&id,size);
 assert_eq!(result,Err(ProgramError::InvalidAccountData));
 drop(a);drop(r);assert_eq!(bytes[p],before);assert_eq!(lamports,initial);assert_eq!(refund_balance,old_refund);
}

#[kani::proof]
#[kani::unwind(40)]
fn PoolL_close_1768() {
 let id=Pubkey::new_from_array(kani::any());
 let key=Pubkey::new_from_array(kani::any());
 let other=Pubkey::new_from_array(kani::any());
 let owner=Pubkey::new_from_array(kani::any());
 let mut bytes:[u8;1768]=kani::any();
 let p:usize=kani::any(); kani::assume(p<bytes.len()); let before=bytes[p];
 let mut lamports:u64=kani::any(); let initial=lamports;
 let mut refund_bytes=[]; let mut refund_balance:u64=kani::any();let old_refund=refund_balance;
 let a=AccountInfo::new(&key,kani::any(),kani::any(),&mut lamports,&mut bytes,&owner,kani::any(),0);
 let r=AccountInfo::new(&other,kani::any(),kani::any(),&mut refund_balance,&mut refund_bytes,&owner,kani::any(),0);
 let size=if kani::any(){10000}else{8504};
 let result=close_program_account_v1(&a,&r,&id,size);
 assert_eq!(result,Err(ProgramError::InvalidAccountData));
 drop(a);drop(r);assert_eq!(bytes[p],before);assert_eq!(lamports,initial);assert_eq!(refund_balance,old_refund);
}
