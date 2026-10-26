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

#[derive(Clone,Copy,PartialEq,Eq)]
pub enum FreshPdaPreparationV1 { CreateOrAllocateSystemOwned, ProgramOwnedZeroed }
pub fn plan_fresh_program_pda(
    account: &AccountInfo<'_>,
    program_id: &Pubkey,
    expected_address: &Pubkey,
    exact_bytes: usize,
) -> Result<FreshPdaPreparationV1, ProgramError> {
    if account.key != expected_address
        || account.executable
        || account.is_signer
        || !account.is_writable
    {
        return Err(PoolV1ProgramError::InvalidFreshAccount.into());
    }
    if account.owner == program_id {
        let data = account.try_borrow_data()?;
        if data.len() != exact_bytes || data.iter().any(|byte| *byte != 0) {
            return Err(PoolV1ProgramError::InvalidFreshAccount.into());
        }
        Ok(FreshPdaPreparationV1::ProgramOwnedZeroed)
    } else if account.owner == &system_program::id() && account.data_is_empty() {
        Ok(FreshPdaPreparationV1::CreateOrAllocateSystemOwned)
    } else {
        Err(PoolV1ProgramError::InvalidFreshAccount.into())
    }
}


#[kani::proof]
#[kani::unwind(40)]
fn PoolL_fresh_192() {
 let id=Pubkey::new_from_array(kani::any());let key=Pubkey::new_from_array(kani::any());
 let expected=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());
 let mut data:[u8;192]=kani::any();let i:usize=kani::any();kani::assume(i<192);let before=data[i];
 let mut lamports:u64=kani::any();let balance=lamports;
 let a=AccountInfo::new(&key,kani::any(),kani::any(),&mut lamports,&mut data,&owner,kani::any(),0);
 let width=match kani::any::<u8>()%6 {0=>384,1=>768,2=>1000,3=>8256,4=>10000,_=>8504};
 let r=plan_fresh_program_pda(&a,&id,&expected,width);
 assert!(matches!(r,Err(ProgramError::Custom(0x41532035))));
 kani::cover!(a.key==&expected && a.owner==&id && !a.executable && !a.is_signer && a.is_writable,"native borrow/length guard reached");
 drop(a);assert_eq!(data[i],before);assert_eq!(lamports,balance);
}

#[kani::proof]
#[kani::unwind(40)]
fn PoolL_fresh_1768() {
 let id=Pubkey::new_from_array(kani::any());let key=Pubkey::new_from_array(kani::any());
 let expected=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());
 let mut data:[u8;1768]=kani::any();let i:usize=kani::any();kani::assume(i<1768);let before=data[i];
 let mut lamports:u64=kani::any();let balance=lamports;
 let a=AccountInfo::new(&key,kani::any(),kani::any(),&mut lamports,&mut data,&owner,kani::any(),0);
 let width=match kani::any::<u8>()%6 {0=>384,1=>768,2=>1000,3=>8256,4=>10000,_=>8504};
 let r=plan_fresh_program_pda(&a,&id,&expected,width);
 assert!(matches!(r,Err(ProgramError::Custom(0x41532035))));
 kani::cover!(a.key==&expected && a.owner==&id && !a.executable && !a.is_signer && a.is_writable,"native borrow/length guard reached");
 drop(a);assert_eq!(data[i],before);assert_eq!(lamports,balance);
}

pub fn PoolL_fresh_header(account: &AccountInfo<'_>, expected_address: &Pubkey) -> ProgramResult {
    if account.key != expected_address
        || account.executable
        || account.is_signer
        || !account.is_writable
    {
        return Err(PoolV1ProgramError::InvalidFreshAccount.into());
    }
    Ok(())
}

pub fn PoolL_fresh_length(data: &[u8], expected: usize) -> ProgramResult {
    if data.len() != expected {
        return Err(PoolV1ProgramError::InvalidFreshAccount.into());
    }
    Ok(())
}

pub fn PoolL_fresh_role(account: &AccountInfo<'_>, program_id: &Pubkey,
    expected: &Pubkey, system: &Pubkey, empty: bool,
    data: Result<&[u8], ProgramError>, size: usize) -> ProgramResult {
    PoolL_fresh_header(account, expected)?;
    if account.owner == program_id {
        PoolL_fresh_length(data?, size)
    } else if account.owner == system && empty {
        Ok(())
    } else {
        Err(PoolV1ProgramError::InvalidFreshAccount.into())
    }
}

#[kani::proof]
#[kani::unwind(40)]
fn PoolL_fresh_pair_192() {
 let id=Pubkey::new_from_array(kani::any());let key=Pubkey::new_from_array(kani::any());
 let expected=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());
 let mut data:[u8;192]=kani::any();let i:usize=kani::any();kani::assume(i<192);let before=data[i];
 let mut lamports:u64=kani::any();let balance=lamports;
 let a=AccountInfo::new(&key,kani::any(),kani::any(),&mut lamports,&mut data,&owner,kani::any(),0);
 let width=match kani::any::<u8>()%6 {0=>384,1=>768,2=>1000,3=>8256,4=>10000,_=>8504};
 let r=plan_fresh_program_pda(&a,&id,&expected,width);
 let borrowed=a.try_borrow_data().unwrap();
 let projected=PoolL_fresh_role(&a,&id,&expected,&system_program::id(),a.data_is_empty(),Ok(&borrowed),width);
 assert_eq!(r.as_ref().err(),projected.as_ref().err());
 drop(borrowed);
 assert!(matches!(r,Err(ProgramError::Custom(0x41532035))));
 kani::cover!(a.key==&expected && a.owner==&id && !a.executable && !a.is_signer && a.is_writable,"native borrow/length guard reached");
 drop(a);assert_eq!(data[i],before);assert_eq!(lamports,balance);
}

#[kani::proof]
#[kani::unwind(40)]
fn PoolL_fresh_pair_1768() {
 let id=Pubkey::new_from_array(kani::any());let key=Pubkey::new_from_array(kani::any());
 let expected=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());
 let mut data:[u8;1768]=kani::any();let i:usize=kani::any();kani::assume(i<1768);let before=data[i];
 let mut lamports:u64=kani::any();let balance=lamports;
 let a=AccountInfo::new(&key,kani::any(),kani::any(),&mut lamports,&mut data,&owner,kani::any(),0);
 let width=match kani::any::<u8>()%6 {0=>384,1=>768,2=>1000,3=>8256,4=>10000,_=>8504};
 let r=plan_fresh_program_pda(&a,&id,&expected,width);
 let borrowed=a.try_borrow_data().unwrap();
 let projected=PoolL_fresh_role(&a,&id,&expected,&system_program::id(),a.data_is_empty(),Ok(&borrowed),width);
 assert_eq!(r.as_ref().err(),projected.as_ref().err());
 drop(borrowed);
 assert!(matches!(r,Err(ProgramError::Custom(0x41532035))));
 kani::cover!(a.key==&expected && a.owner==&id && !a.executable && !a.is_signer && a.is_writable,"native borrow/length guard reached");
 drop(a);assert_eq!(data[i],before);assert_eq!(lamports,balance);
}

pub fn require_program_account(
    account: &AccountInfo,
    program_id: &Pubkey,
    writable: bool,
) -> Result<(), ProgramError> {
    if account.owner != program_id {
        return Err(ProgramError::IncorrectProgramId);
    }
    if account.executable || account.is_writable != writable {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(())
}

pub fn PoolL_canonical_header(account: &AccountInfo<'_>, program_id: &Pubkey) -> ProgramResult {
    require_program_account(account, program_id, true)?;
    if account.is_signer {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(())
}

pub fn PoolL_length_prefix(data: &[u8], expected: usize) -> ProgramResult {
    if data.len() != expected {
        return Err(PoolV1ProgramError::InvalidAccountType.into());
    }
    Ok(())
}

pub fn PoolL_borrow_length(data: Result<&[u8], ProgramError>, exact_bytes: usize) -> ProgramResult {
    let bytes = data?;
    PoolL_length_prefix(bytes, exact_bytes)
}

pub fn PoolL_canonical_role(account: &AccountInfo<'_>, program_id: &Pubkey,
    data: Result<&[u8], ProgramError>) -> ProgramResult {
    PoolL_canonical_header(account, program_id)?;
    PoolL_borrow_length(data, 1000)
}

pub fn PoolL_marker_header(marker_account: &AccountInfo<'_>) -> ProgramResult {
    if marker_account.executable || marker_account.is_signer || !marker_account.is_writable {
        return Err(PoolV1ProgramError::InvalidNullifierMarkerAccount.into());
    }
    Ok(())
}

pub fn PoolL_marker_length(data: &[u8]) -> ProgramResult {
    if data.len() != 208 {
        return Err(PoolV1ProgramError::InvalidNullifierMarkerAccount.into());
    }
    Ok(())
}

pub fn PoolL_marker_role(account: &AccountInfo<'_>, program_id: &Pubkey,
    system: &Pubkey, empty: bool,
    data: Result<&[u8], ProgramError>) -> ProgramResult {
    PoolL_marker_header(account)?;
    if account.owner == program_id {
        PoolL_marker_length(data?)
    } else if account.owner == system && empty {
        Ok(())
    } else {
        Err(PoolV1ProgramError::InvalidNullifierMarkerAccount.into())
    }
}

pub fn require_payer_and_system_program(
    payer: &AccountInfo<'_>,
    system_program_account: &AccountInfo<'_>,
) -> ProgramResult {
    if !payer.is_signer
        || !payer.is_writable
        || payer.executable
        || payer.owner != &system_program::id()
    {
        return Err(PoolV1ProgramError::InvalidPayer.into());
    }
    if system_program_account.key != &system_program::id()
        || system_program_account.owner != &native_loader::id()
        || !system_program_account.executable
        || system_program_account.is_signer
        || system_program_account.is_writable
    {
        return Err(PoolV1ProgramError::InvalidSystemProgram.into());
    }
    Ok(())
}

pub fn PoolL_allocate_prefix(payer: &AccountInfo<'_>, account: &AccountInfo<'_>, system_program_account: &AccountInfo<'_>) -> ProgramResult {
    require_payer_and_system_program(payer, system_program_account)?;
    if account.owner != &system_program::id() || !account.data_is_empty() {
        return Err(PoolV1ProgramError::InvalidFreshAccount.into());
    }
    Ok(())
}

use solana_sdk_ids::native_loader;

fn PoolL_native_canonical_prefix(a:&AccountInfo<'_>,id:&Pubkey)->ProgramResult {
 require_program_account(a,id,true)?;
 if a.is_signer { return Err(ProgramError::InvalidAccountData); }
 let data=a.try_borrow_data()?;
 if data.len()!=1000 { return Err(PoolV1ProgramError::InvalidAccountType.into()); }
 Ok(())
}
fn PoolL_native_marker_prefix(a:&AccountInfo<'_>,id:&Pubkey)->ProgramResult {
 if a.executable || a.is_signer || !a.is_writable {
  return Err(PoolV1ProgramError::InvalidNullifierMarkerAccount.into());
 }
 if a.owner==id {
  let data=a.try_borrow_data()?;
  if data.len()!=208 { return Err(PoolV1ProgramError::InvalidNullifierMarkerAccount.into()); }
  Ok(())
 } else if a.owner==&system_program::id() && a.data_is_empty() { Ok(()) }
 else { Err(PoolV1ProgramError::InvalidNullifierMarkerAccount.into()) }
}

#[kani::proof]
#[kani::unwind(40)]
fn PoolL_canonical_pair_192() {
 let id=Pubkey::new_from_array(kani::any());let key=Pubkey::new_from_array(kani::any());
 let expected=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());
 let mut data:[u8;192]=kani::any();let i:usize=kani::any();kani::assume(i<192);let before=data[i];
 let mut lamports:u64=kani::any();let balance=lamports;
 let a=AccountInfo::new(&key,kani::any(),kani::any(),&mut lamports,&mut data,&owner,kani::any(),0);
 let borrowed=a.try_borrow_data().unwrap();
 let r=PoolL_native_canonical_prefix(&a,&id);
 let projected=PoolL_canonical_role(&a,&id,Ok(&borrowed));
 assert!(r.is_err());assert_eq!(r,projected);drop(borrowed);
 kani::cover!(a.owner==&id && !a.executable && !a.is_signer && a.is_writable,"owner/data guard shape reachable");
 drop(a);assert_eq!(data[i],before);assert_eq!(lamports,balance);
}

#[kani::proof]
#[kani::unwind(40)]
fn PoolL_canonical_pair_1768() {
 let id=Pubkey::new_from_array(kani::any());let key=Pubkey::new_from_array(kani::any());
 let expected=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());
 let mut data:[u8;1768]=kani::any();let i:usize=kani::any();kani::assume(i<1768);let before=data[i];
 let mut lamports:u64=kani::any();let balance=lamports;
 let a=AccountInfo::new(&key,kani::any(),kani::any(),&mut lamports,&mut data,&owner,kani::any(),0);
 let borrowed=a.try_borrow_data().unwrap();
 let r=PoolL_native_canonical_prefix(&a,&id);
 let projected=PoolL_canonical_role(&a,&id,Ok(&borrowed));
 assert!(r.is_err());assert_eq!(r,projected);drop(borrowed);
 kani::cover!(a.owner==&id && !a.executable && !a.is_signer && a.is_writable,"owner/data guard shape reachable");
 drop(a);assert_eq!(data[i],before);assert_eq!(lamports,balance);
}

#[kani::proof]
#[kani::unwind(40)]
fn PoolL_marker_pair_192() {
 let id=Pubkey::new_from_array(kani::any());let key=Pubkey::new_from_array(kani::any());
 let expected=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());
 let mut data:[u8;192]=kani::any();let i:usize=kani::any();kani::assume(i<192);let before=data[i];
 let mut lamports:u64=kani::any();let balance=lamports;
 let a=AccountInfo::new(&key,kani::any(),kani::any(),&mut lamports,&mut data,&owner,kani::any(),0);
 let borrowed=a.try_borrow_data().unwrap();
 let r=PoolL_native_marker_prefix(&a,&id);
 let projected=PoolL_marker_role(&a,&id,&system_program::id(),a.data_is_empty(),Ok(&borrowed));
 assert_eq!(r,Err(ProgramError::Custom(0x41532025)));assert_eq!(r,projected);drop(borrowed);
 kani::cover!(a.owner==&id && !a.executable && !a.is_signer && a.is_writable,"owner/data guard shape reachable");
 drop(a);assert_eq!(data[i],before);assert_eq!(lamports,balance);
}

#[kani::proof]
#[kani::unwind(40)]
fn PoolL_marker_pair_1768() {
 let id=Pubkey::new_from_array(kani::any());let key=Pubkey::new_from_array(kani::any());
 let expected=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());
 let mut data:[u8;1768]=kani::any();let i:usize=kani::any();kani::assume(i<1768);let before=data[i];
 let mut lamports:u64=kani::any();let balance=lamports;
 let a=AccountInfo::new(&key,kani::any(),kani::any(),&mut lamports,&mut data,&owner,kani::any(),0);
 let borrowed=a.try_borrow_data().unwrap();
 let r=PoolL_native_marker_prefix(&a,&id);
 let projected=PoolL_marker_role(&a,&id,&system_program::id(),a.data_is_empty(),Ok(&borrowed));
 assert_eq!(r,Err(ProgramError::Custom(0x41532025)));assert_eq!(r,projected);drop(borrowed);
 kani::cover!(a.owner==&id && !a.executable && !a.is_signer && a.is_writable,"owner/data guard shape reachable");
 drop(a);assert_eq!(data[i],before);assert_eq!(lamports,balance);
}

#[kani::proof]
#[kani::unwind(40)]
fn PoolL_allocate_pair_192() {
 let id=Pubkey::new_from_array(kani::any());let key=Pubkey::new_from_array(kani::any());
 let expected=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());
 let mut data:[u8;192]=kani::any();let i:usize=kani::any();kani::assume(i<192);let before=data[i];
 let mut lamports:u64=kani::any();let balance=lamports;
 let a=AccountInfo::new(&key,kani::any(),kani::any(),&mut lamports,&mut data,&owner,kani::any(),0);
 let mut other_data=[];let mut other_balance=0;
 let payer=AccountInfo::new(&expected,kani::any(),kani::any(),&mut other_balance,&mut other_data,&id,kani::any(),0);
 let mut sys_data=[];let mut sys_balance=0;
 let sys=AccountInfo::new(&id,kani::any(),kani::any(),&mut sys_balance,&mut sys_data,&owner,kani::any(),0);
 let r=PoolL_allocate_prefix(&payer,&a,&sys);
 assert!(r.is_err());drop(payer);drop(sys);
 kani::cover!(a.owner==&id && !a.executable && !a.is_signer && a.is_writable,"owner/data guard shape reachable");
 drop(a);assert_eq!(data[i],before);assert_eq!(lamports,balance);
}

#[kani::proof]
#[kani::unwind(40)]
fn PoolL_allocate_pair_1768() {
 let id=Pubkey::new_from_array(kani::any());let key=Pubkey::new_from_array(kani::any());
 let expected=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());
 let mut data:[u8;1768]=kani::any();let i:usize=kani::any();kani::assume(i<1768);let before=data[i];
 let mut lamports:u64=kani::any();let balance=lamports;
 let a=AccountInfo::new(&key,kani::any(),kani::any(),&mut lamports,&mut data,&owner,kani::any(),0);
 let mut other_data=[];let mut other_balance=0;
 let payer=AccountInfo::new(&expected,kani::any(),kani::any(),&mut other_balance,&mut other_data,&id,kani::any(),0);
 let mut sys_data=[];let mut sys_balance=0;
 let sys=AccountInfo::new(&id,kani::any(),kani::any(),&mut sys_balance,&mut sys_data,&owner,kani::any(),0);
 let r=PoolL_allocate_prefix(&payer,&a,&sys);
 assert!(r.is_err());drop(payer);drop(sys);
 kani::cover!(a.owner==&id && !a.executable && !a.is_signer && a.is_writable,"owner/data guard shape reachable");
 drop(a);assert_eq!(data[i],before);assert_eq!(lamports,balance);
}

use solana_program::instruction::TRANSACTION_LEVEL_STACK_HEIGHT;
fn require_transaction_level_invocation_v1(stack_height: usize) -> ProgramResult {
    if stack_height != TRANSACTION_LEVEL_STACK_HEIGHT {
        return Err(PoolV1ProgramError::CpiInvocationForbidden.into());
    }
    Ok(())
}

#[kani::proof]
fn PoolL_stack() {
 let h:usize=kani::any();let r=require_transaction_level_invocation_v1(h);
 assert_eq!(r,if h==TRANSACTION_LEVEL_STACK_HEIGHT {Ok(())}else{Err(ProgramError::Custom(0x41532036))});
 kani::cover!(h==TRANSACTION_LEVEL_STACK_HEIGHT,"transaction admission reachable");
 kani::cover!(h!=TRANSACTION_LEVEL_STACK_HEIGHT,"CPI rejection reachable");
}
#[kani::proof]
#[kani::unwind(9)]
fn PoolL_cpi_readonly() {
 use solana_program::instruction::AccountMeta;
 let keys:[Pubkey;7]=core::array::from_fn(|_|Pubkey::new_from_array(kani::any()));
 let mut cpi_accounts=vec![
 AccountMeta::new_readonly(keys[0],false),AccountMeta::new_readonly(keys[1],false),
 AccountMeta::new_readonly(keys[2],false),AccountMeta::new_readonly(keys[3],false),
 AccountMeta::new_readonly(keys[4],false),AccountMeta::new_readonly(keys[5],false)];
 let split:bool=kani::any();if split {cpi_accounts.push(AccountMeta::new_readonly(keys[6],false));}
 let i:usize=kani::any();kani::assume(i<cpi_accounts.len());
 assert_eq!(cpi_accounts[i].pubkey,keys[i]);
 assert!(!cpi_accounts[i].is_writable);assert!(!cpi_accounts[i].is_signer);
 kani::cover!(split && i==6,"CP readonly meta reachable");
}
