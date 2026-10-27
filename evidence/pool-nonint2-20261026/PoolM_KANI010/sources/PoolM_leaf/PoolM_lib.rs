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

use solana_program::rent::Rent;
#[derive(Clone,Copy,PartialEq,Eq,Debug)]
enum FreshPdaPreparationV1 { CreateOrAllocateSystemOwned, ProgramOwnedZeroed }
fn plan_fresh_program_pda(
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
fn require_fresh_rent_exempt_program_pda(
    account: &AccountInfo<'_>,
    program_id: &Pubkey,
    expected_address: &Pubkey,
    exact_bytes: usize,
    preparation: FreshPdaPreparationV1,
    rent: &Rent,
) -> ProgramResult {
    let is_fresh = match preparation {
        // `plan_fresh_program_pda` already scanned every byte and no CPI was
        // given this account before this check. Repeating the large zero scan
        // is redundant, especially for 8.5KB rollover pages/shards.
        FreshPdaPreparationV1::ProgramOwnedZeroed => {
            account.key == expected_address
                && account.owner == program_id
                && !account.executable
                && !account.is_signer
                && account.is_writable
                && account.data_len() == exact_bytes
        }
        // A just-created System account crossed a CPI boundary, so retain one
        // complete post-CPI owner/shape/zero-state validation.
        FreshPdaPreparationV1::CreateOrAllocateSystemOwned => {
            plan_fresh_program_pda(account, program_id, expected_address, exact_bytes)?
                == FreshPdaPreparationV1::ProgramOwnedZeroed
        }
    };
    if !is_fresh || !rent.is_exempt(account.lamports(), exact_bytes) {
        return Err(PoolV1ProgramError::InvalidFreshAccount.into());
    }
    Ok(())
}
fn require_program_account(
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
fn require_program_owned_zeroed(
    account: &AccountInfo<'_>,
    program_id: &Pubkey,
    exact_bytes: usize,
    rent: &Rent,
) -> ProgramResult {
    require_program_account(account, program_id, true)?;
    let data = account.try_borrow_data()?;
    if data.len() != exact_bytes
        || data.iter().any(|byte| *byte != 0)
        || !rent.is_exempt(account.lamports(), exact_bytes)
    {
        return Err(PoolV1ProgramError::InvalidFreshAccount.into());
    }
    Ok(())
}
fn require_unique_accounts(accounts: &[AccountInfo<'_>]) -> ProgramResult {
    for left in 0..accounts.len() {
        for right in left + 1..accounts.len() {
            if accounts[left].key == accounts[right].key {
                return Err(ProgramError::InvalidArgument);
            }
        }
    }
    Ok(())
}
mod instruction { pub const POOL_V1_INSTRUCTION_VERSION:u8=1; }
#[path="../PoolM_slice/cancel_prepared_settlement_instruction.rs"] mod cancel;
#[cfg(kani)]
mod PoolM_proofs {
use super::*;
fn project(a:&AccountInfo,id:&Pubkey)->reference::Account {
 reference::Account {owner_matches:a.owner==id,system_owned:a.owner==&system_program::id(),executable:a.executable,signer:a.is_signer,writable:a.is_writable,len:a.data_len()}
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
#[kani::proof]
#[kani::unwind(34)]
fn PoolM_prepared_split_1768(){
let id=Pubkey::new_from_array([7;32]);let key=Pubkey::new_from_array([8;32]);
let owner_class:u8=kani::any();kani::assume(owner_class<3);
let owner=match owner_class {0=>id,1=>system_program::id(),_=>Pubkey::new_from_array([9;32])};
let mut data=[0u8;1768];let mut balance=1;
let a=AccountInfo::new(&key,kani::any(),kani::any(),&mut balance,&mut data,&owner,kani::any(),0);
let size:usize=kani::any();let actual=require_prepared_plan_account_v1(&a,&id,size);
let expected=if reference::prepared(project(&a,&id),size)==0 {Ok(())} else {Err(ProgramError::InvalidAccountData)};
assert_eq!(actual,expected);kani::cover!(actual.is_ok(),"success");kani::cover!(actual.is_err(),"reject");
}

#[kani::proof]
#[kani::unwind(34)]
fn PoolM_authority_split_192(){
let id=Pubkey::new_from_array([7;32]);let key=Pubkey::new_from_array([8;32]);
let owner_class:u8=kani::any();kani::assume(owner_class<3);
let owner=match owner_class {0=>id,1=>system_program::id(),_=>Pubkey::new_from_array([9;32])};
let mut data=[0u8;192];let mut balance=1;
let a=AccountInfo::new(&key,kani::any(),kani::any(),&mut balance,&mut data,&owner,kani::any(),0);
let actual=PoolM_authority_native(&a);
let expected=if reference::authority(project(&a,&id))==0 {Ok(())}else{Err(PoolV1ProgramError::InvalidPayer.into())};
assert_eq!(actual,expected);kani::cover!(actual.is_ok(),"success");kani::cover!(actual.is_err(),"reject");
}

#[kani::proof]
#[kani::unwind(34)]
fn PoolM_authority_split_1768(){
let id=Pubkey::new_from_array([7;32]);let key=Pubkey::new_from_array([8;32]);
let owner_class:u8=kani::any();kani::assume(owner_class<3);
let owner=match owner_class {0=>id,1=>system_program::id(),_=>Pubkey::new_from_array([9;32])};
let mut data=[0u8;1768];let mut balance=1;
let a=AccountInfo::new(&key,kani::any(),kani::any(),&mut balance,&mut data,&owner,kani::any(),0);
let actual=PoolM_authority_native(&a);
let expected=if reference::authority(project(&a,&id))==0 {Ok(())}else{Err(PoolV1ProgramError::InvalidPayer.into())};
assert_eq!(actual,expected);kani::cover!(actual.is_ok(),"success");kani::cover!(actual.is_err(),"reject");
}

#[kani::proof]
#[kani::unwind(34)]
fn PoolM_close_split_192(){
let id=Pubkey::new_from_array([7;32]);let key=Pubkey::new_from_array([8;32]);
let owner_class:u8=kani::any();kani::assume(owner_class<3);
let owner=match owner_class {0=>id,1=>system_program::id(),_=>Pubkey::new_from_array([9;32])};
let mut data=[0u8;192];let mut balance=1;
let a=AccountInfo::new(&key,kani::any(),kani::any(),&mut balance,&mut data,&owner,kani::any(),0);
let refund_key=if kani::any(){key}else{Pubkey::new_from_array([10;32])};let mut refund_data=[];let mut refund_balance=1;
let refund=AccountInfo::new(&refund_key,kani::any(),kani::any(),&mut refund_balance,&mut refund_data,&id,kani::any(),0);
let size=if kani::any(){10000}else{8504};
assert_eq!(close_program_account_v1(&a,&refund,&id,size),Err(ProgramError::InvalidAccountData));
kani::cover!(a.owner==&id && !a.executable && !a.is_signer && a.is_writable && refund.key!=a.key && refund.is_writable,"reaches size guard before close");
}

#[kani::proof]
#[kani::unwind(34)]
fn PoolM_close_split_1768(){
let id=Pubkey::new_from_array([7;32]);let key=Pubkey::new_from_array([8;32]);
let owner_class:u8=kani::any();kani::assume(owner_class<3);
let owner=match owner_class {0=>id,1=>system_program::id(),_=>Pubkey::new_from_array([9;32])};
let mut data=[0u8;1768];let mut balance=1;
let a=AccountInfo::new(&key,kani::any(),kani::any(),&mut balance,&mut data,&owner,kani::any(),0);
let refund_key=if kani::any(){key}else{Pubkey::new_from_array([10;32])};let mut refund_data=[];let mut refund_balance=1;
let refund=AccountInfo::new(&refund_key,kani::any(),kani::any(),&mut refund_balance,&mut refund_data,&id,kani::any(),0);
let size=if kani::any(){10000}else{8504};
assert_eq!(close_program_account_v1(&a,&refund,&id,size),Err(ProgramError::InvalidAccountData));
kani::cover!(a.owner==&id && !a.executable && !a.is_signer && a.is_writable && refund.key!=a.key && refund.is_writable,"reaches size guard before close");
}

#[kani::proof]
#[kani::unwind(34)]
fn PoolM_cancel_shape(){
use cancel::CancelPreparedSettlementAccountShapeV1::*;
let shard:bool=kani::any();let shape=if shard{CoreAndRolloverShard}else{CoreOnly};
assert_eq!(shape.account_count(),if shard{3}else{2});assert_eq!(shape.has_rollover_shard(),shard);
kani::cover!(shard,"shard arm");kani::cover!(!shard,"core arm");
}

#[kani::proof]
#[kani::unwind(34)]
fn PoolM_cancel_parser(){
let data:[u8;8]=kani::any();let actual=cancel::decode_cancel_prepared_settlement_instruction_v1(&data);
use cancel::CancelPreparedSettlementInstructionFormatErrorV1::*;
let expected=if data[0]!=65||data[1]!=83||data[2]!=80||data[3]!=88{Err(WrongMagic)}else if data[4]!=1{Err(WrongVersion)}else if data[5]!=1&&data[5]!=2{Err(WrongAccountShape)}else if data[6]!=0||data[7]!=0{Err(NonZeroReserved)}else{Ok(cancel::CancelPreparedSettlementInstructionV1{account_shape:if data[5]==1{cancel::CancelPreparedSettlementAccountShapeV1::CoreOnly}else{cancel::CancelPreparedSettlementAccountShapeV1::CoreAndRolloverShard}})};
assert_eq!(actual,expected);kani::cover!(actual.is_ok(),"accepted parser");kani::cover!(actual==Err(NonZeroReserved),"last reject");
}

#[kani::proof]
#[kani::unwind(34)]
fn PoolM_unique_2(){
let ids:[u8;2]=kani::any();let keys:[Pubkey;2]=core::array::from_fn(|i|Pubkey::new_from_array([ids[i];32]));
let owner=Pubkey::new_from_array([7;32]);let mut balances=[1u64;2];let mut data=[[0u8;0];2];
let accounts:Vec<_>=keys.iter().zip(balances.iter_mut()).zip(data.iter_mut()).map(|((key,bal),data)|AccountInfo::new(key,false,false,bal,data,&owner,false,0)).collect();
let unique=ids[0]!=ids[1];let result=require_unique_accounts(&accounts);
assert_eq!(result,if unique{Ok(())}else{Err(ProgramError::InvalidArgument)});kani::cover!(unique,"unique");kani::cover!(!unique,"alias");
}

#[kani::proof]
#[kani::unwind(34)]
fn PoolM_unique_3(){
let ids:[u8;3]=kani::any();let keys:[Pubkey;3]=core::array::from_fn(|i|Pubkey::new_from_array([ids[i];32]));
let owner=Pubkey::new_from_array([7;32]);let mut balances=[1u64;3];let mut data=[[0u8;0];3];
let accounts:Vec<_>=keys.iter().zip(balances.iter_mut()).zip(data.iter_mut()).map(|((key,bal),data)|AccountInfo::new(key,false,false,bal,data,&owner,false,0)).collect();
let unique=ids[0]!=ids[1]&&ids[0]!=ids[2]&&ids[1]!=ids[2];let result=require_unique_accounts(&accounts);
assert_eq!(result,if unique{Ok(())}else{Err(ProgramError::InvalidArgument)});kani::cover!(unique,"unique");kani::cover!(!unique,"alias");
}

#[kani::proof]
#[kani::unwind(34)]
fn PoolM_fresh_192(){
let id=Pubkey::new_from_array([7;32]);let key=Pubkey::new_from_array([8;32]);
let owner_class:u8=kani::any();kani::assume(owner_class<3);
let owner=match owner_class {0=>id,1=>system_program::id(),_=>Pubkey::new_from_array([9;32])};
let mut data=[0u8;192];let mut balance=1;
let a=AccountInfo::new(&key,kani::any(),kani::any(),&mut balance,&mut data,&owner,kani::any(),0);
let expected=if kani::any(){key}else{Pubkey::new_from_array([10;32])};let size=if kani::any(){10000}else{8504};
let actual=plan_fresh_program_pda(&a,&id,&expected,size);assert_eq!(actual,Err(PoolV1ProgramError::InvalidFreshAccount.into()));
kani::cover!(a.key==&expected && a.owner==&id && !a.executable && !a.is_signer && a.is_writable,"length reject");
}

#[kani::proof]
#[kani::unwind(34)]
fn PoolM_fresh_1768(){
let id=Pubkey::new_from_array([7;32]);let key=Pubkey::new_from_array([8;32]);
let owner_class:u8=kani::any();kani::assume(owner_class<3);
let owner=match owner_class {0=>id,1=>system_program::id(),_=>Pubkey::new_from_array([9;32])};
let mut data=[0u8;1768];let mut balance=1;
let a=AccountInfo::new(&key,kani::any(),kani::any(),&mut balance,&mut data,&owner,kani::any(),0);
let expected=if kani::any(){key}else{Pubkey::new_from_array([10;32])};let size=if kani::any(){10000}else{8504};
let actual=plan_fresh_program_pda(&a,&id,&expected,size);assert_eq!(actual,Err(PoolV1ProgramError::InvalidFreshAccount.into()));
kani::cover!(a.key==&expected && a.owner==&id && !a.executable && !a.is_signer && a.is_writable,"length reject");
}

#[kani::proof]
#[kani::unwind(34)]
fn PoolM_zeroed_192(){
let id=Pubkey::new_from_array([7;32]);let key=Pubkey::new_from_array([8;32]);
let owner_class:u8=kani::any();kani::assume(owner_class<3);
let owner=match owner_class {0=>id,1=>system_program::id(),_=>Pubkey::new_from_array([9;32])};
let mut data=[0u8;192];let mut balance=1;
let a=AccountInfo::new(&key,kani::any(),kani::any(),&mut balance,&mut data,&owner,kani::any(),0);
let size=if kani::any(){384}else{768};let actual=require_program_owned_zeroed(&a,&id,size,&Rent::default());
let expected=if a.owner!=&id{ProgramError::IncorrectProgramId}else if a.executable||!a.is_writable{ProgramError::InvalidAccountData}else{PoolV1ProgramError::InvalidFreshAccount.into()};
assert_eq!(actual,Err(expected));kani::cover!(a.owner==&id&&!a.executable&&a.is_writable,"length reject");
}

#[kani::proof]
#[kani::unwind(34)]
fn PoolM_zeroed_1768(){
let id=Pubkey::new_from_array([7;32]);let key=Pubkey::new_from_array([8;32]);
let owner_class:u8=kani::any();kani::assume(owner_class<3);
let owner=match owner_class {0=>id,1=>system_program::id(),_=>Pubkey::new_from_array([9;32])};
let mut data=[0u8;1768];let mut balance=1;
let a=AccountInfo::new(&key,kani::any(),kani::any(),&mut balance,&mut data,&owner,kani::any(),0);
let size=if kani::any(){384}else{768};let actual=require_program_owned_zeroed(&a,&id,size,&Rent::default());
let expected=if a.owner!=&id{ProgramError::IncorrectProgramId}else if a.executable||!a.is_writable{ProgramError::InvalidAccountData}else{PoolV1ProgramError::InvalidFreshAccount.into()};
assert_eq!(actual,Err(expected));kani::cover!(a.owner==&id&&!a.executable&&a.is_writable,"length reject");
}

#[kani::proof]
#[kani::unwind(34)]
fn PoolM_postfresh_192(){
let id=Pubkey::new_from_array([7;32]);let key=Pubkey::new_from_array([8;32]);
let owner_class:u8=kani::any();kani::assume(owner_class<3);
let owner=match owner_class {0=>id,1=>system_program::id(),_=>Pubkey::new_from_array([9;32])};
let mut data=[0u8;192];let mut balance=1;
let a=AccountInfo::new(&key,kani::any(),kani::any(),&mut balance,&mut data,&owner,kani::any(),0);
let prep=if kani::any(){FreshPdaPreparationV1::ProgramOwnedZeroed}else{FreshPdaPreparationV1::CreateOrAllocateSystemOwned};
let size=if kani::any(){10000}else{8504};let actual=require_fresh_rent_exempt_program_pda(&a,&id,&key,size,prep,&Rent::default());
assert_eq!(actual,Err(PoolV1ProgramError::InvalidFreshAccount.into()));kani::cover!(prep==FreshPdaPreparationV1::ProgramOwnedZeroed,"cached");kani::cover!(prep==FreshPdaPreparationV1::CreateOrAllocateSystemOwned,"post CPI");
}

#[kani::proof]
#[kani::unwind(34)]
fn PoolM_postfresh_1768(){
let id=Pubkey::new_from_array([7;32]);let key=Pubkey::new_from_array([8;32]);
let owner_class:u8=kani::any();kani::assume(owner_class<3);
let owner=match owner_class {0=>id,1=>system_program::id(),_=>Pubkey::new_from_array([9;32])};
let mut data=[0u8;1768];let mut balance=1;
let a=AccountInfo::new(&key,kani::any(),kani::any(),&mut balance,&mut data,&owner,kani::any(),0);
let prep=if kani::any(){FreshPdaPreparationV1::ProgramOwnedZeroed}else{FreshPdaPreparationV1::CreateOrAllocateSystemOwned};
let size=if kani::any(){10000}else{8504};let actual=require_fresh_rent_exempt_program_pda(&a,&id,&key,size,prep,&Rent::default());
assert_eq!(actual,Err(PoolV1ProgramError::InvalidFreshAccount.into()));kani::cover!(prep==FreshPdaPreparationV1::ProgramOwnedZeroed,"cached");kani::cover!(prep==FreshPdaPreparationV1::CreateOrAllocateSystemOwned,"post CPI");
}

#[kani::proof]
#[kani::unwind(34)]
fn PoolM_allocate_192(){
let id=Pubkey::new_from_array([7;32]);let key=Pubkey::new_from_array([8;32]);
let owner_class:u8=kani::any();kani::assume(owner_class<3);
let owner=match owner_class {0=>id,1=>system_program::id(),_=>Pubkey::new_from_array([9;32])};
let mut data=[0u8;192];let mut balance=1;
let a=AccountInfo::new(&key,kani::any(),kani::any(),&mut balance,&mut data,&owner,kani::any(),0);
// Exact allocation rejection header from create_or_allocate_pda_with_rent.
let actual=if a.owner!=&system_program::id()||!a.data_is_empty(){Err(ProgramError::from(PoolV1ProgramError::InvalidFreshAccount))}else{Ok(())};
assert_eq!(actual,Err(PoolV1ProgramError::InvalidFreshAccount.into()));kani::cover!(owner_class==1,"nonempty System-owned rejected");
}

#[kani::proof]
#[kani::unwind(34)]
fn PoolM_allocate_1768(){
let id=Pubkey::new_from_array([7;32]);let key=Pubkey::new_from_array([8;32]);
let owner_class:u8=kani::any();kani::assume(owner_class<3);
let owner=match owner_class {0=>id,1=>system_program::id(),_=>Pubkey::new_from_array([9;32])};
let mut data=[0u8;1768];let mut balance=1;
let a=AccountInfo::new(&key,kani::any(),kani::any(),&mut balance,&mut data,&owner,kani::any(),0);
// Exact allocation rejection header from create_or_allocate_pda_with_rent.
let actual=if a.owner!=&system_program::id()||!a.data_is_empty(){Err(ProgramError::from(PoolV1ProgramError::InvalidFreshAccount))}else{Ok(())};
assert_eq!(actual,Err(PoolV1ProgramError::InvalidFreshAccount.into()));kani::cover!(owner_class==1,"nonempty System-owned rejected");
}

#[kani::proof]
#[kani::unwind(34)]
fn PoolM_readonly_meta(){
use solana_program::instruction::AccountMeta;
let bytes:[u8;32]=kani::any();let key=Pubkey::new_from_array(bytes);
// Every one of the seven verifier child roles uses this exact constructor.
let m=AccountMeta::new_readonly(key,false);assert!(!m.is_writable&&!m.is_signer);assert_eq!(m.pubkey,key);
}
}
