fn PoolW_zero_reference(
    account: &AccountInfo<'_>, program_id: &Pubkey, exact_bytes: usize, rent: &Rent,
) -> ProgramResult {
    if account.owner != program_id { return Err(ProgramError::IncorrectProgramId); }
    if account.executable || !account.is_writable { return Err(ProgramError::InvalidAccountData); }
    let data = account.try_borrow_data()?;
    if data.len() != exact_bytes { return Err(PoolV1ProgramError::InvalidFreshAccount.into()); }
    for i in 0..data.len() {
        if data[i] != 0 { return Err(PoolV1ProgramError::InvalidFreshAccount.into()); }
    }
    if !rent.is_exempt(account.lamports(), exact_bytes) {
        return Err(PoolV1ProgramError::InvalidFreshAccount.into());
    }
    Ok(())
}

#[kani::proof]
#[kani::unwind(195)]
fn PoolW_zero_pair() {
    let id = Pubkey::new_from_array(kani::any());
    let owner = Pubkey::new_from_array(kani::any());
    let key = Pubkey::new_from_array(kani::any());
    let mut bytes: [u8; 193] = kani::any();
    let length: usize = kani::any(); kani::assume(length <= 193);
    let original = bytes;
    let mut lamports: u64 = kani::any(); let funds = lamports;
    let executable: bool = kani::any(); let writable: bool = kani::any();
    let account = AccountInfo::new(&key, kani::any(), writable, &mut lamports,
        &mut bytes[..length], &owner, executable, kani::any());
    let rent = Rent::default();
    let native = require_program_owned_zeroed(&account, &id, 192, &rent);
    let model = PoolW_zero_reference(&account, &id, 192, &rent);
    assert!(native == model);
    assert!(account.try_borrow_mut_data().is_ok());
    drop(account);
    assert!(bytes == original); assert!(lamports == funds);
}

#[kani::proof]
#[kani::unwind(195)]
fn PoolW_zero_borrow_conflict() {
    let id = Pubkey::new_from_array([7;32]); let key = Pubkey::new_from_array([8;32]);
    let mut bytes: [u8;192] = kani::any(); let original=bytes;
    let mut funds: u64 = kani::any(); let before=funds;
    let account=AccountInfo::new(&key, kani::any(), true, &mut funds, &mut bytes, &id, false, 0);
    let rent=Rent::default();
    let held=account.try_borrow_mut_data().unwrap();
    assert!(require_program_owned_zeroed(&account,&id,192,&rent)==Err(ProgramError::AccountBorrowFailed));
    assert!(PoolW_zero_reference(&account,&id,192,&rent)==Err(ProgramError::AccountBorrowFailed));
    drop(held); assert!(account.try_borrow_mut_data().is_ok()); drop(account);
    assert!(bytes==original); assert!(funds==before);
}

#[kani::proof]
fn PoolW_zero_metadata_precedes_borrow() {
    let id=Pubkey::new_from_array([7;32]); let other=Pubkey::new_from_array([8;32]);
    let owner_is_id:bool=kani::any();let owner=if owner_is_id {id} else {other};
    let writable:bool=kani::any();let executable:bool=kani::any();
    kani::assume(!owner_is_id || executable || !writable);
    let mut bytes:[u8;192]=kani::any();let original=bytes;let mut funds:u64=kani::any();let old=funds;
    let account=AccountInfo::new(&other,kani::any(),writable,&mut funds,&mut bytes,&owner,executable,0);
    let held=account.try_borrow_mut_data().unwrap();
    let expected=if !owner_is_id {ProgramError::IncorrectProgramId} else {ProgramError::InvalidAccountData};
    assert!(require_program_owned_zeroed(&account,&id,192,&Rent::default())==Err(expected.clone()));
    assert!(PoolW_zero_reference(&account,&id,192,&Rent::default())==Err(expected.clone()));
    drop(held);drop(account);assert!(bytes==original);assert!(funds==old);
}

#[kani::proof]
fn PoolW_zero_wrong_size() {
    let id=Pubkey::new_from_array([7;32]); let key=Pubkey::new_from_array([8;32]);
    let mut bytes:[u8;193]=kani::any();let original=bytes;let mut funds:u64=kani::any();let old=funds;
    let account=AccountInfo::new(&key,kani::any(),true,&mut funds,&mut bytes,&id,false,0);
    let expected=Err(PoolV1ProgramError::InvalidFreshAccount.into());
    assert!(require_program_owned_zeroed(&account,&id,192,&Rent::default())==expected);
    assert!(PoolW_zero_reference(&account,&id,192,&Rent::default())==expected);
    drop(account);assert!(bytes==original);assert!(funds==old);
}

#[kani::proof]
#[kani::unwind(195)]
fn PoolW_zero_all_zero_rent() {
    let id=Pubkey::new_from_array([7;32]);let key=Pubkey::new_from_array([8;32]);
    let mut bytes=[0u8;192];let mut funds:u64=kani::any();let old=funds;
    let account=AccountInfo::new(&key,kani::any(),true,&mut funds,&mut bytes,&id,false,0);
    let rent=Rent::default();
    let expected=if rent.is_exempt(old,192) {Ok(())} else {Err(PoolV1ProgramError::InvalidFreshAccount.into())};
    assert!(require_program_owned_zeroed(&account,&id,192,&rent)==expected);
    assert!(PoolW_zero_reference(&account,&id,192,&rent)==expected);
    drop(account);assert!(bytes==[0u8;192]);assert!(funds==old);
}

#[kani::proof]
#[kani::unwind(195)]
fn PoolW_zero_occupied_marker() {
    let id=Pubkey::new_from_array([7;32]);let key=Pubkey::new_from_array([8;32]);
    let mut bytes:[u8;192]=kani::any();kani::assume(bytes[0]!=0);let original=bytes;
    let mut funds:u64=kani::any();let old=funds;
    let account=AccountInfo::new(&key,kani::any(),true,&mut funds,&mut bytes,&id,false,0);
    assert!(require_program_owned_zeroed(&account,&id,192,&Rent::default())==Err(PoolV1ProgramError::InvalidFreshAccount.into()));
    drop(account);assert!(bytes==original);assert!(funds==old);
}

#[kani::proof]
#[kani::unwind(386)]
fn PoolW_copy_full_images() {
    let id=Pubkey::new_from_array([7;32]);let mk=Pubkey::new_from_array(kani::any());let ck=Pubkey::new_from_array(kani::any());
    kani::assume(mk!=ck);
    let mut m:[u8;384]=kani::any();let mut c:[u8;192]=kani::any();
    let mut ml:u64=kani::any();let mut cl:u64=kani::any();let oldml=ml;let oldcl=cl;
    let plan=PoolW_Planned{checkpoint_image:kani::any(),next_master_image:kani::any()};
    let master=AccountInfo::new(&mk,false,true,&mut ml,&mut m,&id,false,0);
    let checkpoint=AccountInfo::new(&ck,false,true,&mut cl,&mut c,&id,false,0);
    assert!(PoolW_copy_tail(&master,&checkpoint,&plan)==Ok(()));
    assert!(master.key==&mk && checkpoint.key==&ck);
    assert!(master.owner==&id && checkpoint.owner==&id);
    drop(master);drop(checkpoint);
    assert!(c==plan.checkpoint_image);assert!(m==plan.next_master_image);
    assert!(ml==oldml && cl==oldcl);
}

#[kani::proof]
fn PoolW_copy_checkpoint_borrow_error() {
    let id=Pubkey::new_from_array([7;32]);let mk=Pubkey::new_from_array([8;32]);let ck=Pubkey::new_from_array([9;32]);
    let mut m=[0u8;384];let mut c=[0u8;192];let mut ml=1;let mut cl=2;
    let plan=PoolW_Planned{checkpoint_image:[65u8;192],next_master_image:[42u8;384]};
    let master=AccountInfo::new(&mk,false,true,&mut ml,&mut m,&id,false,0);
    let checkpoint=AccountInfo::new(&ck,false,true,&mut cl,&mut c,&id,false,0);
    let held=checkpoint.try_borrow_data().unwrap();
    assert!(PoolW_copy_tail(&master,&checkpoint,&plan)==Err(ProgramError::AccountBorrowFailed));
    drop(held);drop(master);drop(checkpoint);
    assert!(m==[0u8;384] && c==[0u8;192]);assert!(ml==1 && cl==2);
}

#[kani::proof]
fn PoolW_zero_owner_error() {
    let id=Pubkey::new_from_array([7;32]);let owner=Pubkey::new_from_array([8;32]);let key=Pubkey::new_from_array([9;32]);
    let mut data:[u8;192]=kani::any();let original=data;let mut funds:u64=kani::any();let old=funds;
    let a=AccountInfo::new(&key,kani::any(),kani::any(),&mut funds,&mut data,&owner,kani::any(),0);
    assert!(require_program_owned_zeroed(&a,&id,192,&Rent::default())==Err(ProgramError::IncorrectProgramId));
    drop(a);assert!(data==original && funds==old);
}
#[kani::proof]
fn PoolW_zero_executable_error() {
    let id=Pubkey::new_from_array([7;32]);let key=Pubkey::new_from_array([9;32]);
    let mut data:[u8;192]=kani::any();let original=data;let mut funds:u64=kani::any();let old=funds;
    let a=AccountInfo::new(&key,kani::any(),kani::any(),&mut funds,&mut data,&id,true,0);
    assert!(require_program_owned_zeroed(&a,&id,192,&Rent::default())==Err(ProgramError::InvalidAccountData));
    drop(a);assert!(data==original && funds==old);
}
#[kani::proof]
fn PoolW_zero_readonly_error() {
    let id=Pubkey::new_from_array([7;32]);let key=Pubkey::new_from_array([9;32]);
    let mut data:[u8;192]=kani::any();let original=data;let mut funds:u64=kani::any();let old=funds;
    let a=AccountInfo::new(&key,kani::any(),false,&mut funds,&mut data,&id,false,0);
    assert!(require_program_owned_zeroed(&a,&id,192,&Rent::default())==Err(ProgramError::InvalidAccountData));
    drop(a);assert!(data==original && funds==old);
}
#[kani::proof]
fn PoolW_fresh_system_empty() {
    let id=Pubkey::new_from_array([7;32]);let key=Pubkey::new_from_array([9;32]);let owner=system_program::id();
    let mut data=[];let mut funds:u64=kani::any();let old=funds;
    let a=AccountInfo::new(&key,false,true,&mut funds,&mut data,&owner,false,0);
    assert!(plan_fresh_program_pda(&a,&id,&key,192)==Ok(FreshPdaPreparationV1::CreateOrAllocateSystemOwned));
    drop(a);assert!(funds==old);
}
#[kani::proof]
fn PoolW_fresh_system_occupied() {
    let id=Pubkey::new_from_array([7;32]);let key=Pubkey::new_from_array([9;32]);let owner=system_program::id();
    let mut data:[u8;192]=kani::any();let original=data;let mut funds:u64=kani::any();let old=funds;
    let a=AccountInfo::new(&key,false,true,&mut funds,&mut data,&owner,false,0);
    assert!(plan_fresh_program_pda(&a,&id,&key,192)==Err(PoolV1ProgramError::InvalidFreshAccount.into()));
    drop(a);assert!(data==original && funds==old);
}
#[kani::proof]
#[kani::unwind(195)]
fn PoolW_fresh_program_zero() {
    let id=Pubkey::new_from_array([7;32]);let key=Pubkey::new_from_array([9;32]);
    let mut data=[0u8;192];let mut funds:u64=kani::any();let old=funds;
    let a=AccountInfo::new(&key,false,true,&mut funds,&mut data,&id,false,0);
    assert!(plan_fresh_program_pda(&a,&id,&key,192)==Ok(FreshPdaPreparationV1::ProgramOwnedZeroed));
    drop(a);assert!(data==[0u8;192] && funds==old);
}
#[kani::proof]
#[kani::unwind(195)]
fn PoolW_fresh_program_occupied() {
    let id=Pubkey::new_from_array([7;32]);let key=Pubkey::new_from_array([9;32]);
    let mut data:[u8;192]=kani::any();kani::assume(data[0]!=0);let original=data;let mut funds:u64=kani::any();let old=funds;
    let a=AccountInfo::new(&key,false,true,&mut funds,&mut data,&id,false,0);
    assert!(plan_fresh_program_pda(&a,&id,&key,192)==Err(PoolV1ProgramError::InvalidFreshAccount.into()));
    drop(a);assert!(data==original && funds==old);
}

#[kani::proof]
fn PoolW_fresh_metadata_error() {
    let id=Pubkey::new_from_array([7;32]);let key=Pubkey::new_from_array([9;32]);let wrong=Pubkey::new_from_array([10;32]);
    let same:bool=kani::any();let executable:bool=kani::any();let signer:bool=kani::any();let writable:bool=kani::any();
    kani::assume(!same || executable || signer || !writable);
    let expected=if same {key} else {wrong};let owner=Pubkey::new_from_array(kani::any());
    let mut data:[u8;192]=kani::any();let original=data;let mut funds:u64=kani::any();let old=funds;
    let a=AccountInfo::new(&key,signer,writable,&mut funds,&mut data,&owner,executable,0);
    assert!(plan_fresh_program_pda(&a,&id,&expected,192)==Err(PoolV1ProgramError::InvalidFreshAccount.into()));
    drop(a);assert!(data==original && funds==old);
}
#[kani::proof]
fn PoolW_fresh_program_wrong_size() {
    let id=Pubkey::new_from_array([7;32]);let key=Pubkey::new_from_array([9;32]);
    let mut data:[u8;193]=kani::any();let original=data;let mut funds:u64=kani::any();let old=funds;
    let a=AccountInfo::new(&key,false,true,&mut funds,&mut data,&id,false,0);
    assert!(plan_fresh_program_pda(&a,&id,&key,192)==Err(PoolV1ProgramError::InvalidFreshAccount.into()));
    drop(a);assert!(data==original && funds==old);
}
#[kani::proof]
fn PoolW_fresh_foreign_owner() {
    let id=Pubkey::new_from_array([7;32]);let key=Pubkey::new_from_array([9;32]);let owner=Pubkey::new_from_array([8;32]);
    let mut data=[];let mut funds:u64=kani::any();let old=funds;
    let a=AccountInfo::new(&key,false,true,&mut funds,&mut data,&owner,false,0);
    assert!(plan_fresh_program_pda(&a,&id,&key,192)==Err(PoolV1ProgramError::InvalidFreshAccount.into()));
    drop(a);assert!(funds==old);
}
#[kani::proof]
#[kani::unwind(80)]
fn PoolW_zero_borrow_tiny() {
    let id=Pubkey::new_from_array([7;32]);let key=Pubkey::new_from_array([9;32]);
    let mut data=[];let mut funds=1;
    let a=AccountInfo::new(&key,false,true,&mut funds,&mut data,&id,false,0);
    let held=a.try_borrow_mut_data().unwrap();
    assert!(require_program_owned_zeroed(&a,&id,192,&Rent::default())==Err(ProgramError::AccountBorrowFailed));
    drop(held);drop(a);assert!(funds==1);
}
#[kani::proof]
#[kani::unwind(80)]
fn PoolW_copy_master_borrow_tiny() {
    let id=Pubkey::new_from_array([7;32]);let mk=Pubkey::new_from_array([8;32]);let ck=Pubkey::new_from_array([9;32]);
    let mut m=[0u8;1];let mut c=[0u8;1];let mut ml=1;let mut cl=2;
    let plan=PoolW_Planned{checkpoint_image:[65u8;192],next_master_image:[42u8;384]};
    let master=AccountInfo::new(&mk,false,true,&mut ml,&mut m,&id,false,0);
    let checkpoint=AccountInfo::new(&ck,false,true,&mut cl,&mut c,&id,false,0);
    let held=master.try_borrow_data().unwrap();
    assert!(PoolW_copy_tail(&master,&checkpoint,&plan)==Err(ProgramError::AccountBorrowFailed));
    drop(held);drop(master);drop(checkpoint);assert!(m==[0u8;1] && c==[0u8;1]);
}
