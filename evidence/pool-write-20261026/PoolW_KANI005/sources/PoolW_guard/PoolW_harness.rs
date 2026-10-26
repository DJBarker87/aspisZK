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
    assert!(require_program_owned_zeroed(&account,&id,192,&Rent::default())==Err(expected));
    assert!(PoolW_zero_reference(&account,&id,192,&Rent::default())==Err(expected));
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
