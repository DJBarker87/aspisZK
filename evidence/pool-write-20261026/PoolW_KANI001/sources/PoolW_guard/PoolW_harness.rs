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
