#![cfg(kani)]
#![allow(dead_code, non_snake_case)]
use solana_account_info::AccountInfo;
use solana_pubkey::Pubkey;
use solana_program_error::ProgramError;

struct OwnedAccount {
    key: Pubkey,
    owner: Pubkey,
    is_signer: bool,
    is_writable: bool,
    executable: bool,
    length: Result<usize, ProgramError>,
    bytes: Result<Vec<u8>, ProgramError>,
}
impl OwnedAccount {
    fn key(&self) -> &Pubkey { &self.key }
    fn owner(&self) -> &Pubkey { &self.owner }
    fn data(&self) -> Result<&[u8], ProgramError> {
        match &self.bytes { Ok(bytes) => Ok(bytes), Err(error) => Err(error.clone()) }
    }
    fn data_len(&self) -> Result<usize, ProgramError> { self.length.clone() }
}

// Copy only decoder-admitted lengths; malformed lengths retain their original
// length and a deferred error. No adversarial account length drives allocation.
fn snapshot(account: &AccountInfo<'_>, length1: usize, length2: usize) -> OwnedAccount {
    let (length, bytes) = match account.try_borrow_data() {
        Ok(data) => {
            let length = data.len();
            let bytes = if length == length1 || length == length2 {
                Ok(data.to_vec())
            } else { Err(ProgramError::InvalidAccountData) };
            (Ok(length), bytes)
        }
        Err(error) => (Err(error.clone()), Err(error)),
    };
    OwnedAccount { key: *account.key, owner: *account.owner,
        is_signer: account.is_signer, is_writable: account.is_writable,
        executable: account.executable, length, bytes }
}


#[kani::proof]
#[kani::unwind(3)]
fn S2W_snapshot_proof_account() {
    let mut input: [u8; 58295] = kani::any();
    let i: usize = kani::any();
    kani::assume(i < input.len());
    let original = input[i];
    let key = Pubkey::new_from_array(kani::any());
    let owner = Pubkey::new_from_array(kani::any());
    let signer: bool = kani::any();
    let writable: bool = kani::any();
    let executable: bool = kani::any();
    let mut lamports: u64 = kani::any();
    let old_lamports = lamports;
    let epoch: u64 = kani::any();
    let account = AccountInfo::new(&key, signer, writable, &mut lamports,
        &mut input, &owner, executable, epoch);
    let snap = snapshot(&account, 58295, 58295);
    assert!(snap.key == key && snap.owner == owner);
    assert!(snap.is_signer == signer && snap.is_writable == writable
        && snap.executable == executable);
    assert!(snap.length == Ok(58295));
    let copied = snap.bytes.unwrap();
    assert!(copied.len() == 58295);
    assert!(copied[i] == original);
    assert!(**account.try_borrow_lamports().unwrap() == old_lamports);
    let mut live = account.try_borrow_mut_data().unwrap();
    assert!(live.len() == 58295 && live[i] == original);
    live[i] = original.wrapping_add(1);
    assert!(copied[i] == original);
}
