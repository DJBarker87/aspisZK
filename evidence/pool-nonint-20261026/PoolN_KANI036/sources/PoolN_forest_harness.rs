
#[cfg(kani)]
mod PoolN_guards {
use super::*;

#[kani::proof]
#[kani::unwind(196)]
fn PoolN_master_192() {
let id=Pubkey::new_from_array([7;32]); let key=Pubkey::new_from_array([8;32]);
let foreign=Pubkey::new_from_array([6;32]);
let mut bytes: [u8;192]=kani::any(); let probe:usize=kani::any(); kani::assume(probe<bytes.len()); let before=bytes[probe];
let mut balance:u64=kani::any(); let original_balance=balance;
let account=AccountInfo::new(&key,false,true,&mut balance,&mut bytes,&id,false,0);
let result=decode_master_account(&id,&account,true); assert!(matches!(result,Err(e) if e==PoolV1ProgramError::InvalidAccountType.into()));
drop(account); assert!(bytes[probe]==before); assert!(balance==original_balance);
}

#[kani::proof]
#[kani::unwind(1772)]
fn PoolN_master_1768() {
let id=Pubkey::new_from_array([7;32]); let key=Pubkey::new_from_array([8;32]);
let foreign=Pubkey::new_from_array([6;32]);
let mut bytes: [u8;1768]=kani::any(); let probe:usize=kani::any(); kani::assume(probe<bytes.len()); let before=bytes[probe];
let mut balance:u64=kani::any(); let original_balance=balance;
let account=AccountInfo::new(&key,false,true,&mut balance,&mut bytes,&foreign,false,0);
let result=decode_master_account(&id,&account,true); assert!(matches!(result,Err(e) if e==ProgramError::IncorrectProgramId));
drop(account); assert!(bytes[probe]==before); assert!(balance==original_balance);
}

#[kani::proof]
#[kani::unwind(196)]
fn PoolN_stored_lane_192() {
let id=Pubkey::new_from_array([7;32]); let key=Pubkey::new_from_array([8;32]);
let foreign=Pubkey::new_from_array([6;32]);
let mut bytes: [u8;192]=kani::any(); let probe:usize=kani::any(); kani::assume(probe<bytes.len()); let before=bytes[probe];
let mut balance:u64=kani::any(); let original_balance=balance;
let account=AccountInfo::new(&key,false,true,&mut balance,&mut bytes,&id,false,0);
assert_eq!(stored_lane_bump(&account),Ok(None));
drop(account); assert!(bytes[probe]==before); assert!(balance==original_balance);
}

#[kani::proof]
#[kani::unwind(1772)]
fn PoolN_stored_lane_1768() {
let id=Pubkey::new_from_array([7;32]); let key=Pubkey::new_from_array([8;32]);
let foreign=Pubkey::new_from_array([6;32]);
let mut bytes: [u8;1768]=kani::any(); let probe:usize=kani::any(); kani::assume(probe<bytes.len()); let before=bytes[probe];
let mut balance:u64=kani::any(); let original_balance=balance;
let account=AccountInfo::new(&key,false,true,&mut balance,&mut bytes,&foreign,false,0);
assert_eq!(stored_lane_bump(&account),Ok(None));
drop(account); assert!(bytes[probe]==before); assert!(balance==original_balance);
}

#[kani::proof]
#[kani::unwind(196)]
fn PoolN_zero_page_192() {
let id=Pubkey::new_from_array([7;32]); let key=Pubkey::new_from_array([8;32]);
let foreign=Pubkey::new_from_array([6;32]);
let mut bytes: [u8;192]=kani::any(); let probe:usize=kani::any(); kani::assume(probe<bytes.len()); let before=bytes[probe];
let mut balance:u64=kani::any(); let original_balance=balance;
let account=AccountInfo::new(&key,false,true,&mut balance,&mut bytes,&id,false,0);
assert_eq!(account_is_zeroed_program_page(&account,&id),Ok(false));
drop(account); assert!(bytes[probe]==before); assert!(balance==original_balance);
}

#[kani::proof]
#[kani::unwind(1772)]
fn PoolN_zero_page_1768() {
let id=Pubkey::new_from_array([7;32]); let key=Pubkey::new_from_array([8;32]);
let foreign=Pubkey::new_from_array([6;32]);
let mut bytes: [u8;1768]=kani::any(); let probe:usize=kani::any(); kani::assume(probe<bytes.len()); let before=bytes[probe];
let mut balance:u64=kani::any(); let original_balance=balance;
let account=AccountInfo::new(&key,false,true,&mut balance,&mut bytes,&foreign,false,0);
assert_eq!(account_is_zeroed_program_page(&account,&id),Ok(false));
drop(account); assert!(bytes[probe]==before); assert!(balance==original_balance);
}

#[kani::proof]
#[kani::unwind(196)]
fn PoolN_zero_owned_192() {
let id=Pubkey::new_from_array([7;32]); let key=Pubkey::new_from_array([8;32]);
let foreign=Pubkey::new_from_array([6;32]);
let mut bytes: [u8;192]=kani::any(); let probe:usize=kani::any(); kani::assume(probe<bytes.len()); let before=bytes[probe];
let mut balance:u64=kani::any(); let original_balance=balance;
let account=AccountInfo::new(&key,false,true,&mut balance,&mut bytes,&id,false,0);
assert_eq!(require_program_owned_zeroed(&account,&id,768,&Rent::default()),Err(PoolV1ProgramError::InvalidFreshAccount.into()));
drop(account); assert!(bytes[probe]==before); assert!(balance==original_balance);
}

#[kani::proof]
#[kani::unwind(1772)]
fn PoolN_zero_owned_1768() {
let id=Pubkey::new_from_array([7;32]); let key=Pubkey::new_from_array([8;32]);
let foreign=Pubkey::new_from_array([6;32]);
let mut bytes: [u8;1768]=kani::any(); let probe:usize=kani::any(); kani::assume(probe<bytes.len()); let before=bytes[probe];
let mut balance:u64=kani::any(); let original_balance=balance;
let account=AccountInfo::new(&key,false,true,&mut balance,&mut bytes,&foreign,false,0);
assert_eq!(require_program_owned_zeroed(&account,&id,768,&Rent::default()),Err(ProgramError::IncorrectProgramId));
drop(account); assert!(bytes[probe]==before); assert!(balance==original_balance);
}

}
