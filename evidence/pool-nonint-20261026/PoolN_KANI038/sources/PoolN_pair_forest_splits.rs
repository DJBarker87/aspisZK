
#[cfg(kani)]
mod PoolN_splits {
use super::*;

#[kani::proof]
#[kani::unwind(196)]
fn PoolN_master_readonly_192() {
let id=Pubkey::new_from_array([7;32]);let foreign=Pubkey::new_from_array([6;32]);let key=Pubkey::new_from_array(kani::any());
let mut bytes:[u8;192]=kani::any();let before=bytes[0];let mut balance:u64=kani::any();let initial_balance=balance;
let account=AccountInfo::new(&key,false,false,&mut balance,&mut bytes,&id,false,0);
assert!(matches!(decode_master_account(&id,&account,false),Err(e) if e==PoolV1ProgramError::InvalidAccountType.into()));
drop(account);assert!(bytes[0]==before);assert_eq!(balance,initial_balance);
}

#[kani::proof]
#[kani::unwind(1772)]
fn PoolN_master_readonly_1768() {
let id=Pubkey::new_from_array([7;32]);let foreign=Pubkey::new_from_array([6;32]);let key=Pubkey::new_from_array(kani::any());
let mut bytes:[u8;1768]=kani::any();let before=bytes[0];let mut balance:u64=kani::any();let initial_balance=balance;
let account=AccountInfo::new(&key,false,false,&mut balance,&mut bytes,&foreign,false,0);
assert!(matches!(decode_master_account(&id,&account,false),Err(e) if e==ProgramError::IncorrectProgramId));
drop(account);assert!(bytes[0]==before);assert_eq!(balance,initial_balance);
}
}
