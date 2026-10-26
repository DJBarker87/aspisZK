
#[cfg(kani)]
mod PoolN_splits {
use super::*;

#[kani::proof]
#[kani::unwind(196)]
fn PoolN_canonical_192() {
let id=Pubkey::new_from_array([7;32]);let foreign=Pubkey::new_from_array([6;32]);let key=Pubkey::new_from_array(kani::any());
let mut bytes:[u8;192]=kani::any();let before=bytes[0];let mut balance:u64=kani::any();let initial_balance=balance;
let account=AccountInfo::new(&key,false,true,&mut balance,&mut bytes,&id,false,0);
assert!(matches!(load_canonical_pool_state(&id,&account),Err(e) if e==PoolV1ProgramError::InvalidAccountType.into()));
drop(account);assert!(bytes[0]==before);assert_eq!(balance,initial_balance);
}

#[kani::proof]
#[kani::unwind(1772)]
fn PoolN_canonical_1768() {
let id=Pubkey::new_from_array([7;32]);let foreign=Pubkey::new_from_array([6;32]);let key=Pubkey::new_from_array(kani::any());
let mut bytes:[u8;1768]=kani::any();let before=bytes[0];let mut balance:u64=kani::any();let initial_balance=balance;
let account=AccountInfo::new(&key,false,true,&mut balance,&mut bytes,&foreign,false,0);
assert!(matches!(load_canonical_pool_state(&id,&account),Err(e) if e==ProgramError::IncorrectProgramId));
drop(account);assert!(bytes[0]==before);assert_eq!(balance,initial_balance);
}

#[kani::proof]
#[kani::unwind(196)]
fn PoolN_invariant_192() {
let id=Pubkey::new_from_array([7;32]);let foreign=Pubkey::new_from_array([6;32]);let key=Pubkey::new_from_array(kani::any());
let mut bytes:[u8;192]=kani::any();let before=bytes[0];let mut balance:u64=kani::any();let initial_balance=balance;
let account=AccountInfo::new(&key,false,true,&mut balance,&mut bytes,&id,false,0);
assert!(matches!(CanonicalPoolStateV1::decode_account_from_program_invariant(&id,&account),Err(e) if e==PoolV1ProgramError::InvalidAccountType.into()));
drop(account);assert!(bytes[0]==before);assert_eq!(balance,initial_balance);
}

#[kani::proof]
#[kani::unwind(1772)]
fn PoolN_invariant_1768() {
let id=Pubkey::new_from_array([7;32]);let foreign=Pubkey::new_from_array([6;32]);let key=Pubkey::new_from_array(kani::any());
let mut bytes:[u8;1768]=kani::any();let before=bytes[0];let mut balance:u64=kani::any();let initial_balance=balance;
let account=AccountInfo::new(&key,false,true,&mut balance,&mut bytes,&foreign,false,0);
assert!(matches!(CanonicalPoolStateV1::decode_account_from_program_invariant(&id,&account),Err(e) if e==ProgramError::IncorrectProgramId));
drop(account);assert!(bytes[0]==before);assert_eq!(balance,initial_balance);
}

#[kani::proof]
#[kani::unwind(196)]
fn PoolN_fresh_flags_192() {
let id=Pubkey::new_from_array([7;32]);let foreign=Pubkey::new_from_array([6;32]);let key=Pubkey::new_from_array(kani::any());
let mut bytes:[u8;192]=kani::any();let before=bytes[0];let mut balance:u64=kani::any();let initial_balance=balance;
let account=AccountInfo::new(&key,kani::any(),kani::any(),&mut balance,&mut bytes,&id,false,0);
let sizes=[384usize,768,1000,8256,10000,8504];let i:usize=kani::any();kani::assume(i<6);
assert_eq!(plan_fresh_program_pda(&account,&id,&key,sizes[i]),Err(PoolV1ProgramError::InvalidFreshAccount.into()));
kani::cover!(account.is_signer && account.is_writable,"signer cannot bypass freshness");
drop(account);assert!(bytes[0]==before);assert_eq!(balance,initial_balance);
}

#[kani::proof]
#[kani::unwind(1772)]
fn PoolN_fresh_flags_1768() {
let id=Pubkey::new_from_array([7;32]);let foreign=Pubkey::new_from_array([6;32]);let key=Pubkey::new_from_array(kani::any());
let mut bytes:[u8;1768]=kani::any();let before=bytes[0];let mut balance:u64=kani::any();let initial_balance=balance;
let account=AccountInfo::new(&key,kani::any(),kani::any(),&mut balance,&mut bytes,&foreign,false,0);
let sizes=[384usize,768,1000,8256,10000,8504];let i:usize=kani::any();kani::assume(i<6);
assert_eq!(plan_fresh_program_pda(&account,&id,&key,sizes[i]),Err(PoolV1ProgramError::InvalidFreshAccount.into()));
kani::cover!(account.is_signer && account.is_writable,"signer cannot bypass freshness");
drop(account);assert!(bytes[0]==before);assert_eq!(balance,initial_balance);
}

#[kani::proof]
#[kani::unwind(196)]
fn PoolN_payer_flags_192() {
let id=Pubkey::new_from_array([7;32]);let foreign=Pubkey::new_from_array([6;32]);let key=Pubkey::new_from_array(kani::any());
let mut bytes:[u8;192]=kani::any();let before=bytes[0];let mut balance:u64=kani::any();let initial_balance=balance;
let account=AccountInfo::new(&key,kani::any(),kani::any(),&mut balance,&mut bytes,&id,false,0);
let system_key=system_program::id();let loader=native_loader::id();let mut sysbal=1;let mut sysdata=[];
let system=AccountInfo::new(&system_key,false,false,&mut sysbal,&mut sysdata,&loader,true,0);
assert_eq!(require_payer_and_system_program(&account,&system),Err(PoolV1ProgramError::InvalidPayer.into()));
kani::cover!(account.is_signer && account.is_writable,"owner rejection reached with signer payer flags");
drop(account);assert!(bytes[0]==before);assert_eq!(balance,initial_balance);
}

#[kani::proof]
#[kani::unwind(1772)]
fn PoolN_payer_flags_1768() {
let id=Pubkey::new_from_array([7;32]);let foreign=Pubkey::new_from_array([6;32]);let key=Pubkey::new_from_array(kani::any());
let mut bytes:[u8;1768]=kani::any();let before=bytes[0];let mut balance:u64=kani::any();let initial_balance=balance;
let account=AccountInfo::new(&key,kani::any(),kani::any(),&mut balance,&mut bytes,&foreign,false,0);
let system_key=system_program::id();let loader=native_loader::id();let mut sysbal=1;let mut sysdata=[];
let system=AccountInfo::new(&system_key,false,false,&mut sysbal,&mut sysdata,&loader,true,0);
assert_eq!(require_payer_and_system_program(&account,&system),Err(PoolV1ProgramError::InvalidPayer.into()));
kani::cover!(account.is_signer && account.is_writable,"owner rejection reached with signer payer flags");
drop(account);assert!(bytes[0]==before);assert_eq!(balance,initial_balance);
}

#[kani::proof]
#[kani::unwind(196)]
fn PoolN_marker_flags_192() {
let id=Pubkey::new_from_array([7;32]);let foreign=Pubkey::new_from_array([6;32]);let key=Pubkey::new_from_array(kani::any());
let mut bytes:[u8;192]=kani::any();let before=bytes[0];let mut balance:u64=kani::any();let initial_balance=balance;
let account=AccountInfo::new(&key,kani::any(),kani::any(),&mut balance,&mut bytes,&id,false,0);
assert_eq!(crate::nullifier::recheck_pair_forest_nullifier_marker_v1(&id,&account),Err(PoolV1ProgramError::InvalidNullifierMarkerAccount.into()));
drop(account);assert!(bytes[0]==before);assert_eq!(balance,initial_balance);
}

#[kani::proof]
#[kani::unwind(1772)]
fn PoolN_marker_flags_1768() {
let id=Pubkey::new_from_array([7;32]);let foreign=Pubkey::new_from_array([6;32]);let key=Pubkey::new_from_array(kani::any());
let mut bytes:[u8;1768]=kani::any();let before=bytes[0];let mut balance:u64=kani::any();let initial_balance=balance;
let account=AccountInfo::new(&key,kani::any(),kani::any(),&mut balance,&mut bytes,&foreign,false,0);
assert_eq!(crate::nullifier::recheck_pair_forest_nullifier_marker_v1(&id,&account),Err(PoolV1ProgramError::InvalidNullifierMarkerAccount.into()));
drop(account);assert!(bytes[0]==before);assert_eq!(balance,initial_balance);
}

#[kani::proof]
#[kani::unwind(196)]
fn PoolN_plan_flags_192() {
let id=Pubkey::new_from_array([7;32]);let foreign=Pubkey::new_from_array([6;32]);let key=Pubkey::new_from_array(kani::any());
let mut bytes:[u8;192]=kani::any();let before=bytes[0];let mut balance:u64=kani::any();let initial_balance=balance;
let account=AccountInfo::new(&key,kani::any(),kani::any(),&mut balance,&mut bytes,&id,false,0);
let size=if kani::any(){POOL_V1_PREPARED_SETTLEMENT_CORE_ACCOUNT_BYTES}else{POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_ACCOUNT_BYTES};
assert_eq!(require_prepared_plan_account_v1(&account,&id,size),Err(ProgramError::InvalidAccountData));
drop(account);assert!(bytes[0]==before);assert_eq!(balance,initial_balance);
}

#[kani::proof]
#[kani::unwind(1772)]
fn PoolN_plan_flags_1768() {
let id=Pubkey::new_from_array([7;32]);let foreign=Pubkey::new_from_array([6;32]);let key=Pubkey::new_from_array(kani::any());
let mut bytes:[u8;1768]=kani::any();let before=bytes[0];let mut balance:u64=kani::any();let initial_balance=balance;
let account=AccountInfo::new(&key,kani::any(),kani::any(),&mut balance,&mut bytes,&foreign,false,0);
let size=if kani::any(){POOL_V1_PREPARED_SETTLEMENT_CORE_ACCOUNT_BYTES}else{POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_ACCOUNT_BYTES};
assert_eq!(require_prepared_plan_account_v1(&account,&id,size),Err(ProgramError::InvalidAccountData));
drop(account);assert!(bytes[0]==before);assert_eq!(balance,initial_balance);
}
}
