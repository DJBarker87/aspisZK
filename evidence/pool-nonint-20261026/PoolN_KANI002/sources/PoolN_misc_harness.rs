
#[cfg(kani)]
mod PoolN_guards {
use super::*;
use solana_program::{account_info::AccountInfo,pubkey::Pubkey,program_error::ProgramError};
use crate::error::PoolV1ProgramError;

#[kani::proof]
#[kani::unwind(196)]
fn PoolN_root_page_192() {
let id=Pubkey::new_from_array([7;32]); let key=Pubkey::new_from_array([8;32]);
let foreign=Pubkey::new_from_array([6;32]);
let mut bytes: [u8;192]=kani::any(); let before=bytes;
let mut balance:u64=kani::any(); let original_balance=balance;
let account=AccountInfo::new(&key,false,true,&mut balance,&mut bytes,&id,false,0);
assert!(matches!(crate::history::validate_root_page_bytes(&account.try_borrow_data().unwrap(),&key,0),Err(e) if e==PoolV1ProgramError::InvalidAccountType.into()));
drop(account); assert!(bytes==before); assert!(balance==original_balance);
}

#[kani::proof]
#[kani::unwind(1772)]
fn PoolN_root_page_1768() {
let id=Pubkey::new_from_array([7;32]); let key=Pubkey::new_from_array([8;32]);
let foreign=Pubkey::new_from_array([6;32]);
let mut bytes: [u8;1768]=kani::any(); let before=bytes;
let mut balance:u64=kani::any(); let original_balance=balance;
let account=AccountInfo::new(&key,false,true,&mut balance,&mut bytes,&foreign,false,0);
assert!(matches!(crate::history::validate_root_page_bytes(&account.try_borrow_data().unwrap(),&key,0),Err(e) if e==PoolV1ProgramError::InvalidAccountType.into()));
drop(account); assert!(bytes==before); assert!(balance==original_balance);
}

#[kani::proof]
#[kani::unwind(196)]
fn PoolN_marker_192() {
let id=Pubkey::new_from_array([7;32]); let key=Pubkey::new_from_array([8;32]);
let foreign=Pubkey::new_from_array([6;32]);
let mut bytes: [u8;192]=kani::any(); let before=bytes;
let mut balance:u64=kani::any(); let original_balance=balance;
let account=AccountInfo::new(&key,false,true,&mut balance,&mut bytes,&id,false,0);
assert_eq!(crate::nullifier::recheck_pair_forest_nullifier_marker_v1(&id,&account),Err(PoolV1ProgramError::InvalidNullifierMarkerAccount.into()));
drop(account); assert!(bytes==before); assert!(balance==original_balance);
}

#[kani::proof]
#[kani::unwind(1772)]
fn PoolN_marker_1768() {
let id=Pubkey::new_from_array([7;32]); let key=Pubkey::new_from_array([8;32]);
let foreign=Pubkey::new_from_array([6;32]);
let mut bytes: [u8;1768]=kani::any(); let before=bytes;
let mut balance:u64=kani::any(); let original_balance=balance;
let account=AccountInfo::new(&key,false,true,&mut balance,&mut bytes,&foreign,false,0);
assert_eq!(crate::nullifier::recheck_pair_forest_nullifier_marker_v1(&id,&account),Err(PoolV1ProgramError::InvalidNullifierMarkerAccount.into()));
drop(account); assert!(bytes==before); assert!(balance==original_balance);
}

#[kani::proof]
#[kani::unwind(196)]
fn PoolN_token_parsers_192() {
let id=Pubkey::new_from_array([7;32]); let key=Pubkey::new_from_array([8;32]);
let foreign=Pubkey::new_from_array([6;32]);
let mut bytes: [u8;192]=kani::any(); let before=bytes;
let mut balance:u64=kani::any(); let original_balance=balance;
let account=AccountInfo::new(&key,false,true,&mut balance,&mut bytes,&id,false,0);
let data=account.try_borrow_data().unwrap();
assert!(matches!(crate::vault::parse_legacy_mint_v1(&data),Err(e) if e==PoolV1ProgramError::UnsupportedTokenConfiguration.into()));
assert!(matches!(crate::vault::parse_legacy_token_account_v1(&data),Err(e) if e==PoolV1ProgramError::UnsupportedTokenConfiguration.into()));
drop(account); assert!(bytes==before); assert!(balance==original_balance);
}

#[kani::proof]
#[kani::unwind(1772)]
fn PoolN_token_parsers_1768() {
let id=Pubkey::new_from_array([7;32]); let key=Pubkey::new_from_array([8;32]);
let foreign=Pubkey::new_from_array([6;32]);
let mut bytes: [u8;1768]=kani::any(); let before=bytes;
let mut balance:u64=kani::any(); let original_balance=balance;
let account=AccountInfo::new(&key,false,true,&mut balance,&mut bytes,&foreign,false,0);
let data=account.try_borrow_data().unwrap();
assert!(matches!(crate::vault::parse_legacy_mint_v1(&data),Err(e) if e==PoolV1ProgramError::UnsupportedTokenConfiguration.into()));
assert!(matches!(crate::vault::parse_legacy_token_account_v1(&data),Err(e) if e==PoolV1ProgramError::UnsupportedTokenConfiguration.into()));
drop(account); assert!(bytes==before); assert!(balance==original_balance);
}

#[kani::proof]
#[kani::unwind(196)]
fn PoolN_lane_codec_192() {
let id=Pubkey::new_from_array([7;32]); let key=Pubkey::new_from_array([8;32]);
let foreign=Pubkey::new_from_array([6;32]);
let mut bytes: [u8;192]=kani::any(); let before=bytes;
let mut balance:u64=kani::any(); let original_balance=balance;
let account=AccountInfo::new(&key,false,true,&mut balance,&mut bytes,&id,false,0);
assert!(aspis_statement::pool_v1::decode_pool_v1_pair_forest_lane_state_v1(&account.try_borrow_data().unwrap(),&crate::empty_roots::POOL_V1_PAIR_EMPTY_ROOTS).is_err());
drop(account); assert!(bytes==before); assert!(balance==original_balance);
}

#[kani::proof]
#[kani::unwind(1772)]
fn PoolN_lane_codec_1768() {
let id=Pubkey::new_from_array([7;32]); let key=Pubkey::new_from_array([8;32]);
let foreign=Pubkey::new_from_array([6;32]);
let mut bytes: [u8;1768]=kani::any(); let before=bytes;
let mut balance:u64=kani::any(); let original_balance=balance;
let account=AccountInfo::new(&key,false,true,&mut balance,&mut bytes,&foreign,false,0);
assert!(aspis_statement::pool_v1::decode_pool_v1_pair_forest_lane_state_v1(&account.try_borrow_data().unwrap(),&crate::empty_roots::POOL_V1_PAIR_EMPTY_ROOTS).is_err());
drop(account); assert!(bytes==before); assert!(balance==original_balance);
}

}
