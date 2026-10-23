#![allow(dead_code,unexpected_cfgs)]
use solana_program::{account_info::AccountInfo,pubkey::Pubkey,program_error::ProgramError};
#[cfg(kani)] mod proofs {
 use super::*;
 #[kani::proof]
 #[kani::unwind(3)]
 fn shared_alias_exact_view() {
  let key=Pubkey::new_from_array([1;32]);let owner=Pubkey::new_from_array([2;32]);
  let mut lamports=0;let mut storage:[u8;58295]=kani::any();
  let length:usize=kani::any();kani::assume(length<=58295);
  let original=AccountInfo::new(&key,false,false,&mut lamports,&mut storage[..length],&owner,false,0);
  let alias=original.clone();
  let first=original.try_borrow_data().unwrap();let second=alias.try_borrow_data().unwrap();
  assert_eq!(first.len(),second.len());assert_eq!(first.as_ptr(),second.as_ptr());
  assert!(first.len()!=1880 || second.len()!=58295);
  if length>0 {let selected:usize=kani::any();kani::assume(selected<length);assert_eq!(first[selected],second[selected]);}
  drop(second);drop(first);assert!(alias.try_borrow_mut_data().is_ok());
  kani::cover!(length==1880,"public sized alias");kani::cover!(length==58295,"proof sized alias");
 }
 #[kani::proof]
 #[kani::unwind(3)]
 fn exclusive_guard_blocks_alias() {
  let key=Pubkey::new_from_array([1;32]);let owner=Pubkey::new_from_array([2;32]);
  let mut lamports=0;let mut storage:[u8;58295]=kani::any();
  let length:usize=kani::any();kani::assume(length<=58295);
  let original=AccountInfo::new(&key,false,true,&mut lamports,&mut storage[..length],&owner,false,0);
  let alias=original.clone();
  let guard=original.try_borrow_mut_data().unwrap();
  assert!(matches!(alias.try_borrow_data(),Err(ProgramError::AccountBorrowFailed)));
  assert!(matches!(alias.try_borrow_mut_data(),Err(ProgramError::AccountBorrowFailed)));
  assert_eq!(guard.len(),length);
  drop(guard);assert!(alias.try_borrow_mut_data().is_ok());
  kani::cover!(length==1768,"live checkpoint guard");
 }

}
