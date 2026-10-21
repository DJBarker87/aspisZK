#![allow(dead_code,unexpected_cfgs)]
use solana_program::{account_info::AccountInfo,pubkey::Pubkey,program_error::ProgramError};
use std::cell::Cell;
#[cfg(kani)]
#[kani::requires(counter==std::rc::Rc::as_ptr(&account.data).cast::<Cell<isize>>())]
#[kani::modifies(counter.cast::<isize>())]
#[kani::ensures(|_| unsafe{(*counter).get()}==old(unsafe{(*counter).get()}))]
fn exclusive_roundtrip(account:&AccountInfo<'_>,counter:*const Cell<isize>) {
 match account.try_borrow_mut_data() {
  Ok(guard)=>drop(guard),
  Err(error)=>assert!(matches!(error,ProgramError::AccountBorrowFailed)),
 }
}
#[cfg(kani)] mod proofs {
 use super::*;
 #[kani::proof_for_contract(exclusive_roundtrip)]
 #[kani::unwind(36)]
 fn actual_sdk_exclusive_write_frame() {
  let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());
  let flags:[bool;3]=kani::any();let rent_epoch:u64=kani::any();let mut lamports:u64=kani::any();
  let mut bytes:[u8;58295]=kani::any();let length:usize=kani::any();kani::assume(length<=58295);
  let account=AccountInfo::new(&key,flags[0],flags[1],&mut lamports,&mut bytes[..length],&owner,flags[2],rent_epoch);
  let counter=std::rc::Rc::as_ptr(&account.data).cast::<Cell<isize>>();
  assert_eq!(unsafe{(*counter).get()},0);
  let trial=account.try_borrow_data().unwrap();assert_eq!(unsafe{(*counter).get()},1);drop(trial);
  assert_eq!(unsafe{(*counter).get()},0);
  let initial:isize=kani::any();unsafe{(*counter).set(initial);}
  exclusive_roundtrip(&account,counter);
  assert_eq!(unsafe{(*counter).get()},initial);
  unsafe{(*counter).set(0);}
  kani::cover!(initial==0 && length==58295,"full proof view write-set checked");
  kani::cover!(initial==isize::MAX && length==0,"saturated empty view rejection checked");
 }
}
