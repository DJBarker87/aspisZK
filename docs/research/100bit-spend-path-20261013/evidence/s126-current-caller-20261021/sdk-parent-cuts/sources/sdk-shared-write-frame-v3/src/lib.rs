#![allow(dead_code,unexpected_cfgs)]
use solana_program::{account_info::AccountInfo,pubkey::Pubkey,program_error::ProgramError};
use std::cell::Cell;
#[cfg(kani)]
#[kani::requires(counter==std::rc::Rc::as_ptr(&account.data).cast::<Cell<isize>>())]
#[kani::modifies(counter.cast::<isize>())]
#[kani::ensures(|_| unsafe{(*counter).get()}==old(unsafe{(*counter).get()}))]
fn shared_roundtrip(account:&AccountInfo<'_>,counter:*const Cell<isize>) {
 match account.try_borrow_data() {
  Ok(guard)=>drop(guard),
  Err(error)=>assert!(matches!(error,ProgramError::AccountBorrowFailed)),
 }
}
#[cfg(kani)] mod proofs {
 use super::*;
 #[kani::proof_for_contract(shared_roundtrip)]
 #[kani::unwind(36)]
 fn actual_sdk_shared_write_frame() {
  let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());
  let flags:[bool;3]=kani::any();let rent_epoch:u64=kani::any();let mut lamports:u64=kani::any();
  let mut bytes:[u8;10485760]=kani::any();let length:usize=kani::any();kani::assume(length<=10485760);
  let account=AccountInfo::new(&key,flags[0],flags[1],&mut lamports,&mut bytes[..length],&owner,flags[2],rent_epoch);
  // The pinned RcInner header is validated before logical-count injection.
  let data_value=std::rc::Rc::as_ptr(&account.data).cast::<usize>();
  let lamport_value=std::rc::Rc::as_ptr(&account.lamports).cast::<usize>();
  let ds=unsafe{data_value.sub(2).cast_mut()};let dw=unsafe{data_value.sub(1).cast_mut()};
  let ls=unsafe{lamport_value.sub(2).cast_mut()};let lw=unsafe{lamport_value.sub(1).cast_mut()};
  assert_eq!(unsafe{*ds},1);assert_eq!(unsafe{*dw},1);assert_eq!(unsafe{*ls},1);assert_eq!(unsafe{*lw},1);
  let rc_counts:[usize;4]=kani::any();
  for count in rc_counts {kani::assume(count>=1 && count<=isize::MAX as usize);}
  unsafe{*ds=rc_counts[0];*dw=rc_counts[1];*ls=rc_counts[2];*lw=rc_counts[3];}
  assert_eq!(std::rc::Rc::strong_count(&account.data),rc_counts[0]);
  assert_eq!(std::rc::Rc::weak_count(&account.data),rc_counts[1]-1);
  assert_eq!(std::rc::Rc::strong_count(&account.lamports),rc_counts[2]);
  assert_eq!(std::rc::Rc::weak_count(&account.lamports),rc_counts[3]-1);
  let counter=std::rc::Rc::as_ptr(&account.data).cast::<Cell<isize>>();
  assert_eq!(unsafe{(*counter).get()},0);
  let trial=account.try_borrow_data().unwrap();assert_eq!(unsafe{(*counter).get()},1);drop(trial);
  assert_eq!(unsafe{(*counter).get()},0);
  let lamport_counter=std::rc::Rc::as_ptr(&account.lamports).cast::<Cell<isize>>();
  assert_eq!(unsafe{(*lamport_counter).get()},0);
  let initial_lamport:isize=kani::any();unsafe{(*lamport_counter).set(initial_lamport);}
  let initial:isize=kani::any();unsafe{(*counter).set(initial);}
  shared_roundtrip(&account,counter);
  assert_eq!(unsafe{(*counter).get()},initial);
  assert_eq!(std::rc::Rc::strong_count(&account.data),rc_counts[0]);
  assert_eq!(std::rc::Rc::weak_count(&account.data),rc_counts[1]-1);
  assert_eq!(std::rc::Rc::strong_count(&account.lamports),rc_counts[2]);
  assert_eq!(std::rc::Rc::weak_count(&account.lamports),rc_counts[3]-1);
  assert_eq!(unsafe{(*lamport_counter).get()},initial_lamport);
  unsafe{(*lamport_counter).set(0);}
  unsafe{(*counter).set(0);*ds=1;*dw=1;*ls=1;*lw=1;}
  kani::cover!(initial==0 && length==10485760,"maximum buffer view write-set checked");
  kani::cover!(initial==isize::MAX && length==0,"saturated empty view rejection checked");
 }
}
