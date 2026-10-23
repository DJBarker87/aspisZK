#![allow(dead_code,unexpected_cfgs)]
use solana_program::{account_info::AccountInfo,pubkey::Pubkey,program_error::ProgramError};
#[cfg(kani)] mod proofs {
 use super::*;
 #[kani::proof]
 #[kani::unwind(3)]
 fn actual_sdk_all_borrow_counts() {
  let key=Pubkey::new_from_array([1;32]);let owner=Pubkey::new_from_array([2;32]);
  let mut lamports=0;let mut bytes:[u8;1768]=kani::any();
  let length:usize=kani::any();kani::assume(length<=1768);
  let account=AccountInfo::new(&key,false,true,&mut lamports,&mut bytes[..length],&owner,false,0);
  // RefCell has a potentially-unsized value tail; confirm the actual pinned
  // compiler/SDK counter location by its public borrow transitions first.
  let counter=std::rc::Rc::as_ptr(&account.data).cast::<std::cell::Cell<isize>>();
  assert_eq!(unsafe{(*counter).get()},0);
  let trial=account.try_borrow_data().unwrap();assert_eq!(unsafe{(*counter).get()},1);
  drop(trial);assert_eq!(unsafe{(*counter).get()},0);
  let trial=account.try_borrow_mut_data().unwrap();assert_eq!(unsafe{(*counter).get()},-1);
  drop(trial);assert_eq!(unsafe{(*counter).get()},0);
  let initial:isize=kani::any();unsafe{(*counter).set(initial);}
  let read_ok=initial>=0 && initial<isize::MAX;
  match account.try_borrow_data() {
   Ok(guard)=>{assert!(read_ok);assert_eq!(guard.len(),length);assert_eq!(unsafe{(*counter).get()},initial+1);drop(guard);},
   Err(error)=>{assert!(!read_ok);assert!(matches!(error,ProgramError::AccountBorrowFailed));},
  }
  assert_eq!(unsafe{(*counter).get()},initial);
  match account.try_borrow_mut_data() {
   Ok(guard)=>{assert_eq!(initial,0);assert_eq!(guard.len(),length);assert_eq!(unsafe{(*counter).get()},-1);drop(guard);},
   Err(error)=>{assert_ne!(initial,0);assert!(matches!(error,ProgramError::AccountBorrowFailed));},
  }
  assert_eq!(unsafe{(*counter).get()},initial);
  // No live guards remain. Restore the fresh state before dropping the Rc.
  unsafe{(*counter).set(0);}
  assert_eq!(**account.try_borrow_lamports().unwrap(),0);
  kani::cover!(initial==isize::MAX,"shared counter saturation rejects");
  kani::cover!(initial==isize::MAX-1,"last representable shared borrow");
  kani::cover!(initial==isize::MIN,"negative saturated counter rejects");
  kani::cover!(initial==0,"fresh exclusive borrow");
 }
}
