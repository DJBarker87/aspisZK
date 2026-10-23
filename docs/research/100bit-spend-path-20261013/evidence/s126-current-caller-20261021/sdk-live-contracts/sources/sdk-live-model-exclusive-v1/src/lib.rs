#![allow(dead_code,unexpected_cfgs)]
use solana_program::{account_info::AccountInfo,pubkey::Pubkey,program_error::ProgramError};
use std::cell::Cell;
mod sdk_live_models;
#[cfg(kani)]
#[kani::requires(counter==std::rc::Rc::as_ptr(&account.data).cast::<Cell<isize>>())]
#[kani::modifies(counter.cast::<isize>())]
#[kani::ensures(|_| unsafe{(*counter).get()}==old(unsafe{(*counter).get()}))]
fn compare_live(account:&AccountInfo<'_>,counter:*const Cell<isize>){
 let initial=unsafe{(*counter).get()};
 let actual=account.try_borrow_mut_data();
 let after_actual=unsafe{(*counter).get()};
 let observed=match &actual {
  Ok(guard)=>{
   assert_eq!(std::mem::size_of_val(guard),2*std::mem::size_of::<usize>());
   Some(unsafe{[*(guard as *const _ as *const usize),*(guard as *const _ as *const usize).add(1)]})
  },
  Err(error)=>{assert_eq!(*error,ProgramError::AccountBorrowFailed);None},
 };
 drop(actual);
 assert_eq!(unsafe{(*counter).get()},initial);
 let expected=sdk_live_models::exclusive(account);
 assert_eq!(unsafe{(*counter).get()},after_actual);
 match expected {
  Ok(guard)=>{
   assert_eq!(std::mem::size_of_val(&guard),2*std::mem::size_of::<usize>());
   let words=unsafe{[*(std::ptr::addr_of!(guard).cast::<usize>()),*(std::ptr::addr_of!(guard).cast::<usize>().add(1))]};
   assert_eq!(observed,Some(words));
   assert_eq!(guard.len(),unsafe{(&*account.data.as_ptr()).len()});
   assert_eq!(guard.as_ptr(),unsafe{(&*account.data.as_ptr()).as_ptr()});
   drop(guard);
  },
  Err(error)=>{assert_eq!(error,ProgramError::AccountBorrowFailed);assert!(observed.is_none());},
 }

 assert_eq!(unsafe{(*counter).get()},initial);
}

#[cfg(kani)] mod proofs {
use super::*;
#[kani::proof_for_contract(compare_live)] #[kani::unwind(36)]
fn actual_sdk_live_contract(){
 let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());
 let flags:[bool;3]=kani::any();let rent_epoch:u64=kani::any();let mut lamports:u64=kani::any();
 let mut bytes:[u8;10485760]=kani::any();let length:usize=kani::any();kani::assume(length<=10485760);
 let account=AccountInfo::new(&key,flags[0],flags[1],&mut lamports,&mut bytes[..length],&owner,flags[2],rent_epoch);
 let data=std::rc::Rc::as_ptr(&account.data);let amount=std::rc::Rc::as_ptr(&account.lamports);
 let counter=data.cast::<Cell<isize>>();let amount_counter=amount.cast::<Cell<isize>>();
 let fields=[unsafe{data.cast::<usize>().sub(2).cast_mut()},unsafe{data.cast::<usize>().sub(1).cast_mut()},unsafe{amount.cast::<usize>().sub(2).cast_mut()},unsafe{amount.cast::<usize>().sub(1).cast_mut()}];
 for field in fields {assert_eq!(unsafe{*field},1);}
 let rc:[usize;4]=kani::any();for count in rc {kani::assume(count>=1);}
 for i in 0..4 {unsafe{*fields[i]=rc[i];}}
 assert_eq!(std::rc::Rc::strong_count(&account.data),rc[0]);assert_eq!(std::rc::Rc::weak_count(&account.data),rc[1]-1);
 assert_eq!(std::rc::Rc::strong_count(&account.lamports),rc[2]);assert_eq!(std::rc::Rc::weak_count(&account.lamports),rc[3]-1);
 let initial:isize=kani::any();let initial_amount:isize=kani::any();
 unsafe{(*counter).set(initial);(*amount_counter).set(initial_amount);}
 compare_live(&account,counter);
 assert_eq!(unsafe{(*counter).get()},initial);assert_eq!(unsafe{(*amount_counter).get()},initial_amount);
 for i in 0..4 {assert_eq!(unsafe{*fields[i]},rc[i]);}
 unsafe{(*counter).set(0);(*amount_counter).set(0);}
 for field in fields {unsafe{*field=1;}}
 kani::cover!(initial==0&&length==10485760,"maximum view ordinary source contract");
 kani::cover!(initial==isize::MAX&&length==0,"saturated counter empty source contract");
 kani::cover!(initial == -1 && rc[0]==usize::MAX,"exclusive counter and full Rc domain");
}
}
