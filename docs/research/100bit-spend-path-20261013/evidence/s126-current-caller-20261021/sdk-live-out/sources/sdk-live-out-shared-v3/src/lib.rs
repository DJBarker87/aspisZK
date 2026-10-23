#![allow(dead_code,unexpected_cfgs)]
use solana_program::{account_info::AccountInfo,pubkey::Pubkey,program_error::ProgramError};
use std::{cell::Cell,mem::MaybeUninit};
type Reply<'b,'a> = Result<std::cell::Ref<'b,&'b mut[u8]>,ProgramError>;
fn counter(account:&AccountInfo<'_>)->*const Cell<isize>{std::rc::Rc::as_ptr(&account.data).cast()}
#[kani::modifies(out.as_mut_ptr().cast::<[u8;std::mem::size_of::<Reply<'b,'a>>()]>(), counter(account).cast_mut().cast::<isize>())]
#[kani::ensures(|_| {
 let before=old(unsafe{(*counter(account)).get()});let now=unsafe{(*counter(account)).get()};
 match unsafe{out.assume_init_ref()} {
  Ok(guard)=>before>=0 && before<isize::MAX && now==before+1 && std::mem::size_of_val(guard)==2*std::mem::size_of::<usize>() &&
   unsafe{*(guard as *const _ as *const usize)}==account.data.as_ptr() as usize &&
   unsafe{*(guard as *const _ as *const usize).add(1)}==counter(account) as usize,
  Err(e)=>matches!(e,ProgramError::AccountBorrowFailed) && (before<0 || before==isize::MAX) && now==before,
 }
})]
fn sdk_out<'b,'a>(account:&'b AccountInfo<'a>,out:&mut MaybeUninit<Reply<'b,'a>>) {
 out.write(account.try_borrow_data());
}
fn sdk_bridge<'b,'a>(account:&'b AccountInfo<'a>)->Reply<'b,'a>{
 let mut out=MaybeUninit::uninit();sdk_out(account,&mut out);unsafe{out.assume_init()}
}
#[cfg(kani)] mod proofs {
use super::*;
#[kani::proof_for_contract(sdk_out)] #[kani::unwind(36)]
fn actual_sdk_out_contract(){
 let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());
 let flags:[bool;3]=kani::any();let rent_epoch:u64=kani::any();let mut lamports:u64=kani::any();
 let mut bytes:[u8;58295]=kani::any();let length:usize=kani::any();kani::assume(length<=58295);
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
 let mut output=MaybeUninit::uninit();sdk_out(&account,&mut output);
 let result=unsafe{output.assume_init()};
 drop(result);
 assert_eq!(unsafe{(*counter).get()},initial);assert_eq!(unsafe{(*amount_counter).get()},initial_amount);
 for i in 0..4 {assert_eq!(unsafe{*fields[i]},rc[i]);}
 unsafe{(*counter).set(0);(*amount_counter).set(0);}
 for field in fields {unsafe{*field=1;}}
 kani::cover!(initial==0&&length==58295,"maximum view ordinary source contract");
 kani::cover!(initial==isize::MAX&&length==0,"saturated counter empty source contract");
 kani::cover!(initial == -1 && rc[0]==usize::MAX,"exclusive counter and full Rc domain");
}
#[kani::proof]
#[kani::stub_verified(sdk_out)] #[kani::unwind(36)]
fn actual_sdk_out_bridge(){
 let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());
 let flags:[bool;3]=kani::any();let rent_epoch:u64=kani::any();let mut lamports:u64=kani::any();
 let mut bytes:[u8;58295]=kani::any();let length:usize=kani::any();kani::assume(length<=58295);
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
 let result=sdk_bridge(&account);
 drop(result);
 assert_eq!(unsafe{(*counter).get()},initial);assert_eq!(unsafe{(*amount_counter).get()},initial_amount);
 for i in 0..4 {assert_eq!(unsafe{*fields[i]},rc[i]);}
 unsafe{(*counter).set(0);(*amount_counter).set(0);}
 for field in fields {unsafe{*field=1;}}
 kani::cover!(initial==0&&length==58295,"maximum view ordinary source contract");
 kani::cover!(initial==isize::MAX&&length==0,"saturated counter empty source contract");
 kani::cover!(initial == -1 && rc[0]==usize::MAX,"exclusive counter and full Rc domain");
}
}
