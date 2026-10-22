//! Proof-only exact SDK borrow references. Return the real std guard types.
//! Their full two-word layout, result/error and counter frame must be checked
//! against the pinned original SDK before any caller may use these stubs.
use solana_program::{account_info::AccountInfo,program_error::ProgramError};
use std::{cell::{Cell,Ref,RefMut},rc::Rc};

#[repr(C)]
struct GuardBits<T>{value:*mut T,counter:*const Cell<isize>}

pub fn length(account:&AccountInfo<'_>)->Result<usize,ProgramError>{
 let counter=Rc::as_ptr(&account.data).cast::<Cell<isize>>();
 let before=unsafe{(*counter).get()};
 if before>=0 && before<isize::MAX {
  Ok(unsafe{(&*account.data.as_ptr()).len()})
 }else{Err(ProgramError::AccountBorrowFailed)}
}
pub fn shared<'b,'a>(account:&'b AccountInfo<'a>)->Result<Ref<'b,&'b mut [u8]>,ProgramError>{
 let counter=Rc::as_ptr(&account.data).cast::<Cell<isize>>();
 let before=unsafe{(*counter).get()};
 if before>=0 && before<isize::MAX {
  unsafe{(*counter).set(before+1);}
  let bits=GuardBits{value:account.data.as_ptr(),counter};
  Ok(unsafe{std::mem::transmute::<GuardBits<&'a mut [u8]>,Ref<'b,&'b mut [u8]>>(bits)})
 }else{Err(ProgramError::AccountBorrowFailed)}
}
pub fn exclusive<'b,'a>(account:&'b AccountInfo<'a>)->Result<RefMut<'b,&'a mut [u8]>,ProgramError>{
 let counter=Rc::as_ptr(&account.data).cast::<Cell<isize>>();
 let before=unsafe{(*counter).get()};
 if before==0 {
  unsafe{(*counter).set(-1);}
  let bits=GuardBits{value:account.data.as_ptr(),counter};
  Ok(unsafe{std::mem::transmute::<GuardBits<&'a mut [u8]>,RefMut<'b,&'a mut [u8]>>(bits)})
 }else{Err(ProgramError::AccountBorrowFailed)}
}
