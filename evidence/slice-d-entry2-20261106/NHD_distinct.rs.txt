//! One frozen inner comparison iteration, at an arbitrary invariant pre-state.
use super::*;
extern crate alloc;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn selected(key:Pubkey)->OwnedAccount{OwnedAccount{key,owner:Pubkey::new_from_array([0;32]),is_signer:false,is_writable:false,executable:false,length:Err(ProgramError::AccountBorrowFailed),bytes:Err(ProgramError::AccountBorrowFailed)}}
#[kani::requires(previous<index && index<7)]
#[kani::ensures(|r| if accounts[previous].key()==accounts[index].key(){matches!(r.0,Err(ProgramError::InvalidArgument))&&r.1==previous}else{r.0.is_ok()&&r.1==previous+1})]
#[kani::modifies()]
fn comparison_step(accounts:&[&OwnedAccount;7],index:usize,mut previous:usize)->(ProgramResult,usize){
 if accounts[previous].key() == accounts[index].key() {
  return (Err(ProgramError::InvalidArgument),previous);
 }
 previous += 1;
 (Ok(()),previous)
}
#[kani::proof_for_contract(comparison_step)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn iteration7(){
 let keys:[[u8;32];7]=kani::any();
 let a=core::mem::ManuallyDrop::new(core::array::from_fn::<_,7,_>(|i|selected(Pubkey::new_from_array(keys[i]))));
 let accounts=core::array::from_fn::<_,7,_>(|i|&a[i]);
 let i:usize=kani::any();let p:usize=kani::any();kani::assume(p<i&&i<7);let _=comparison_step(&accounts,i,p);
}

#[kani::requires(previous<index && index<7)]
#[kani::ensures(|r| !(if accounts[previous].key()==accounts[index].key(){matches!(r.0,Err(ProgramError::InvalidArgument))&&r.1==previous}else{r.0.is_ok()&&r.1==previous+1}))]
#[kani::modifies()]
fn comparison_step_wrong(accounts:&[&OwnedAccount;7],index:usize,mut previous:usize)->(ProgramResult,usize){
 if accounts[previous].key() == accounts[index].key() {
  return (Err(ProgramError::InvalidArgument),previous);
 }
 previous += 1;
 (Ok(()),previous)
}
#[kani::proof_for_contract(comparison_step_wrong)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn iteration7_wrong(){
 let keys:[[u8;32];7]=kani::any();
 let a=core::mem::ManuallyDrop::new(core::array::from_fn::<_,7,_>(|i|selected(Pubkey::new_from_array(keys[i]))));
 let accounts=core::array::from_fn::<_,7,_>(|i|&a[i]);
 let i:usize=kani::any();let p:usize=kani::any();kani::assume(p<i&&i<7);let _=comparison_step_wrong(&accounts,i,p);
}
