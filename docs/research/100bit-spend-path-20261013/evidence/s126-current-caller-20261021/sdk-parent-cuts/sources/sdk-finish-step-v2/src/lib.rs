#![allow(dead_code,unexpected_cfgs)]
use solana_program::{account_info::AccountInfo,pubkey::Pubkey};
#[cfg_attr(kani,kani::requires(destination.len()==1768 && source.len()==1768))]
#[cfg_attr(kani,kani::requires(offset<1768))]
#[cfg_attr(kani,kani::requires(target==unsafe{destination.as_mut_ptr().add(offset)}))]
#[cfg_attr(kani,kani::modifies(target))]
#[cfg_attr(kani,kani::ensures(|_| destination[offset]==old(source[offset])))]
fn native_copy_step(destination:&mut std::cell::RefMut<'_,&mut [u8]>,source:&[u8],offset:usize,target:*mut u8) {
 destination[offset..offset+1].copy_from_slice(&source[offset..offset+1]);
}
#[cfg(kani)] mod proofs {
 use super::*;
 #[kani::proof_for_contract(native_copy_step)] #[kani::unwind(8)]
 fn actual_sdk_copy_step_frame() {
  let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());
  let flags:[bool;3]=kani::any();let rent:u64=kani::any();let mut amount:u64=kani::any();
  let mut bytes:[u8;1768]=kani::any();let source:[u8;1768]=kani::any();
  let offset:usize=kani::any();kani::assume(offset<1768);
  let account=AccountInfo::new(&key,flags[0],flags[1],&mut amount,&mut bytes,&owner,flags[2],rent);
  let mut guard=account.try_borrow_mut_data().unwrap();
  let target=unsafe{guard.as_mut_ptr().add(offset)};
  native_copy_step(&mut guard,&source,offset,target);
  kani::cover!(offset==0,"first actual SDK copy step");
  kani::cover!(offset==1767,"last actual SDK copy step");
 }
}
