#![allow(dead_code,unexpected_cfgs)]
use solana_program::{account_info::AccountInfo,pubkey::Pubkey,program_error::ProgramError};
use aspis_s126_owned_sdk::{OwnedAccount,OwnedDataCell,OwnedLamportsCell,OwnedSdk,LiveGuards,
 owned_acquire_shared,owned_acquire_checkpoint,owned_release_guards};
#[cfg(kani)] mod proofs {
 use super::*;
 #[kani::proof]
 #[kani::unwind(3)]
 fn shared_owned_join() {
  let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());
  let flags:[bool;3]=kani::any();let rent_epoch:u64=kani::any();let mut lamports:u64=kani::any();let initial_lamports=lamports;
  let mut bytes:[u8;1768]=kani::any();let selected:usize=kani::any();kani::assume(selected<1768);
  let snapshot=bytes.to_vec();let initial_byte=bytes[selected];
  let account=AccountInfo::new(&key,flags[0],flags[1],&mut lamports,&mut bytes,&owner,flags[2],rent_epoch);
  let counter=std::rc::Rc::as_ptr(&account.data).cast::<std::cell::Cell<isize>>();
  assert_eq!(unsafe{(*counter).get()},0);
  let trial=account.try_borrow_data().unwrap();assert_eq!(unsafe{(*counter).get()},1);drop(trial);
  let initial:isize=kani::any();unsafe{(*counter).set(initial);}
  let mut model=OwnedSdk{
   accounts:vec![OwnedAccount{key:key.to_bytes(),owner:owner.to_bytes(),is_signer:flags[0],is_writable:flags[1],executable:flags[2],rent_epoch,data_slot:0,lamports_slot:0}],
   data_cells:vec![OwnedDataCell{bytes:snapshot,borrowed:initial,strong:std::rc::Rc::strong_count(&account.data),weak:std::rc::Rc::weak_count(&account.data)}],
   lamports_cells:vec![OwnedLamportsCell{amount:initial_lamports,borrowed:0,strong:std::rc::Rc::strong_count(&account.lamports),weak:std::rc::Rc::weak_count(&account.lamports)}],
  };
  let expected=owned_acquire_shared(&mut model,0);
  let actual=account.try_borrow_data();
  match actual {
   Ok(guard)=>{
    assert!(expected.is_ok());assert_eq!(model.data_cells[0].borrowed,unsafe{(*counter).get()});
    assert_eq!(model.data_cells[0].bytes[selected],guard[selected]);
    drop(guard);
    owned_release_guards(&mut model,LiveGuards{checkpoint:None,public:Some(0),proof:None});
   },
   Err(error)=>{assert!(matches!(error,ProgramError::AccountBorrowFailed));assert!(matches!(expected,Err(ProgramError::AccountBorrowFailed)));},
  }
  assert_eq!(model.data_cells[0].borrowed,initial);assert_eq!(unsafe{(*counter).get()},initial);
  assert_eq!(model.data_cells[0].bytes[selected],initial_byte);
  assert_eq!(model.data_cells[0].strong,std::rc::Rc::strong_count(&account.data));
  assert_eq!(model.data_cells[0].weak,std::rc::Rc::weak_count(&account.data));
  assert_eq!(model.accounts[0].key,account.key.to_bytes());assert_eq!(model.accounts[0].owner,account.owner.to_bytes());
  assert_eq!(model.accounts[0].is_signer,account.is_signer);assert_eq!(model.accounts[0].is_writable,account.is_writable);
  assert_eq!(model.accounts[0].executable,account.executable);assert_eq!(model.accounts[0].rent_epoch,account.rent_epoch);
  assert_eq!(model.lamports_cells[0].amount,**account.try_borrow_lamports().unwrap());
  unsafe{(*counter).set(0);}
  kani::cover!(initial==isize::MAX,"matching saturated failure");
  kani::cover!(initial==isize::MAX-1,"matching last shared acquisition/release");
 }
}
