use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn account()->OwnedAccount{OwnedAccount{key:Pubkey::new_from_array(kani::any()),owner:Pubkey::new_from_array(kani::any()),is_signer:kani::any(),is_writable:kani::any(),executable:kani::any(),length:Ok(kani::any()),bytes:Err(ProgramError::AccountBorrowFailed)}}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn readonly_account(){let a=core::mem::ManuallyDrop::new(account());let k=Pubkey::new_from_array(kani::any());let expected=if a.owner!=k||a.is_signer||a.is_writable||a.executable{Err(ProgramError::InvalidAccountData)}else{Ok(())};let r=require_readonly_account(&a,&k);assert!((r==expected) != cfg!(NGL_invert));}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn readonly_account_wrong(){let a=core::mem::ManuallyDrop::new(account());let k=Pubkey::new_from_array(kani::any());let expected=if a.owner!=k||a.is_signer||a.is_writable||a.executable{Err(ProgramError::InvalidAccountData)}else{Ok(())};let r=require_readonly_account(&a,&k);assert!((r==expected) == cfg!(NGL_invert));}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn length_deferred(){let mut a=core::mem::ManuallyDrop::new(account());let n:usize=kani::any();let tag:u8=kani::any();kani::assume(tag<3);a.length=if tag==0{Ok(n)}else if tag==1{Err(ProgramError::AccountBorrowFailed)}else{Err(ProgramError::InvalidAccountData)};let r=a.data_len();let exact=match tag{0=>matches!(r,Ok(v)if v==n),1=>matches!(r,Err(ProgramError::AccountBorrowFailed)),_=>matches!(r,Err(ProgramError::InvalidAccountData))};assert!(exact != cfg!(NGL_invert));}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn length_deferred_wrong(){let mut a=core::mem::ManuallyDrop::new(account());let n:usize=kani::any();let tag:u8=kani::any();kani::assume(tag<3);a.length=if tag==0{Ok(n)}else if tag==1{Err(ProgramError::AccountBorrowFailed)}else{Err(ProgramError::InvalidAccountData)};let r=a.data_len();let exact=match tag{0=>matches!(r,Ok(v)if v==n),1=>matches!(r,Err(ProgramError::AccountBorrowFailed)),_=>matches!(r,Err(ProgramError::InvalidAccountData))};assert!(exact == cfg!(NGL_invert));}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn data_deferred(){let mut a=core::mem::ManuallyDrop::new(account());let borrow:bool=kani::any();a.bytes=Err(if borrow{ProgramError::AccountBorrowFailed}else{ProgramError::InvalidAccountData});let r=a.data();let exact=if borrow{matches!(r,Err(ProgramError::AccountBorrowFailed))}else{matches!(r,Err(ProgramError::InvalidAccountData))};assert!(exact != cfg!(NGL_invert));}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn data_deferred_wrong(){let mut a=core::mem::ManuallyDrop::new(account());let borrow:bool=kani::any();a.bytes=Err(if borrow{ProgramError::AccountBorrowFailed}else{ProgramError::InvalidAccountData});let r=a.data();let exact=if borrow{matches!(r,Err(ProgramError::AccountBorrowFailed))}else{matches!(r,Err(ProgramError::InvalidAccountData))};assert!(exact == cfg!(NGL_invert));}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn checkpoint_meta(){let owner:[u8;32]=kani::any();let program:[u8;32]=kani::any();let mut a=core::mem::ManuallyDrop::new(account());a.owner=Pubkey::new_from_array(owner);let writable:bool=kani::any();let n:usize=kani::any();let error:bool=kani::any();a.length=if error{Err(ProgramError::AccountBorrowFailed)}else{Ok(n)};let invalid=owner!=program||a.is_signer||a.executable||a.is_writable!=writable;let r=require_verifier_checkpoint(&a,&Pubkey::new_from_array(program),writable);let exact=if invalid{matches!(r,Err(ProgramError::InvalidAccountData))}else if error{matches!(r,Err(ProgramError::AccountBorrowFailed))}else if n!=1768{matches!(r,Err(ProgramError::InvalidAccountData))}else{matches!(r,Ok(()))};assert!(exact != cfg!(NGL_invert));}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn checkpoint_meta_wrong(){let owner:[u8;32]=kani::any();let program:[u8;32]=kani::any();let mut a=core::mem::ManuallyDrop::new(account());a.owner=Pubkey::new_from_array(owner);let writable:bool=kani::any();let n:usize=kani::any();let error:bool=kani::any();a.length=if error{Err(ProgramError::AccountBorrowFailed)}else{Ok(n)};let invalid=owner!=program||a.is_signer||a.executable||a.is_writable!=writable;let r=require_verifier_checkpoint(&a,&Pubkey::new_from_array(program),writable);let exact=if invalid{matches!(r,Err(ProgramError::InvalidAccountData))}else if error{matches!(r,Err(ProgramError::AccountBorrowFailed))}else if n!=1768{matches!(r,Err(ProgramError::InvalidAccountData))}else{matches!(r,Ok(()))};assert!(exact == cfg!(NGL_invert));}
