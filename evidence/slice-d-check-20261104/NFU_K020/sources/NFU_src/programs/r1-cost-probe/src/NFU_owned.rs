use super::*;
fn account()->OwnedAccount{OwnedAccount{key:Pubkey::new_from_array([0;32]),owner:Pubkey::new_from_array([0;32]),is_signer:kani::any(),is_writable:kani::any(),executable:kani::any(),length:Ok(0),bytes:Err(ProgramError::AccountBorrowFailed)}}
#[kani::proof]
fn readonly_buffer(){let a=core::mem::ManuallyDrop::new(account());let r=require_readonly_buffer(&a);let expected=if a.is_signer||a.is_writable||a.executable{Err(ProgramError::InvalidAccountData)}else{Ok(())};assert!((r==expected) != cfg!(NFU_invert));}
#[kani::proof]
fn key_identity(){let a=core::mem::ManuallyDrop::new(account());assert!((core::ptr::eq(a.key(),&a.key)) != cfg!(NFU_invert));}
#[kani::proof]
fn owner_identity(){let a=core::mem::ManuallyDrop::new(account());assert!((core::ptr::eq(a.owner(),&a.owner)) != cfg!(NFU_invert));}
