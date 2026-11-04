use super::*;
fn account()->OwnedAccount{OwnedAccount{key:Pubkey::new_from_array(kani::any()),owner:Pubkey::new_from_array(kani::any()),is_signer:kani::any(),is_writable:kani::any(),executable:kani::any(),length:Ok(kani::any()),bytes:Err(ProgramError::AccountBorrowFailed)}}
#[kani::proof]
fn readonly_buffer(){let a=account();let r=require_readonly_buffer(&a);let expected=if a.is_signer||a.is_writable||a.executable{Err(ProgramError::InvalidAccountData)}else{Ok(())};assert!((r==expected) != cfg!(NFU_invert));}
#[kani::proof]
fn key_identity(){let a=account();assert!((core::ptr::eq(a.key(),&a.key)) != cfg!(NFU_invert));}
#[kani::proof]
fn owner_identity(){let a=account();assert!((core::ptr::eq(a.owner(),&a.owner)) != cfg!(NFU_invert));}
