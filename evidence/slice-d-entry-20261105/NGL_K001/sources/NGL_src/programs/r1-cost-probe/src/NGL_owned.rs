use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn account()->OwnedAccount{OwnedAccount{key:Pubkey::new_from_array(kani::any()),owner:Pubkey::new_from_array(kani::any()),is_signer:kani::any(),is_writable:kani::any(),executable:kani::any(),length:Ok(kani::any()),bytes:Err(ProgramError::AccountBorrowFailed)}}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn readonly_account(){let a=core::mem::ManuallyDrop::new(account());let k=Pubkey::new_from_array(kani::any());let expected=if a.owner!=k||a.is_signer||a.is_writable||a.executable{Err(ProgramError::InvalidAccountData)}else{Ok(())};let r=require_readonly_account(&a,&k);assert!((r==expected) != cfg!(NGL_invert));}
