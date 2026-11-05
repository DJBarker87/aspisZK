//! Exact metadata signature calibration; the weak pilot contract is intentional.
use super::*;
extern crate alloc;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[kani::ensures(|r| r.is_ok()||matches!(r,Err(ProgramError::InvalidAccountData)))]
#[kani::modifies()]
fn full_interface(a:&Pubkey,b:&Pubkey,s:bool,w:bool,e:bool)->ProgramResult{readonly_meta_ok(a,b,s,w,e)}
#[kani::proof_for_contract(full_interface)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn declared_contract(){let a=Pubkey::new_from_array(kani::any());let _=full_interface(&a,&a,false,false,false);}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn real(){let a=Pubkey::new_from_array(kani::any());assert!(full_interface(&a,&a,false,false,false).is_ok());}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub_verified(full_interface)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn stub(){let a=Pubkey::new_from_array(kani::any());assert!(full_interface(&a,&a,false,false,false).is_ok());}
#[kani::ensures(|r| r.is_ok()||matches!(r,Err(ProgramError::InvalidAccountData)))]
#[kani::modifies()]
fn frame_violation(a:&Pubkey,b:&Pubkey,s:bool,w:bool,e:bool,local:&mut u8)->ProgramResult{*local=local.wrapping_add(1);readonly_meta_ok(a,b,s,w,e)}
#[kani::proof_for_contract(frame_violation)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn modifies(){let a=Pubkey::new_from_array(kani::any());let mut local:u8=kani::any();let _=frame_violation(&a,&a,false,false,false,&mut local);}
