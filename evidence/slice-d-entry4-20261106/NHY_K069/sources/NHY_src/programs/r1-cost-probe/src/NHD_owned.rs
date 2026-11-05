//! Isolated clone/transport steps; no verified-stub interface is claimed.
use super::*;
extern crate alloc;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[kani::proof] #[kani::unwind(2)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn clone_borrow_error(){let original=ProgramError::AccountBorrowFailed;let cloned=original.clone();assert!(matches!(cloned,ProgramError::AccountBorrowFailed));assert!(matches!(original,ProgramError::AccountBorrowFailed));}
#[kani::proof] #[kani::unwind(2)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn clone_invalid_data(){let original=ProgramError::InvalidAccountData;let cloned=original.clone();assert!(matches!(cloned,ProgramError::InvalidAccountData));assert!(matches!(original,ProgramError::InvalidAccountData));}
#[kani::proof] #[kani::unwind(2)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn clone_borrow_error_wrong(){let original=ProgramError::AccountBorrowFailed;let cloned=original.clone();assert!(!matches!(cloned,ProgramError::AccountBorrowFailed));}
#[kani::proof] #[kani::unwind(2)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn clone_invalid_data_wrong(){let original=ProgramError::InvalidAccountData;let cloned=original.clone();assert!(!matches!(cloned,ProgramError::InvalidAccountData));}

fn borrow_account()->OwnedAccount{OwnedAccount{key:Pubkey::new_from_array(kani::any()),owner:Pubkey::new_from_array(kani::any()),is_signer:kani::any(),is_writable:kani::any(),executable:kani::any(),length:Err(ProgramError::AccountBorrowFailed),bytes:Err(ProgramError::AccountBorrowFailed)}}
#[kani::requires(matches!(a.length,Err(ProgramError::AccountBorrowFailed)) && matches!(a.bytes,Err(ProgramError::AccountBorrowFailed)))]
#[kani::ensures(|r| matches!(r,Err(ProgramError::AccountBorrowFailed)))]
#[kani::modifies()]
fn borrow_length_packet(a:&OwnedAccount)->Result<usize,ProgramError>{a.data_len()}
#[kani::proof_for_contract(borrow_length_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn borrow_length_full_frame(){let a=core::mem::ManuallyDrop::new(borrow_account());let _=core::mem::ManuallyDrop::new(borrow_length_packet(&a));}

#[kani::requires(matches!(a.length,Err(ProgramError::AccountBorrowFailed)) && matches!(a.bytes,Err(ProgramError::AccountBorrowFailed)))]
#[kani::ensures(|r| !matches!(r,Err(ProgramError::AccountBorrowFailed)))]
#[kani::modifies()]
fn borrow_length_packet_wrong(a:&OwnedAccount)->Result<usize,ProgramError>{a.data_len()}
#[kani::proof_for_contract(borrow_length_packet_wrong)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn borrow_length_full_frame_wrong(){let a=core::mem::ManuallyDrop::new(borrow_account());let _=core::mem::ManuallyDrop::new(borrow_length_packet_wrong(&a));}

// Paired with NGL_CloneDomain.clone on SnapshotError; K014..017 native value laws.
// Domain is asserted at every use, never assumed as an output equality.
fn clone_canonical(e:&ProgramError)->ProgramError{match e{ProgramError::AccountBorrowFailed=>ProgramError::AccountBorrowFailed,ProgramError::InvalidAccountData=>ProgramError::InvalidAccountData,_=>{assert!(false,"clone domain");ProgramError::InvalidAccountData}}}
fn clone_canonical_wrong(e:&ProgramError)->ProgramError{match e{ProgramError::AccountBorrowFailed=>ProgramError::InvalidAccountData,ProgramError::InvalidAccountData=>ProgramError::AccountBorrowFailed,_=>{assert!(false,"clone domain");ProgramError::InvalidAccountData}}}

#[kani::requires(matches!(a.length,Err(ProgramError::AccountBorrowFailed)) && matches!(a.bytes,Err(ProgramError::AccountBorrowFailed)))]
#[kani::ensures(|r| *r)]
#[kani::modifies()]
fn checkpoint_borrow_packet(a:&OwnedAccount,p:&Pubkey,w:bool)->bool {
 let bad=a.owner!=*p||a.is_signer||a.executable||a.is_writable!=w;
 let r=require_verifier_checkpoint(a,p,w);
 if bad{matches!(r,Err(ProgramError::InvalidAccountData))}else{matches!(r,Err(ProgramError::AccountBorrowFailed))}
}
#[kani::proof_for_contract(checkpoint_borrow_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn checkpoint_borrow(){let a=core::mem::ManuallyDrop::new(borrow_account());let p=Pubkey::new_from_array(kani::any());let _=checkpoint_borrow_packet(&a,&p,kani::any());}
#[kani::proof_for_contract(checkpoint_borrow_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn checkpoint_borrow_wrong_clone(){let a=core::mem::ManuallyDrop::new(borrow_account());let p=Pubkey::new_from_array(kani::any());let _=checkpoint_borrow_packet(&a,&p,kani::any());}

#[kani::requires(matches!(a.length,Err(ProgramError::AccountBorrowFailed)) && matches!(a.bytes,Err(ProgramError::AccountBorrowFailed)))]
#[kani::ensures(|r| *r)]
#[kani::modifies()]
fn borrow_length_bool_packet(a:&OwnedAccount)->bool{let r=core::mem::ManuallyDrop::new(a.data_len());matches!(&*r,Err(ProgramError::AccountBorrowFailed))}
#[kani::proof_for_contract(borrow_length_bool_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn borrow_length_bool(){let a=core::mem::ManuallyDrop::new(borrow_account());let _=borrow_length_bool_packet(&a);}
#[kani::proof_for_contract(checkpoint_borrow_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn checkpoint_borrow_direct(){let a=core::mem::ManuallyDrop::new(borrow_account());let p=Pubkey::new_from_array(kani::any());let _=checkpoint_borrow_packet(&a,&p,kani::any());}

#[kani::ensures(|r| r.is_ok()||matches!(r,Err(ProgramError::InvalidAccountData)))]
#[kani::modifies()]
fn readonly_full_interface(a:&OwnedAccount,p:&Pubkey)->ProgramResult{require_readonly_account(a,p)}
fn readonly_good()->core::mem::ManuallyDrop<OwnedAccount>{let mut a=core::mem::ManuallyDrop::new(borrow_account());a.is_signer=false;a.is_writable=false;a.executable=false;a}
#[kani::proof_for_contract(readonly_full_interface)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn readonly_declared_contract(){let a=readonly_good();let _=readonly_full_interface(&a,&a.owner);}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn readonly_real(){let a=readonly_good();assert!(readonly_full_interface(&a,&a.owner).is_ok());}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub_verified(readonly_full_interface)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn readonly_stub(){let a=readonly_good();assert!(readonly_full_interface(&a,&a.owner).is_ok());}
#[kani::ensures(|r| r.is_ok()||matches!(r,Err(ProgramError::InvalidAccountData)))]
#[kani::modifies()]
fn readonly_frame_violation(a:&OwnedAccount,p:&Pubkey,local:&mut u8)->ProgramResult{*local=local.wrapping_add(1);require_readonly_account(a,p)}
#[kani::proof_for_contract(readonly_frame_violation)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn readonly_modifies(){let a=readonly_good();let mut local:u8=kani::any();let _=readonly_frame_violation(&a,&a.owner,&mut local);}

#[kani::requires(a.bytes.is_ok())]
#[kani::ensures(|r| r.is_ok())]
#[kani::modifies()]
fn data_full_interface(a:&OwnedAccount)->Result<&[u8],ProgramError>{match &a.bytes{Ok(v)=>Ok(v.as_slice()),Err(_)=>Err(ProgramError::InvalidAccountData)}}
fn data_good()->core::mem::ManuallyDrop<OwnedAccount>{let mut a=core::mem::ManuallyDrop::new(borrow_account());a.bytes=Ok(kani::vec::exact_vec::<u8,4>());a.length=Ok(4);a}
#[kani::proof_for_contract(data_full_interface)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn data_declared_contract(){let a=data_good();let _=data_full_interface(&a);}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn data_real(){let a=data_good();let expected=a.bytes.as_ref().unwrap();let got=data_full_interface(&a).unwrap();assert_eq!(got.as_ptr(),expected.as_ptr());assert_eq!(got.len(),expected.len());}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub_verified(data_full_interface)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn data_stub(){let a=data_good();let expected=a.bytes.as_ref().unwrap();let got=data_full_interface(&a).unwrap();assert_eq!(got.as_ptr(),expected.as_ptr());assert_eq!(got.len(),expected.len());}
#[kani::requires(a.bytes.is_ok())]
#[kani::ensures(|r| r.is_ok())]
#[kani::modifies()]
fn data_frame_violation<'a>(a:&'a OwnedAccount,local:&mut u8)->Result<&'a [u8],ProgramError>{*local=local.wrapping_add(1);data_full_interface(a)}
#[kani::proof_for_contract(data_frame_violation)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn data_modifies(){let a=data_good();let mut local:u8=kani::any();let _=data_frame_violation(&a,&mut local);}
