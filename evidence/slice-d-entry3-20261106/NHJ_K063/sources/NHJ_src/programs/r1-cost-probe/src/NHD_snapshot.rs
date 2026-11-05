//! One arbitrary byte window, plus actual shared-guard cleanup.
use super::*;
extern crate alloc;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn window<const N:usize>(wrong:bool){
 let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());
 let mut lamports:u64=kani::any();let old_lamports=lamports;
 let mut bytes=kani::vec::exact_vec::<u8,N>();
 let offset:usize=kani::any();kani::assume(offset<N);let original=bytes[offset];
 let signer:bool=kani::any();let writable:bool=kani::any();let executable:bool=kani::any();let rent:u64=kani::any();
 let a=core::mem::ManuallyDrop::new(AccountInfo::new(&key,signer,writable,&mut lamports,&mut bytes[offset..offset+1],&owner,executable,rent));
 let r=core::mem::ManuallyDrop::new(snapshot(&a,1,1));
 assert_eq!(r.key,key);assert_eq!(r.owner,owner);assert_eq!(r.is_signer,signer);assert_eq!(r.is_writable,writable);assert_eq!(r.executable,executable);
 assert!(matches!(r.length,Ok(n)if n==1));
 match &r.bytes {Ok(v)=>{assert_eq!(v.len(),1);assert!((v[0]==original)!=wrong);},Err(_)=>assert!(false)}
 // A second exclusive borrow succeeds only after snapshot's shared guard dropped.
 let held=a.try_borrow_mut_data().unwrap();assert_eq!(held.len(),1);assert_eq!(held[0],original);drop(held);
 assert_eq!(a.lamports(),old_lamports);assert_eq!(a.rent_epoch,rent);
}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn window_1768(){window::<1768>( false);}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn window_1768_wrong(){window::<1768>( true);}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn window_58295(){window::<58295>( false);}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn window_58295_wrong(){window::<58295>( true);}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn window_1880(){window::<1880>( false);}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn window_1880_wrong(){window::<1880>( true);}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn window_384(){window::<384>( false);}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn window_384_wrong(){window::<384>( true);}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn window_192(){window::<192>( false);}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn window_192_wrong(){window::<192>( true);}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn window_768(){window::<768>( false);}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn window_768_wrong(){window::<768>( true);}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn window_128(){window::<128>( false);}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn window_128_wrong(){window::<128>( true);}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn window_256(){window::<256>( false);}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn window_256_wrong(){window::<256>( true);}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn window_320(){window::<320>( false);}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn window_320_wrong(){window::<320>( true);}
