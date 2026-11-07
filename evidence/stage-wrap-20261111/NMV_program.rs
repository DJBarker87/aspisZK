use super::*;
use core::cell::RefCell;
use solana_program::program_error::ProgramError;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));

// An existing key reference retains provenance to this harness-local enclosing
// allocation. Only the disjoint RefCell field is written, never the key.
#[repr(C)]
struct Port { key: Pubkey, log: RefCell<Log> }
#[derive(Default)]
struct Log { reads: usize, writes: usize, first: usize, second: usize }
fn port<'a>(a:&'a AccountInfo<'_>)->&'a Port { unsafe { &*(a.key as *const Pubkey as *const Port) } }
fn shared<'a,'info: 'info>(a:&'a AccountInfo<'info>)->Result<core::cell::Ref<'a,&'info mut [u8]>,ProgramError>{
 port(a).log.borrow_mut().reads+=1;
 a.data.try_borrow().map_err(|_|ProgramError::AccountBorrowFailed)
}
fn shared_omit<'a,'info: 'info>(a:&'a AccountInfo<'info>)->Result<core::cell::Ref<'a,&'info mut [u8]>,ProgramError>{a.data.try_borrow().map_err(|_|ProgramError::AccountBorrowFailed)}
fn exclusive<'a,'info: 'info>(a:&'a AccountInfo<'info>)->Result<core::cell::RefMut<'a,&'info mut [u8]>,ProgramError>{
 port(a).log.borrow_mut().writes+=1;
 a.data.try_borrow_mut().map_err(|_|ProgramError::AccountBorrowFailed)
}

fn snapshot_test<const MODE:u8,const BRANCH:u8>() {
 let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());
 let p=Port{key,log:RefCell::new(Log::default())};
 let signer:bool=kani::any();let writable:bool=kani::any();let executable:bool=kani::any();
 let mut lamports:u64=kani::any();let mut bytes:[u8;4]=kani::any();
 let n:usize=kani::any();kani::assume(n<=4);
 let original:[u8;4]=bytes;let data=&mut bytes[..n];
 let a=AccountInfo::new(&p.key,signer,writable,&mut lamports,data,&owner,executable,0);
 let l1:usize=kani::any();let l2:usize=kani::any();
 if BRANCH==0 {kani::assume(n==l1||n==l2);} else if BRANCH==1 {kani::assume(n!=l1&&n!=l2);}
 let hold=if BRANCH==2 {Some(a.data.borrow_mut())} else {None};
 let out=snapshot(&a,if MODE==2 {l1.wrapping_add(1)}else{l1},l2);
 let k:usize=kani::any();kani::assume(k<32);
 assert_eq!(out.key.as_ref()[k],p.key.as_ref()[k]);assert_eq!(out.owner.as_ref()[k],owner.as_ref()[k]);
 assert_eq!(out.is_signer,signer);assert_eq!(out.is_writable,writable);assert_eq!(out.executable,executable);
 if BRANCH==2 { assert!(matches!(out.length,Err(ProgramError::AccountBorrowFailed)));assert!(matches!(out.bytes,Err(ProgramError::AccountBorrowFailed))); }
 else {
  assert_eq!(out.length,Ok(if MODE==1 {n+1}else{n}));
  if n==l1||n==l2 {
   let out=out.bytes.unwrap();assert_eq!(out.len(),n);
   let i:usize=kani::any();if i<n {assert_eq!(out[i],original[i]);}
  } else {assert!(matches!(out.bytes,Err(ProgramError::InvalidAccountData)));}
 }
 assert_eq!(p.log.borrow().reads,1);
 drop(hold);
 assert!(a.try_borrow_mut_data().is_ok());
}
#[kani::proof]#[kani::unwind(8)]
#[kani::stub(solana_program::account_info::AccountInfo::try_borrow_data,shared)]
#[kani::stub(solana_program::account_info::AccountInfo::try_borrow_mut_data,exclusive)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
fn NMV_snapshot_admitted(){snapshot_test::<0,0>();}
#[kani::proof]#[kani::unwind(8)]
#[kani::stub(solana_program::account_info::AccountInfo::try_borrow_data,shared)]
#[kani::stub(solana_program::account_info::AccountInfo::try_borrow_mut_data,exclusive)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
fn NMV_snapshot_malformed(){snapshot_test::<0,1>();}
#[kani::proof]#[kani::unwind(8)]
#[kani::stub(solana_program::account_info::AccountInfo::try_borrow_data,shared)]
#[kani::stub(solana_program::account_info::AccountInfo::try_borrow_mut_data,exclusive)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
fn NMV_snapshot_conflict(){snapshot_test::<0,2>();}
#[kani::proof]#[kani::unwind(8)]
#[kani::stub(solana_program::account_info::AccountInfo::try_borrow_data,shared)]
#[kani::stub(solana_program::account_info::AccountInfo::try_borrow_mut_data,exclusive)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
fn NMV_snapshot_reply_control(){snapshot_test::<1,0>();}
#[kani::proof]#[kani::unwind(8)]
#[kani::stub(solana_program::account_info::AccountInfo::try_borrow_data,shared)]
#[kani::stub(solana_program::account_info::AccountInfo::try_borrow_mut_data,exclusive)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
fn NMV_snapshot_argument_control(){snapshot_test::<2,0>();}
#[kani::proof]#[kani::unwind(8)]
#[kani::stub(solana_program::account_info::AccountInfo::try_borrow_data,shared_omit)]
#[kani::stub(solana_program::account_info::AccountInfo::try_borrow_mut_data,exclusive)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
fn NMV_snapshot_footprint_control(){snapshot_test::<3,1>();}
#[kani::proof]#[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn NMV_copy_pass(){let src:[u8;4]=kani::any();let mut dst=[0u8;4];dst.copy_from_slice(&src);assert_eq!(src,dst);}
#[kani::proof]#[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn NMV_copy_fail(){let src:[u8;4]=kani::any();let mut dst=[0u8;4];dst.copy_from_slice(&src);assert_ne!(src,dst);}

include!("NMV_parent.rs");
