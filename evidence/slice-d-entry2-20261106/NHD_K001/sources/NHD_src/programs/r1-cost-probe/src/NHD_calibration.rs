//! Ruling (t) result-family calibration. Every observer is local.
use solana_program::{entrypoint::ProgramResult,program_error::ProgramError};
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));

#[kani::ensures(|r| r.is_ok() || matches!(r,Err(ProgramError::InvalidAccountData)))]
#[kani::modifies()]
fn program_result(_x:u8)->ProgramResult {Ok(())}
#[kani::proof_for_contract(program_result)]
fn program_contract(){let _=program_result(kani::any());}
#[kani::proof]
fn program_real(){assert_eq!(program_result(kani::any()),Ok(()));}
#[kani::proof]
#[kani::stub_verified(program_result)]
fn program_stub(){assert_eq!(program_result(kani::any()),Ok(()));}
#[kani::ensures(|r| r.is_ok())]
#[kani::modifies()]
fn program_bad_frame(local:&mut u8)->ProgramResult {*local=local.wrapping_add(1);Ok(())}
#[kani::proof_for_contract(program_bad_frame)]
fn program_modifies(){let mut local:u8=kani::any();let _=program_bad_frame(&mut local);}

#[kani::ensures(|r| r.is_ok())]
#[kani::modifies()]
fn length_result(x:usize)->Result<usize,ProgramError>{Ok(x)}
#[kani::proof_for_contract(length_result)]
fn length_contract(){let _=length_result(kani::any());}
#[kani::proof]
fn length_real(){let x:usize=kani::any();assert_eq!(length_result(x),Ok(x));}
#[kani::proof]
#[kani::stub_verified(length_result)]
fn length_stub(){let x:usize=kani::any();assert_eq!(length_result(x),Ok(x));}
#[kani::ensures(|r| r.is_ok())]
#[kani::modifies()]
fn length_bad_frame(local:&mut u8)->Result<usize,ProgramError>{*local=local.wrapping_add(1);Ok(0)}
#[kani::proof_for_contract(length_bad_frame)]
fn length_modifies(){let mut local:u8=kani::any();let _=length_bad_frame(&mut local);}

#[kani::ensures(|r| r.is_ok())]
#[kani::modifies()]
fn slice_result(x:&[u8])->Result<&[u8],ProgramError>{Ok(x)}
#[kani::proof_for_contract(slice_result)]
fn slice_contract(){let x:[u8;4]=kani::any();let _=slice_result(&x);}
#[kani::proof]
fn slice_real(){let x:[u8;4]=kani::any();let r=slice_result(&x).unwrap();assert_eq!(r.as_ptr(),x.as_ptr());assert_eq!(r.len(),4);}
#[kani::proof]
#[kani::stub_verified(slice_result)]
fn slice_stub(){let x:[u8;4]=kani::any();let r=slice_result(&x).unwrap();assert_eq!(r.as_ptr(),x.as_ptr());assert_eq!(r.len(),4);}
#[kani::ensures(|r| r.is_ok())]
#[kani::modifies()]
fn slice_bad_frame<'a>(x:&'a [u8],local:&mut u8)->Result<&'a [u8],ProgramError>{*local=local.wrapping_add(1);Ok(x)}
#[kani::proof_for_contract(slice_bad_frame)]
fn slice_modifies(){let x:[u8;4]=kani::any();let mut local:u8=kani::any();let _=slice_bad_frame(&x,&mut local);}
