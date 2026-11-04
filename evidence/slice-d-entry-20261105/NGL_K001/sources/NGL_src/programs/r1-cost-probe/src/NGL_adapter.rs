use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn readonly_meta(){let owner:[u8;32]=kani::any();let expected:[u8;32]=kani::any();let s:bool=kani::any();let w:bool=kani::any();let e:bool=kani::any();let r=readonly_meta_ok(&Pubkey::new_from_array(owner),&Pubkey::new_from_array(expected),s,w,e);let v=if owner!=expected||s||w||e{Err(ProgramError::InvalidAccountData)}else{Ok(())};assert!((r==v) != cfg!(NGL_invert));}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn key_copy(){let x:[u8;32]=kani::any();let k=Pubkey::new_from_array(x);let j:usize=kani::any();kani::assume(j<32);assert!((k.as_ref()[j]==x[j]) != cfg!(NGL_invert));}
