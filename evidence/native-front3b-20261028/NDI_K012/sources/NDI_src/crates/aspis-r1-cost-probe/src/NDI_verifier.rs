use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[kani::requires(r.at<=r.bytes.len() && 32<=r.bytes.len()-r.at && j<32)]
#[kani::modifies(&mut r.at)]
#[kani::ensures(|out| ((*out==r.bytes[old(r.at)+j]) && r.at==old(r.at)+32) != cfg!(NDI_invert_raw_window))]
fn raw_window(r:&mut Reader<'_>,j:usize)->u8 {r.raw::<32>()[j]}
#[kani::proof_for_contract(raw_window)] #[kani::unwind(35)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn raw_window_contract(){let bytes:[u8;1768]=kani::any();let at:usize=kani::any();let j:usize=kani::any();kani::assume(at<=1736 && j<32);let mut r=Reader{bytes:&bytes,at};let _=raw_window(&mut r,j);}
#[kani::proof] #[kani::stub_verified(raw_window)] #[kani::unwind(35)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn raw_window_caller(){let bytes:[u8;1768]=kani::any();let at:usize=kani::any();let j:usize=kani::any();kani::assume(at<=1736 && j<32);let mut r=Reader{bytes:&bytes,at};let out=raw_window(&mut r,j);assert_eq!(out,bytes[at+j]);assert_eq!(r.at,at+32);}
#[kani::proof] #[kani::stub_verified(raw_window)] #[kani::unwind(35)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn raw_window_wrong(){let bytes:[u8;1768]=kani::any();let at:usize=kani::any();let j:usize=kani::any();kani::assume(at<=1736 && j<32);let mut r=Reader{bytes:&bytes,at};let out=raw_window(&mut r,j);assert_ne!(out,bytes[at+j]);}
