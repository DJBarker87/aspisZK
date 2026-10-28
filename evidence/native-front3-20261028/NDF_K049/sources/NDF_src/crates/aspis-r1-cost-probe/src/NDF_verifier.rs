use super::*;
#[path="NDF_reference.rs"] pub(super) mod reference;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[kani::proof_for_contract(Reader::raw::<32>)] #[kani::unwind(35)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn raw_contract(){let bytes:[u8;1768]=kani::any();let at:usize=kani::any();kani::assume(at<=1736);let mut r=Reader{bytes:&bytes,at};let _=r.raw::<32>();}
#[kani::proof] #[kani::stub_verified(Reader::raw::<32>)] #[kani::unwind(35)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn raw_caller(){let bytes:[u8;1768]=kani::any();let at:usize=kani::any();kani::assume(at<=1736);let mut r=Reader{bytes:&bytes,at};let out=r.raw::<32>();assert_eq!((out,r.at),reference::raw_ref::<32>(&bytes,at));}
