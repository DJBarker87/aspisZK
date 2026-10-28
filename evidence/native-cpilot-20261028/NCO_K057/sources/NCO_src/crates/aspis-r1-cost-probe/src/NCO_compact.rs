use super::*;
#[path="NCO_reference.rs"] pub(super) mod reference;
#[kani::proof_for_contract(compact_row)]
fn compact_row_contract(){let _=compact_row(kani::any());}
#[kani::proof] #[kani::stub_verified(compact_row)]
fn compact_row_caller(){let row:u8=kani::any();assert_eq!(compact_row(row),reference::compact_row_ref(row));}
#[kani::proof] #[kani::stub_verified(compact_row)]
fn compact_row_wrong(){let row:u8=kani::any();assert_ne!(compact_row(row),reference::compact_row_ref(row));}
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
pub(super) fn expanded_one(compact:&[u8],out:&[u8])->bool{
 if compact.len()!=16 || out.len()!=32{return false;}
 let mut j=0;while j<32 {if out[j] != if j<16{compact[j]}else{0}{return false;}j+=1;}true
}
#[kani::proof_for_contract(expand_values)] #[kani::unwind(35)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn expand_contract(){let compact:[u8;16]=kani::any();let mut out:[u8;32]=kani::any();let _=expand_values(&compact,&mut out);}
#[kani::proof] #[kani::unwind(35)] #[kani::stub_verified(expand_values)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn expand_callsite(){let compact:[u8;16]=kani::any();let mut out:[u8;32]=kani::any();assert_eq!(expand_values(&compact,&mut out),Ok(()));assert!(expanded_one(&compact,&out));}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn copy_positive(){let compact:[u8;16]=kani::any();let mut out:[u8;16]=kani::any();out.copy_from_slice(&compact);let j:usize=kani::any();kani::assume(j<16);assert_eq!(out[j],compact[j]);}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn copy_negative(){let compact:[u8;16]=kani::any();let mut out:[u8;16]=kani::any();out.copy_from_slice(&compact);let j:usize=kani::any();kani::assume(j<16);assert_ne!(out[j],compact[j]);}
