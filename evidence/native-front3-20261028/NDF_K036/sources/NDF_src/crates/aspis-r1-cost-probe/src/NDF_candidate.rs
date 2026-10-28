use super::*;
#[path="NDF_reference.rs"] pub(super) mod reference;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[kani::proof_for_contract(opening)]
#[kani::unwind(835)]
fn opening_contract(){let proof:[u8;compact::PROOF_BYTES]=kani::any();let i:usize=kani::any();kani::assume(i<22);let _=opening(&proof,i);}
#[kani::proof_for_contract(batch_key_at)]
fn key_contract(){let keys:[u64;16]=kani::any();let i:usize=kani::any();kani::assume(i<16);let _=batch_key_at(&keys,i);}
#[kani::proof] #[kani::stub_verified(batch_key_at)]
fn key_caller(){let keys:[u64;16]=kani::any();let i:usize=kani::any();kani::assume(i<16);assert_eq!(batch_key_at(&keys,i),reference::batch_key_at_ref(&keys,i));}
#[kani::proof] #[kani::stub_verified(batch_key_at)]
fn key_wrong(){let keys:[u64;16]=kani::any();let i:usize=kani::any();kani::assume(i<16);assert_ne!(batch_key_at(&keys,i),reference::batch_key_at_ref(&keys,i));}
#[kani::proof_for_contract(same_batch_index)]
fn index_contract(){let values:[u32;16]=kani::any();let i:usize=kani::any();kani::assume(i<16);let _=same_batch_index(&values,i,kani::any());}
#[kani::proof] #[kani::stub_verified(same_batch_index)]
fn index_caller(){let values:[u32;16]=kani::any();let i:usize=kani::any();let v:u32=kani::any();kani::assume(i<16);assert_eq!(same_batch_index(&values,i,v),reference::same_batch_index_ref(&values,i,v));}
#[kani::proof] #[kani::stub_verified(same_batch_index)]
fn index_wrong(){let values:[u32;16]=kani::any();let i:usize=kani::any();let v:u32=kani::any();kani::assume(i<16);assert_ne!(same_batch_index(&values,i,v),reference::same_batch_index_ref(&values,i,v));}
#[kani::proof_for_contract(same_batch_leaf)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn leaf_contract(){let values:[[u8;32];16]=kani::any();let i:usize=kani::any();kani::assume(i<16);let _=same_batch_leaf(&values,i,kani::any());}
#[kani::proof] #[kani::stub_verified(same_batch_leaf)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn leaf_caller(){let values:[[u8;32];16]=kani::any();let i:usize=kani::any();let v:[u8;32]=kani::any();kani::assume(i<16);assert_eq!(same_batch_leaf(&values,i,v),reference::same_batch_leaf_ref(&values,i,v));}
#[kani::proof] #[kani::stub_verified(same_batch_leaf)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn leaf_wrong(){let values:[[u8;32];16]=kani::any();let i:usize=kani::any();let v:[u8;32]=kani::any();kani::assume(i<16);assert_ne!(same_batch_leaf(&values,i,v),reference::same_batch_leaf_ref(&values,i,v));}
