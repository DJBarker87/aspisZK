use super::*;
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(<[u32]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBY_slot_last_sentinel_wrong(){let mut proof=[0u8;57607];proof[57606]=1;let nodes=slot(&proof,5);let byte=nodes[nodes.len()-1];assert!(!(byte==proof[57606]&&nodes.len()==32*SLOT_NODES[5]));}
