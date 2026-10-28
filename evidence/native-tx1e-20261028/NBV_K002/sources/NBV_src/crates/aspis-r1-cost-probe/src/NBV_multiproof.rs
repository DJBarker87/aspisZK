use super::*;
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u32]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u32]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBV_count_copy_prefix(){let input:[u32;16]=kani::any();let n:usize=kani::any();let k:usize=kani::any();kani::assume(n>0&&n<=16&&k<16);let mut level=[0u32;16];level[..n].copy_from_slice(&input[..n]);assert_eq!(level[k],if k<n{input[k]}else{0});}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u32]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u32]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBV_count_copy_wrong(){let mut input=[0u32;16];input[7]=1;input[15]=512;let n=16;let k=15;let mut level=[0u32;16];level[..n].copy_from_slice(&input[..n]);assert_eq!(level[k],0);}
