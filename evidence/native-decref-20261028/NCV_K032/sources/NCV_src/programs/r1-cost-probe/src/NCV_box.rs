#![allow(non_snake_case,dead_code)]
use super::*;
const NCV_INVERSE:bool=false;
fn NCV_any_checkpoint()->PoolV1PairForestCheckpointV1{
 PoolV1PairForestCheckpointV1{bump:kani::any(),master:kani::any(),deployment_domain:kani::any(),checkpoint_sequence:kani::any(),global_root:[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())],lane_sequences:kani::any()}
}
#[kani::modifies()]
#[kani::ensures(|r:&Box<PoolV1PairForestCheckpointV1>| (**r==*a)!=NCV_INVERSE)]
fn NCV_box_copy(a:&PoolV1PairForestCheckpointV1)->Box<PoolV1PairForestCheckpointV1>{Box::new(*a)}
#[kani::modifies(x)]
#[kani::ensures(|r:&Box<PoolV1PairForestCheckpointV1>| **r==*a)]
fn NCV_box_frame(a:&PoolV1PairForestCheckpointV1,x:&mut u8,y:&mut u8)->Box<PoolV1PairForestCheckpointV1>{*x=1;if NCV_INVERSE{*y=2;}Box::new(*a)}
#[kani::proof_for_contract(NCV_box_copy)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NCV_KMX::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NCV_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::NCV_KMX::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::NCV_KMX::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::NCV_KMX::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::NCV_KMX::KMX_realloc)]
#[kani::unwind(34)]
fn NCV_box_copy_check(){let a=NCV_any_checkpoint();let _=NCV_box_copy(&a);}
#[kani::proof_for_contract(NCV_box_frame)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NCV_KMX::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NCV_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::NCV_KMX::KMX_clone_from_slice)]
#[kani::stub(alloc::vec::Vec::<u8>::extend_from_slice,crate::NCV_KMX::KMX_extend_from_slice)]
#[kani::stub(<[u8]>::to_vec,crate::NCV_KMX::KMX_to_vec)]
#[kani::stub(alloc::alloc::realloc,crate::NCV_KMX::KMX_realloc)]
#[kani::unwind(34)]
fn NCV_box_frame_check(){let a=NCV_any_checkpoint();let mut x=kani::any();let mut y=kani::any();let _=NCV_box_frame(&a,&mut x,&mut y);}
