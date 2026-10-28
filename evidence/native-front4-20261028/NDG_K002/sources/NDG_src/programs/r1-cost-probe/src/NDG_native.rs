use super::*;
#[path="NDG_reference.rs"] pub mod reference;
#[kani::proof_for_contract(super::pool_program_id)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDG_kmx::KMX_copy_nonoverlapping)]
#[kani::unwind(34)]
fn pool_contract(){pool_program_id();}
#[kani::proof_for_contract(super::registry_program_id)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDG_kmx::KMX_copy_nonoverlapping)]
#[kani::unwind(34)]
fn registry_contract(){registry_program_id();}
#[kani::proof_for_contract(super::readonly_buffer_meta_ok)]
fn buffer_contract(){let _=readonly_buffer_meta_ok(kani::any(),kani::any(),kani::any());}
#[kani::proof_for_contract(super::readonly_meta_ok)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDG_kmx::KMX_copy_nonoverlapping)]
#[kani::unwind(34)]
fn meta_contract(){let a=Pubkey::new_from_array(kani::any());let b=Pubkey::new_from_array(kani::any());let _=readonly_meta_ok(&a,&b,kani::any(),kani::any(),kani::any());}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDG_kmx::KMX_copy_nonoverlapping)]
fn copy_positive(){let src:[u8;32]=kani::any();let mut dst=[0;32];unsafe{core::ptr::copy_nonoverlapping(src.as_ptr(),dst.as_mut_ptr(),32)};let i:usize=kani::any();kani::assume(i<32);assert_eq!(src[i],dst[i]);}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDG_kmx::KMX_copy_nonoverlapping)]
fn copy_negative(){let mut src=[0u8;32];src[31]=1;let mut dst=[0;32];unsafe{core::ptr::copy_nonoverlapping(src.as_ptr(),dst.as_mut_ptr(),32)};assert_eq!(dst[31],0);}
