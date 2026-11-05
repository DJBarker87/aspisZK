//! Default build only. Native static read is not a deployed-slot theorem.
use super::*;
extern crate alloc;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn pool_default(){let value=pool_program_id();let i:usize=kani::any();kani::assume(i<32);assert_eq!(value[i],0x41);}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn pool_default_wrong(){let value=pool_program_id();let i:usize=kani::any();kani::assume(i<32);assert_eq!(value[i],0x44);}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn registry_default(){let value=registry_program_id();let i:usize=kani::any();kani::assume(i<32);assert_eq!(value[i],0x44);}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn registry_default_wrong(){let value=registry_program_id();let i:usize=kani::any();kani::assume(i<32);assert_eq!(value[i],0x33);}
