//! Fixed-array interface fidelity and deployed native static packets.
use super::*;
extern crate alloc;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
const POOL_DEV:[u8;32]=[160,19,98,42,240,202,109,154,218,233,162,167,169,176,187,66,122,69,190,75,195,45,233,50,40,58,26,66,26,133,145,52];
#[kani::ensures(|r| *r==POOL_DEV)] #[kani::modifies()]
fn pool_packet()->[u8;32]{ pool_program_id() }
#[kani::proof_for_contract(pool_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn pool_devnet(){pool_packet();}
#[kani::ensures(|r| *r!=POOL_DEV)] #[kani::modifies()]
fn pool_wrong_packet()->[u8;32]{ pool_program_id() }
#[kani::proof_for_contract(pool_wrong_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn pool_devnet_wrong(){pool_wrong_packet();}
const REGISTRY_DEV:[u8;32]=[131,9,163,201,153,45,35,222,189,104,139,224,185,96,72,135,226,88,106,68,10,156,60,72,82,28,53,49,227,146,232,171];
#[kani::ensures(|r| *r==REGISTRY_DEV)] #[kani::modifies()]
fn registry_packet()->[u8;32]{ registry_program_id() }
#[kani::proof_for_contract(registry_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn registry_devnet(){registry_packet();}
#[kani::ensures(|r| *r!=REGISTRY_DEV)] #[kani::modifies()]
fn registry_wrong_packet()->[u8;32]{ registry_program_id() }
#[kani::proof_for_contract(registry_wrong_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn registry_devnet_wrong(){registry_wrong_packet();}

#[kani::ensures(|r| r[0]==0)] #[kani::modifies()]
fn weak_array()->[u8;32]{[0;32]}
#[kani::proof_for_contract(weak_array)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn array_real(){weak_array();}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn array_real_caller(){assert_eq!(weak_array()[31],0);}
#[kani::proof] #[kani::unwind(35)] #[kani::stub_verified(weak_array)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn array_unimplied(){assert_eq!(weak_array()[31],0);}
#[kani::ensures(|r| r[0]!=0)] #[kani::modifies()]
fn array_invert_packet()->[u8;32]{[0;32]}
#[kani::proof_for_contract(array_invert_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn array_invert(){array_invert_packet();}
#[kani::modifies()] #[kani::ensures(|r| r[0]==0)]
fn array_write_packet(cell:&mut u8)->[u8;32]{*cell=1;[0;32]}
#[kani::proof_for_contract(array_write_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn array_modifies(){let mut cell=kani::any();array_write_packet(&mut cell);}
