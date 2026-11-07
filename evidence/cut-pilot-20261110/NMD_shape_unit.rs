use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[kani::modifies()]
#[kani::ensures(|out| true)]
fn NMD_shape(_frame:&mut u8)->Result<(),Error> {Ok(())}
#[kani::modifies()]
#[kani::ensures(|out| !(true))]
fn NMD_inverse_shape(_frame:&mut u8)->Result<(),Error> {Ok(())}
#[kani::modifies()]
#[kani::ensures(|out| true)]
fn NMD_modifies_shape(frame:&mut u8)->Result<(),Error> {*frame=1;Ok(())}
#[kani::proof_for_contract(NMD_shape)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMD_contract() {let mut frame=0;NMD_shape(&mut frame);}
#[kani::proof_for_contract(NMD_inverse_shape)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMD_inverse() {let mut frame=0;NMD_inverse_shape(&mut frame);}
#[kani::proof_for_contract(NMD_modifies_shape)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMD_modifies() {let mut frame=0;NMD_modifies_shape(&mut frame);}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMD_real() {let mut frame=0;let r=NMD_shape(&mut frame);assert!(r.is_ok());}
#[kani::proof]
#[kani::stub_verified(NMD_shape)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMD_unimplied() {let mut frame=0;let r=NMD_shape(&mut frame);assert!(r.is_ok());}
