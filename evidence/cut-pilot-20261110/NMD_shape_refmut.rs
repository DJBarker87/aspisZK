use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[kani::modifies(cell)]
#[kani::ensures(|out| **out<=255)]
fn NMD_shape<'a>(cell:&'a core::cell::RefCell<u8>,_frame:&mut u8)->core::cell::RefMut<'a,u8> {cell.borrow_mut()}
#[kani::modifies(cell)]
#[kani::ensures(|out| !(**out<=255))]
fn NMD_inverse_shape<'a>(cell:&'a core::cell::RefCell<u8>,_frame:&mut u8)->core::cell::RefMut<'a,u8> {cell.borrow_mut()}
#[kani::modifies(cell)]
#[kani::ensures(|out| **out<=255)]
fn NMD_modifies_shape<'a>(cell:&'a core::cell::RefCell<u8>,frame:&mut u8)->core::cell::RefMut<'a,u8> {*frame=1;cell.borrow_mut()}
#[kani::proof_for_contract(NMD_shape)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMD_contract() {let cell=core::cell::RefCell::new(7u8);let mut frame=0;NMD_shape(&cell,&mut frame);}
#[kani::proof_for_contract(NMD_inverse_shape)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMD_inverse() {let cell=core::cell::RefCell::new(7u8);let mut frame=0;NMD_inverse_shape(&cell,&mut frame);}
#[kani::proof_for_contract(NMD_modifies_shape)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMD_modifies() {let cell=core::cell::RefCell::new(7u8);let mut frame=0;NMD_modifies_shape(&cell,&mut frame);}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMD_real() {let cell=core::cell::RefCell::new(7u8);let mut frame=0;let r=NMD_shape(&cell,&mut frame);assert_eq!(*r,7);}
#[kani::proof]
#[kani::stub_verified(NMD_shape)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMD_unimplied() {let cell=core::cell::RefCell::new(7u8);let mut frame=0;let r=NMD_shape(&cell,&mut frame);assert_eq!(*r,7);}
