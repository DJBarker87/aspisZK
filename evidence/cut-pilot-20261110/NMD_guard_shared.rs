use super::*;
use core::cell::{RefCell,Ref,RefMut};
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));

fn NMD_guard(cell:&RefCell<u8>)->Ref<'_,u8>{cell.borrow()}
// The only write footprint of this minimal body is the real borrow token.
// It has no allocator or ambient state; no omitted footprint is claimed.
fn NMD_construct_cut(cell:&RefCell<u8>)->Ref<'_,u8>{cell.borrow()}
fn NMD_construct_bad_value(cell:&RefCell<u8>)->Ref<'_,u8>{cell.replace(kani::any());cell.borrow()}
fn NMD_construct_bad_token(cell:&RefCell<u8>)->Ref<'_,u8>{let leaked=cell.borrow();core::mem::forget(leaked);cell.borrow()}
fn NMD_test<const INVERSE:bool>() {
 let value:u8=kani::any();let cell=RefCell::new(value);
 let guard=NMD_guard(&cell);
 let exact=*guard==value && (&*guard as *const u8)==cell.as_ptr();
 assert!(exact!=INVERSE);
 drop(guard);
 assert!(cell.try_borrow_mut().is_ok(),"original cell's token is released");
}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMD_guard_real(){NMD_test::<false>();}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(NMD_guard,NMD_construct_cut)]
fn NMD_guard_cut(){NMD_test::<false>();}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(NMD_guard,NMD_construct_bad_value)]
fn NMD_guard_bad_value(){NMD_test::<false>();}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(NMD_guard,NMD_construct_bad_token)]
fn NMD_guard_bad_token(){NMD_test::<false>();}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(NMD_guard,NMD_construct_cut)]
fn NMD_guard_inverse(){NMD_test::<true>();}
#[kani::proof]#[kani::unwind(4)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMD_copy_control(){let src:[u8;2]=kani::any();let mut dst=[0u8;2];dst.copy_from_slice(&src);assert!(dst[1]!=src[1]);}
