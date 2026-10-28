#![feature(allocator_api)]
extern crate alloc;
mod KMX_stubs;
#[kani::proof] #[kani::unwind(1770)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn KND_transition() {
 let initial:[u8;1768]=kani::any(); let bytes:[u8;16]=kani::any();
 let mut out=alloc::vec::Vec::from(initial);out.truncate(808);
 assert_eq!(out.len(),808);assert_eq!(out.capacity(),1768);
 KMX_stubs::KMX_extend_from_slice(&mut out,&bytes);
 assert_eq!(out.len(),824);assert_eq!(out.capacity(),1768);
 for j in 0..824 {
  assert_eq!(out[j],(if j<808{initial[j]}else{bytes[j-808]}) ^ 1u8);
 }
}
