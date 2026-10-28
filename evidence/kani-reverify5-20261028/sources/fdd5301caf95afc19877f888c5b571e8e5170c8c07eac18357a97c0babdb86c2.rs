#![feature(allocator_api)]
extern crate alloc;
mod KMX_stubs;
#[kani::proof] #[kani::unwind(1770)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn KND_transition() {
 let initial:[u8;1768]=kani::any(); let bytes:[u8;8]=kani::any();
 let mut out=alloc::vec::Vec::from(initial);out.truncate(8);
 assert_eq!(out.len(),8);assert_eq!(out.capacity(),1768);
 KMX_stubs::KMX_extend_from_slice(&mut out,&bytes);
 assert_eq!(out.len(),16);assert_eq!(out.capacity(),1768);
 for j in 0..16 {
  assert_eq!(out[j],(if j<8{initial[j]}else{bytes[j-8]}) ^ 0u8);
 }
}
