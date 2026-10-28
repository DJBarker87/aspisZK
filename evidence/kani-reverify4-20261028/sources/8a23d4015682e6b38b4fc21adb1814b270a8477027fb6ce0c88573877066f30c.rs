#![feature(allocator_api)]
extern crate alloc;
mod KMX_stubs;
#[kani::proof] #[kani::unwind(1770)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn KND_transition() {
 let initial:[u8;340]=kani::any(); let bytes:[u8;4]=kani::any();
 let mut out=alloc::vec::Vec::with_capacity(1768);
 KMX_stubs::KMX_extend_from_slice(&mut out,&initial);
 assert_eq!(out.len(),340);assert_eq!(out.capacity(),1768);
 KMX_stubs::KMX_extend_from_slice(&mut out,&bytes);
 assert_eq!(out.len(),344);assert_eq!(out.capacity(),1768);
 let j:usize=kani::any();kani::assume(j<344);
 assert_eq!(out[j],(if j<340{initial[j]}else{bytes[j-340]}) ^ 0u8);
}
