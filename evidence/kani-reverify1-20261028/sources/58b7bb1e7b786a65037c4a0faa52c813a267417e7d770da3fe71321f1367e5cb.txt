#![feature(allocator_api)]
extern crate alloc;
mod KMX_stubs;
#[kani::proof]
#[kani::unwind(17)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
fn KMY_expand_copy_window() {
 let source:[u8;16]=kani::any();let mut dst:[u8;96]=kani::any();
 let at:usize=kani::any();kani::assume(at<=80);
 let j:usize=kani::any();kani::assume(j<96);let old=dst[j];
 KMX_stubs::KMX_copy_from_slice(&mut dst[at..at+16],&source);
 assert_eq!(dst[j],if at<=j && j<at+16 {source[j-at]} else {old});
}
#[kani::proof]
#[kani::unwind(17)]
fn KMY_expand_zero_window() {
 let mut dst:[u8;96]=kani::any();let at:usize=kani::any();kani::assume(at<=80);
 let j:usize=kani::any();kani::assume(j<96);let old=dst[j];
 dst[at..at+16].fill(0);
 assert_eq!(dst[j],if at<=j && j<at+16 {0} else {old});
}

#[kani::proof]
fn KMY_expand_metadata() {
 let mut backing:[u8;96]=kani::any();let slot:usize=kani::any();kani::assume(slot<3);
 let at=32*slot;let end:usize=kani::any();kani::assume(at+32<=end && end<=96);
 let base=backing.as_mut_ptr();let window=&mut backing[..end][at..at+32];
 assert!(core::ptr::eq(window.as_ptr(),base.wrapping_add(at)));
 assert_eq!(window.len(),32);assert_eq!(16usize%16,0);assert_eq!(window.len(),2*16);
 assert!(core::ptr::eq(backing.as_ptr(),base));
}
