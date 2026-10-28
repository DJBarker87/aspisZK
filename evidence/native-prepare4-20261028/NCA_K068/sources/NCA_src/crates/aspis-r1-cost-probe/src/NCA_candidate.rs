use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[kani::proof]#[kani::unwind(2)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
fn NCA_append_first(){
 let source:u8=kani::any();let storage=Box::new([core::mem::MaybeUninit::<u8>::uninit();256]);let ptr=Box::into_raw(storage) as *mut u8;
 // Exact reached first root-append iteration. Live prefix is empty; all spare capacity uninitialized.
 let mut out=unsafe{Vec::from_raw_parts(ptr,0,256)};
 out.push(source);assert_eq!(out.len(),1);assert_eq!(out.capacity(),256);assert_eq!(out.as_ptr(),ptr);assert_eq!(out[0],source);
 kani::cover!(source==1,"nonzero first appended byte");
}
