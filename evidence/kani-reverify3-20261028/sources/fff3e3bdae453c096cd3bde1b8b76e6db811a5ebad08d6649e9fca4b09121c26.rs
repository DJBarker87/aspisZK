#![feature(allocator_api)]
extern crate alloc;
mod KMX_stubs;
#[path="KMY_field.rs"] mod field;
use field::{QM31 as K,CM31,M31};
#[kani::proof] #[kani::unwind(1769)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn KNA_body_160_320(){let initial:[u8;1736]=kani::any();let source:[u8;32]=kani::any();
let mut out=alloc::vec::Vec::from(initial);
KMX_stubs::KMX_extend_from_slice(&mut out,&source);
assert_eq!(out.len(),1768);assert_eq!(out.capacity(),3472);
let j:usize=kani::any();kani::assume(160<=j && j<320);
assert_eq!(out[j],(if j<1736{initial[j]}else{source[j-1736]})^0u8);
}
