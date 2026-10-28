#![feature(allocator_api)]
extern crate alloc;
mod KMX_stubs;
#[path="KMY_field.rs"] mod field;
use field::{QM31 as K,CM31,M31};
#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn KNA_query_256_128_148(){let initial:[u8;256]=kani::any();let source:[u8;4]=kani::any();
let i:usize=kani::any();kani::assume(17<=i && i<22);let len=64+4*i;
let mut out=alloc::vec::Vec::from(initial);out.truncate(len);
assert_eq!(out.len(),len);assert_eq!(out.capacity(),256);
let j:usize=kani::any();kani::assume(128<=j && j<148 && j<len);assert_eq!(out[j],initial[j]);
KMX_stubs::KMX_extend_from_slice(&mut out,&source);
assert_eq!(out.len(),len+4);assert_eq!(out.capacity(),256);
assert_eq!(out[j],(if j<len{initial[j]}else{source[j-len]})^0u8);
}
