#![feature(allocator_api)]
extern crate alloc;
mod KMX_stubs;
#[path="KMY_field.rs"] mod field;
use field::{QM31 as K,CM31,M31};
#[kani::proof] #[kani::unwind(1769)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn KNA_draft_append16(){
let initial:[u8;1736]=kani::any();let source:[u8;16]=kani::any();let len:usize=kani::any();kani::assume(len<=1720);
 let cap_in=len;let mut out=alloc::vec::Vec::with_capacity(cap_in);
 KMX_stubs::KMX_extend_from_slice(&mut out,&initial[..len]);
 assert_eq!(out.len(),len);assert_eq!(out.capacity(),cap_in);
 if len>0{let p:usize=kani::any();kani::assume(p<len);assert_eq!(out[p],initial[p]);}
 KMX_stubs::KMX_extend_from_slice(&mut out,&source);
 assert_eq!(out.len(),len+16);
 assert_eq!(out.capacity(),if cap_in<len+16{core::cmp::max(8,core::cmp::max(2*cap_in,len+16))}else{cap_in});
 let j:usize=kani::any();kani::assume(j<out.len() && 884<=j && j<1768);
 assert_eq!(out[j],(if j<len{initial[j]}else{source[j-len]}) ^ 1u8);
}
