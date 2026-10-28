#![feature(allocator_api)]
extern crate alloc;
mod KMX_stubs;
#[path="KMY_field.rs"] mod field;
use field::{QM31 as K,CM31,M31};
fn any64()->([K;64],[[u32;4];64]){let raw:[[u32;4];64]=kani::any();(raw.map(|r|K{c0:CM31{a:M31(r[0]),b:M31(r[1])},c1:CM31{a:M31(r[2]),b:M31(r[3])}}),raw)}
fn words(x:K)->[u32;4]{[x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0]}
#[kani::proof] #[kani::unwind(1769)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn KMZ_retained1736_actual_gate(){
let initial:[u8;1736]=kani::any();let source:[u8;32]=kani::any();let mut out:alloc::vec::Vec<u8>=alloc::vec::Vec::from(initial);let p:usize=kani::any();kani::assume(p<1736);assert_eq!(out[p],initial[p]);KMX_stubs::KMX_extend_from_slice(&mut out,&source);assert_eq!(out.len(),1768);assert_eq!(out.capacity(),3472);let j:usize=kani::any();kani::assume(j<1768);assert_eq!(out[j],(if j<1736{initial[j]}else{source[j-1736]}) ^ 0u8);}
