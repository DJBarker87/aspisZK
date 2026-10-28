#![feature(allocator_api)]
extern crate alloc;
mod KMX_stubs;
#[path="KMY_field.rs"] mod field;
use field::{QM31 as K,CM31,M31};
fn any64()->([K;64],[[u32;4];64]){let raw:[[u32;4];64]=kani::any();(raw.map(|r|K{c0:CM31{a:M31(r[0]),b:M31(r[1])},c1:CM31{a:M31(r[2]),b:M31(r[3])}}),raw)}
fn words(x:K)->[u32;4]{[x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0]}
#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn KMZ_query_last_gate(){
let initial:[u8;1736]=kani::any();let source:[u8;4]=kani::any();let i:usize=kani::any();kani::assume(17<=i && i<22);let len=64+4*i;
 let cap_in=256;let mut out=alloc::vec::Vec::with_capacity(cap_in);
 KMX_stubs::KMX_extend_from_slice(&mut out,&initial[..len]);
 assert_eq!(out.len(),len);assert_eq!(out.capacity(),cap_in);
 if len>0{let p:usize=kani::any();kani::assume(p<len);assert_eq!(out[p],initial[p]);}
 KMX_stubs::KMX_extend_from_slice(&mut out,&source);
 assert_eq!(out.len(),len+4);
 assert_eq!(out.capacity(),if cap_in<len+4{core::cmp::max(8,core::cmp::max(2*cap_in,len+4))}else{cap_in});
 let j:usize=kani::any();kani::assume(j<out.len());
 assert_eq!(out[j],(if j<len{initial[j]}else{source[j-len]}) ^ 1u8);
}
