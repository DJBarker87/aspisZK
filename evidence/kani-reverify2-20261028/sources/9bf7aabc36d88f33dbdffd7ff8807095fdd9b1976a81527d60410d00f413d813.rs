#![feature(allocator_api)]
extern crate alloc;
mod KMX_stubs;
#[path="KMY_field.rs"] mod field;
use field::{QM31 as K,CM31,M31};
fn any64()->([K;64],[[u32;4];64]){let raw:[[u32;4];64]=kani::any();(raw.map(|r|K{c0:CM31{a:M31(r[0]),b:M31(r[1])},c1:CM31{a:M31(r[2]),b:M31(r[3])}}),raw)}
fn words(x:K)->[u32;4]{[x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0]}
#[kani::proof] #[kani::unwind(65)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn KMZ_iterator_suffix_gate(){
let (src,raw)=any64();let i:usize=kani::any();kani::assume(i<63);let mut it=src[i..].iter();it.next();let j:usize=kani::any();kani::assume(j<63-i);let l:usize=kani::any();kani::assume(l<4);assert_eq!(words(it.as_slice()[j])[l],raw[i+1+j][l] ^ 1u32);assert_eq!(it.len(),63-i);}
