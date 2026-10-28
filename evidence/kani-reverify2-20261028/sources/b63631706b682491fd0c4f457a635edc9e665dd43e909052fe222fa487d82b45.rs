#![feature(allocator_api)]
extern crate alloc;
mod KMX_stubs;
#[path="KMY_field.rs"] mod field;
use field::{QM31 as K,CM31,M31};
fn any64()->([K;64],[[u32;4];64]){let raw:[[u32;4];64]=kani::any();(raw.map(|r|K{c0:CM31{a:M31(r[0]),b:M31(r[1])},c1:CM31{a:M31(r[2]),b:M31(r[3])}}),raw)}
fn words(x:K)->[u32;4]{[x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0]}
#[kani::proof] #[kani::unwind(67)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn KMZ_typed_exterior_gate(){
let (src,_)=any64();let (edge,_)=any64();let mut dst=[K::ZERO;66];dst[0]=edge[0];dst[65]=edge[1];let j=if kani::any(){0}else{65};let old=dst[j];KMX_stubs::KMX_copy_from_slice(&mut dst[1..65],&src);let l:usize=kani::any();kani::assume(l<4);assert_eq!(words(dst[j])[l],words(old)[l] ^ 1u32);}
