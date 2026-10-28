#![feature(allocator_api)]
extern crate alloc;
mod KMX_stubs;
#[path="KMY_field.rs"] mod field;
use field::{QM31 as K,CM31,M31};
fn KNA_put_k(out:&mut alloc::vec::Vec<u8>,x:K){let mut b=[0;16];x.write_le_bytes(&mut b);KMX_stubs::KMX_extend_from_slice(out,&b);}
#[kani::proof] #[kani::unwind(1769)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(alloc::alloc::realloc,crate::KMX_stubs::KMX_realloc)]
fn KNA_draft_selected(){
 let raw:[u32;4]=kani::any();let selected=K{c0:CM31{a:M31(raw[0]),b:M31(raw[1])},c1:CM31{a:M31(raw[2]),b:M31(raw[3])}};let shared=&selected;
 let i:usize=kani::any();kani::assume(i<64);let len=712+16*i;
 let initial:[u8;1736]=kani::any();let mut out=KMX_stubs::KMX_to_vec(&initial[..len]);
 let &x=shared;KNA_put_k(&mut out,x);assert_eq!(out.len(),len+16);
 let j:usize=kani::any();kani::assume(j<out.len() && 0<=j && j<884);
 assert_eq!(out[j],(if j<len{initial[j]}else{raw[(j-len)/4].to_le_bytes()[(j-len)%4]}) ^ 1u8);
}
