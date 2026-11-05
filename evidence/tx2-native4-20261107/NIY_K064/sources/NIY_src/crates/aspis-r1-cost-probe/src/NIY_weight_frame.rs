use super::*;
use crate::{KMX_copy_nonoverlapping,KMX_copy_from_slice};
use aspis_core::field::{M31,CM31};
fn kw(q:K,j:usize)->u32{match j{0=>q.c0.a.0,1=>q.c0.b.0,2=>q.c1.a.0,_=>q.c1.b.0}}
fn reserve_check(){
 let mut v:alloc::vec::Vec<K>=alloc::vec::Vec::new();let reply=v.try_reserve_exact(64);
 assert_eq!(v.len(),0);
 match reply{Ok(())=>assert_eq!(v.capacity(),64^(if cfg!(NIY_invert){1}else{0})),Err(_)=>assert_eq!(v.capacity(),0)}
}
fn step_check(){
 let raw:[[u32;4];64]=kani::any();
 let mut weights:alloc::vec::Vec<K>=alloc::vec::Vec::from(raw.map(|x|K{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}}));
 let bytes:[u8;1768]=kani::any();let i:usize=kani::any();kani::assume(i<64);let observed:usize=kani::any();kani::assume(observed<64);let j:usize=kani::any();kani::assume(j<4);
 let pointer=weights.as_ptr();let capacity=weights.capacity();let before=kw(weights[observed],j);let at=712+16*i;let mut reader=Reader{bytes:&bytes,at};
 // One actual iterator next, one actual Reader::k, and the exact source assignment.
 let mut it=weights[i..].iter_mut();let out=it.next().unwrap();let reply=reader.k();
 if let Ok(value)=reply{*out=value;}
 assert_eq!(it.len(),63-i);drop(it);
 if cfg!(NIY_invert){weights[observed].c0.a.0^=1;weights[observed].c0.b.0^=1;weights[observed].c1.a.0^=1;weights[observed].c1.b.0^=1;}
 assert_eq!(weights.as_ptr(),pointer);assert_eq!(weights.len(),64);assert_eq!(weights.capacity(),capacity);assert_eq!(reader.at,at+16);
 match reply{Ok(value)=>assert_eq!(kw(weights[observed],j),if observed==i{kw(value,j)}else{before}),Err(error)=>{assert_eq!(error,Error::Checkpoint);assert_eq!(kw(weights[observed],j),before);}}
}
#[kani::proof]
#[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn reserve64(){reserve_check();}
#[kani::proof]
#[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn reserve64_renamed(){reserve_check();}
#[kani::proof]
#[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn weight_step(){step_check();}
#[kani::proof]
#[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn weight_step_renamed(){step_check();}
