use super::*;
use crate::{KMX_copy_nonoverlapping,KMX_copy_from_slice};
use aspis_core::field::{M31,CM31};
fn kw(k:K)->[u32;4]{[k.c0.a.0,k.c0.b.0,k.c1.a.0,k.c1.b.0]}
fn k(x:[u32;4])->K{K{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}}}
// M03: arbitrary native raw Vec pre-state; the selected weight is the read
// window from weights[index]. Log the REAL destination obtained by index_mut.
#[kani::proof]
#[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn pending_destination(){
 let before:[[u64;4];64]=kani::any();let words:[u32;4]=kani::any();
 let i:usize=kani::any();let j:usize=kani::any();kani::assume(i<64&&j<64);
 let mut raw=alloc::vec::Vec::with_capacity(64);for row in before{raw.push(row);}
 let ptr=raw.as_ptr();let cap=raw.capacity();let w=k(words);let mut index=i;
 let destination=&mut raw[index] as *mut [u64;4];
 // Keep the native index_mut write; the logged pointer is never dereferenced.
 raw[index]=[w.c0.a.0 as u64,w.c0.b.0 as u64,w.c1.a.0 as u64,w.c1.b.0 as u64];index+=1;
 let observed=if cfg!(NJR_bad_destination){&mut raw[(i+1)%64] as *mut [u64;4]}else{destination};
 assert_eq!(observed,ptr.wrapping_add(i) as *mut [u64;4]);
 assert_eq!(index,i+1);assert_eq!(raw.len(),64);assert_eq!(raw.capacity(),cap);assert_eq!(raw.as_ptr(),ptr);
 let mut expected=if i==j{[words[0] as u64,words[1] as u64,words[2] as u64,words[3] as u64]}else{before[j]};
 if cfg!(NJR_invert){expected[0]^=1;}
 assert_eq!(raw[j][0],expected[0]);assert_eq!(raw[j][1],expected[1]);assert_eq!(raw[j][2],expected[2]);assert_eq!(raw[j][3],expected[3]);
}
