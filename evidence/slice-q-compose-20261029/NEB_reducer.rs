// Scratch-only contracts; the actual frozen scalar and wrapper bodies execute.
use super::*;
pub fn reference(x:u64)->u32 {
 let x=(x & P as u64).wrapping_add(x >> 31u32);
 let x=(x & P as u64).wrapping_add(x >> 31u32);
 let x=x as u32;
 if x>=P {x.wrapping_sub(P)}else{x}
}
pub fn reduce_post(x:u64,r:u32)->bool {
 if cfg!(NEB_wrong_reduce) {r!=reference(x)} else {r==reference(x)}
}
pub fn wrapper_post(x:u64,r:M31)->bool {
 if cfg!(NEB_wrong_wrapper) {r.0!=reference(x)} else {r.0==reference(x)}
}
#[kani::proof_for_contract(super::reduce_u64)]
fn reduce_contract() {let x:u64=kani::any();let _=super::reduce_u64(x);}
#[kani::proof_for_contract(M31::reduce_u64)]
#[kani::stub_verified(super::reduce_u64)]
fn wrapper_contract() {let x:u64=kani::any();let _=M31::reduce_u64(x);}

// U64 -> U32 return-shape fidelity controls. These are not source credit.
#[kani::ensures(|r| *r<=1)]
fn weak(x:u64)->u32 {(x & 1) as u32}
#[kani::proof_for_contract(weak)]
fn weak_contract() {let _=weak(kani::any());}
#[kani::proof]
fn real_body() {assert_eq!(weak(0),0);}
#[kani::proof] #[kani::stub_verified(weak)]
fn unimplied() {assert_eq!(weak(0),0);}
#[kani::modifies(x)] #[kani::ensures(|r| *r<=1)]
fn bad_frame(x:&mut u32,y:&mut u32)->u32 {let _=x;*y=y.wrapping_add(1);0}
#[kani::proof_for_contract(bad_frame)]
fn frame_control() {let mut x:u32=kani::any();let mut y:u32=kani::any();let _=bad_frame(&mut x,&mut y);}
