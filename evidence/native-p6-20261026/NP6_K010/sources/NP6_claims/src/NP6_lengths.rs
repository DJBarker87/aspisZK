use crate::*;
// Whole source comparison, all safe short-record lengths before the first row.
#[kani::proof]
#[kani::unwind(32)]
fn NP6_first_length_rejection(){
 let framed:[u8;932]=kani::any();
 let length=5+(kani::any::<u16>() as usize)%928;
 let root=[0u8;32];
 let prefix=r1_wire::np6_prefix(&root,&framed[..length]);
 let a=shipped::call(&prefix);let b=reference::call(&prefix);
 match a {Err(e)=>assert!(e==r1_wire::Error::Length{row:25}),Ok(_)=>assert!(false)}
 match b {Err(e)=>assert!(e==r1_wire::Error::Length{row:25}),Ok(_)=>assert!(false)}
}
