//! Full public record frame on every returning Result, including errors.
use crate::*;
fn verify<const NATIVE:bool>(){
 let framed:[u8;3717]=kani::any();let root=[0u8;32];
 let i=(kani::any::<u16>()as usize)%3717;let original=framed[i];
 let prefix=r1_wire::np6_prefix(&root,&framed);
 let result=if NATIVE{shipped::call(&prefix)}else{reference::call(&prefix)};
 assert!(framed[i]==original);
 drop(result);
}
#[kani::proof] #[kani::unwind(32)] fn NP6_native_full_frame(){verify::<true>();}
#[kani::proof] #[kani::unwind(32)] fn NP6_reference_full_frame(){verify::<false>();}
