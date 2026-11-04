#![no_std]
extern crate alloc;
use alloc::vec::Vec;
// hashv is an external runtime call. Its complete reply is the explicit
// observation supplied to this safe reference; no SHA computation is modeled.
pub fn digest_ref(_parts:&[&[u8]],reply:[u8;32])->[u8;32]{reply}
#[derive(Clone,Copy)]
pub struct Q{pub limbs:[u32;4]}
pub fn finish_step_ref(weights:&mut[Q],index:usize,value:Q){weights[index]=value;}
pub fn filled_ref(n:usize,value:Q,reserved:bool)->Result<Vec<Q>,()>{
 if !reserved{return Err(());}
 let mut out=Vec::new();out.resize(n,value);Ok(out)
}
