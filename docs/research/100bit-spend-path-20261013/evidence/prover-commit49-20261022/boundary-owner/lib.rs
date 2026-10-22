#![allow(unexpected_cfgs)]
pub mod field;
pub mod owned {
use super::field::M31;
pub fn sum(q:[u32;28],i:usize,left:u8,total:u64)->u64 {
 if left==0 {total} else {
  let next=total+u64::from(q[i]);
  sum(q,i+1,left-1,next)
 }
}
pub fn limb(q:[u32;28])->M31 {
 let initial=2*u64::from(q[0]);
 M31::reduce_u64(sum(q,1,27,initial))
}
}
