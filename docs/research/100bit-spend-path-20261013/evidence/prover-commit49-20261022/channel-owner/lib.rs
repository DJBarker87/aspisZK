#![allow(unexpected_cfgs)]
pub mod field;
pub mod channels {
use super::field::M31;
pub fn sum(a:[M31;3],b:[M31;3],i:usize,left:u8,total:u64)->u64 {
 if left==0 {total} else {
  let product=u64::from(a[i].0).wrapping_mul(u64::from(b[i].0));
  let next=total.wrapping_add(product);sum(a,b,i+1,left-1,next)
 }
}
pub fn dot3(a:[M31;3],b:[M31;3])->M31 {M31::reduce_u64(sum(a,b,0,3,0))}
}
