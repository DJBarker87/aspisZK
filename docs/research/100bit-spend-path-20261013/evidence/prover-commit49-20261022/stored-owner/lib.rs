#![allow(unexpected_cfgs)]
pub mod field;
pub mod stored {
use super::field::QM31 as K;
pub fn product(rows:[[K;4];5],j:usize,d:usize,left:u8,acc:K)->K {
 if left==0 {acc} else {
  let digit=(j>>((2*d) as u32))&3;
  let next=acc.mul(rows[d][digit]);product(rows,j,d+1,left-1,next)
 }
}
}
