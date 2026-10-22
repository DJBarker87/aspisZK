#![allow(unexpected_cfgs)]
pub mod field;
use field::QM31 as K;
pub fn horner(q:[K;1024],offset:usize,left:u8,x:K,sum:K)->K {
 if left==0 {sum} else {
  let j=left-1;
  let next=sum.mul(x).add(q[offset+j as usize]);
  horner(q,offset,left-1,x,next)
 }
}
pub fn extra(q:[K;1024],a:K,b:K)->K {
 let left=horner(q,0,28,a,K::ZERO);
 let right=horner(q,28,28,b,K::ZERO);
 K::ZERO.add(left).add(right)
}
