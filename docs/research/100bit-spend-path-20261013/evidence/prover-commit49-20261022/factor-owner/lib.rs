#![allow(unexpected_cfgs)]
pub mod field;
pub mod factors {
use super::field::QM31 as K;
pub fn point(a:K,b:K)->[K;4] {
 [K::ONE.sub(a).mul(K::ONE.sub(b)),a.mul(K::ONE.sub(b)),K::ONE.sub(a).mul(b),a.mul(b)]
}
pub fn circle(x:K,y:K)->[K;4] { [K::ONE,y,x,x.mul(y)] }
pub fn double(x:K)->K {x.mul(x).add(x.mul(x)).sub(K::ONE)}
pub fn product(q:[K;5],i:usize,left:u8,s:K)->K {
 if left==0 {s} else {
  let next=s.mul(q[i]);
  product(q,i+1,left-1,next)
 }
}
}
