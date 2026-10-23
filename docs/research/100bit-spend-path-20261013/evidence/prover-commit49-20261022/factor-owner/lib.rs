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

pub fn line(x:K,y:K)->[K;4] {[K::ONE,x,y,x.mul(y)]}
pub fn lines(mut out:[[K;4];5],d:usize,left:u8,x:K)->[[K;4];5] {
 if left==0 {out} else {
  let y=double(x);out[d]=line(x,y);let next=double(y);
  lines(out,d+1,left-1,next)
 }
}
pub fn circle_rows(x:K,y:K)->[[K;4];5] {
 let mut out=[[K::ZERO;4];5];out[0]=circle(x,y);
 lines(out,1,4,double(x))
}
}
