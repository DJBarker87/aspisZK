#![allow(unexpected_cfgs)]
pub mod field;
use field::WideExact as E;
pub fn fill<const N:usize>(mut out:[E;N],x:E,p:E,i:usize,left:u8)->[E;N] {
 if left==0 {out} else {
  out[i]=p;
  if left==1 {out} else {fill(out,x,p.mul(x),i+1,left-1)}
 }
}
pub fn gamma(x:E)->[E;29] {fill([E::ZERO;29],x,E::ONE,0,29)}
pub fn kappa(x:E)->[E;7] {fill([E::ZERO;7],x,E::ONE,0,7)}
