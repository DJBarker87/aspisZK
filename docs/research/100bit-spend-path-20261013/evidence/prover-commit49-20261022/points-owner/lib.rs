#![allow(unexpected_cfgs)]
pub mod field;
pub mod points {
use super::field::QM31 as K;
pub fn successor(p:[K;10],mut out:[K;10],left:u8,carry:K)->[K;10] {
 if left==0 {out} else {
  let coordinate=(left-1) as usize;
  let bit=p[coordinate];let bc=bit.mul(carry);
  out[coordinate]=bit.add(carry).sub(bc.add(bc));
  successor(p,out,left-1,bc)
 }
}
pub fn absorption(mut p:[K;10])->[K;10] {
 p[7]=K::ONE.sub(p[7]);
 p[6]=K::ONE.sub(p[6]);p
}
pub fn all(p:[K;10])->[[K;10];3] {
 [p,successor(p,p,10,K::ONE),absorption(p)]
}
}
