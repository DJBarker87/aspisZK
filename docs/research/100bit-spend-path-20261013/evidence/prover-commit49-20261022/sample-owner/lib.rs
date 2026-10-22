#![allow(unexpected_cfgs)]
pub mod field;
pub mod owned {
use super::field;
use field::QM31 as K;
// Explicit oracle-result tape; native f calls are bound separately, in order.
pub fn sum(values:[K;512],start:usize,left:u16,total:K)->K {
 if left==0 { total } else {
  let next=total.add(values[start]);
  sum(values,start+1,left-1,next)
 }
}
pub fn tail(mut point:[K;10],round:usize,remaining:usize,assignment:usize,offset:usize,left:u8)->[K;10] {
 if left==0 {point} else {
  point[round+1+offset]=if (assignment>>((remaining-1-offset) as u32))&1==0 {K::ZERO} else {K::ONE};
  tail(point,round,remaining,assignment,offset+1,left-1)
 }
}
pub fn sample(mut point:[K;10],round:usize,sample:u32)->[K;10] {
 point[round]=K::from_cm31(field::CM31::from_m31(field::M31(sample)));
 point
}
// The final coefficient shift once the separately checked inverse returns.
pub fn shift(mut p:[K;28],original:K,eta_term0:K,inv:K,half:K)->[K;28] {
 let c=original.sub(eta_term0).mul(inv);
 p[0]=p[0].sub(c.mul(half));
 p[1]=p[1].add(c);
 p
}
}
