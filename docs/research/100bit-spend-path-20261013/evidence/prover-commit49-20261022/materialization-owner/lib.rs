#![allow(unexpected_cfgs)]
pub mod field;
pub mod owned {
use super::field::{QM31 as K,WideExact as E};
pub fn cell(kp:[E;7],raw:[K;7],kind:usize,left:u8,sum:E)->E {
 if left==0 {sum} else {
  let next=sum.add(kp[kind].mul_qm31(raw[kind]));
  cell(kp,raw,kind+1,left-1,next)
 }
}
pub fn inactive(q:[E;1024],raw:[K;1024],j:usize,left:u16,sum:E)->E {
 if left==0 {sum} else {
  let next=sum.add(q[j].mul_qm31(raw[j]));
  inactive(q,raw,j+1,left-1,next)
 }
}
}

pub mod materialization {
use super::{field::{QM31 as K,WideExact as E},owned::cell};
pub fn fill(kp:[E;7],raw:[[K;7];1024],mut out:[E;1024],j:usize,left:u16)->[E;1024] {
 if left==0 {out} else {
  out[j]=cell(kp,raw[j],0,7,out[j]);fill(kp,raw,out,j+1,left-1)
 }
}
pub fn all(kp:[E;7],raw:[[K;7];1024])->[E;1024] {fill(kp,raw,[E::ZERO;1024],0,1024)}
}
