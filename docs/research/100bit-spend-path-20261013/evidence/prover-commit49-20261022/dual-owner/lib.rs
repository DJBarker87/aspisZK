#![allow(unexpected_cfgs)]
pub mod field;
use field::{WideExact as E,M31};
pub fn scalar(x:E,y:M31)->E {x.mul_m31(y)}
pub fn dual_cell(h:[E;4],alpha:E)->E {
 h[0].add(alpha.mul(h[3].add(alpha.mul(h[2].add(alpha.mul(h[1])))))).mul_m31(M31(536870912))
}
pub fn round_step(q:[E;1024],w:[E;1024],mut out:[E;7],d:usize,s:usize,t:usize)->[E;7] {
 let permutation=[0usize,3,2,1];let k=s+permutation[t];
 out[k]=out[k].add(q[4*d+s].mul(w[4*d+t]));out
}
pub fn roots(x:E,y:M31,h:[E;4],q:[E;1024],w:[E;1024],out:[E;7],d:usize,s:usize,t:usize)->(E,E,[E;7]) {
 (scalar(x,y),dual_cell(h,x),round_step(q,w,out,d,s,t))
}

pub mod dual {
use super::{field::WideExact as E,dual_cell};
pub fn first(q:[E;1024],a:E,mut out:[E;256],i:usize,left:u16)->[E;256] {
 if left==0 {out} else {
  let h=[q[4*i],q[4*i+1],q[4*i+2],q[4*i+3]];
  out[i]=dual_cell(h,a);first(q,a,out,i+1,left-1)
 }
}
pub fn all(q:[E;1024],a:E)->[E;256] {first(q,a,[E::ZERO;256],0,256)}
}
