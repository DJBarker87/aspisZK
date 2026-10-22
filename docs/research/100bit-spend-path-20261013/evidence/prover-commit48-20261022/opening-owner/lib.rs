#![allow(unexpected_cfgs)]
pub mod field;
use field::WideExact as E;
// One output q[j], with the selected column gathered separately. No callback,
// mutable borrow, std iterator, or source-level while loop is extracted.
pub fn mix(coefficients:[E;29],powers:[E;29],i:usize,left:u8,sum:E)->E {
 if left==0 {sum} else {
  let next=sum.add(powers[i].mul(coefficients[i]));
  mix(coefficients,powers,i+1,left-1,next)
 }
}
pub fn fold_cell(h:[E;4],alpha:E)->E {
 h[0].add(alpha.mul(h[1].add(alpha.mul(h[2].add(alpha.mul(h[3]))))))
}
pub fn fold_first(q:[E;1024],alpha:E,mut out:[E;256],i:usize,left:u16)->[E;256] {
 if left==0 {out} else {
  out[i]=fold_cell([q[4*i],q[4*i+1],q[4*i+2],q[4*i+3]],alpha);
  fold_first(q,alpha,out,i+1,left-1)
 }
}
pub fn fold_second(q:[E;256],alpha:E,mut out:[E;64],i:usize,left:u8)->[E;64] {
 if left==0 {out} else {
  out[i]=fold_cell([q[4*i],q[4*i+1],q[4*i+2],q[4*i+3]],alpha);
  fold_second(q,alpha,out,i+1,left-1)
 }
}
