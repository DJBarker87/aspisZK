#![allow(unexpected_cfgs)]
pub mod field;
use field::WideExact as E;
pub fn fill(mut out:[E;512],j:usize,left:u16,width:usize,factor:E)->[E;512] {
 if left==0 {out} else {
  out[width+j]=out[j].mul(factor);
  fill(out,j+1,left-1,width,factor)
 }
}
pub fn stages(out:[E;512],left:u8,width:usize,factor:E)->[E;512] {
 if left==0 {out} else {
  let out=fill(out,0,width as u16,width,factor);
  let square=factor.mul(factor);
  stages(out,left-1,width*2,square.add(square).sub(E::ONE))
 }
}
pub fn values(x:E)->[E;512] {stages([E::ONE;512],9,1,x)}
