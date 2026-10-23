#![allow(unexpected_cfgs)]
pub mod field;
pub mod gamma53 {
use super::field::WideExact as E;
pub fn cell(coefficients:&[[E;1024];29],powers:&[E;29],j:usize,lane:usize,left:u8,acc:E)->E {
 if left==0 {acc} else {
  cell(coefficients,powers,j,lane+1,left-1,acc.add(powers[lane].mul(coefficients[lane][j])))
 }
}
pub fn fill(coefficients:&[[E;1024];29],powers:&[E;29],mut out:[E;1024],j:usize,left:u16)->[E;1024] {
 if left==0 {out} else {
  out[j]=cell(coefficients,powers,j,0,29,E::ZERO);
  fill(coefficients,powers,out,j+1,left-1)
 }
}
pub fn all(coefficients:&[[E;1024];29],powers:&[E;29])->[E;1024] {
 fill(coefficients,powers,[E::ZERO;1024],0,1024)
}
}
