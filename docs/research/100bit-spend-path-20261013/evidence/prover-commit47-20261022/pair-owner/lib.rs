#![allow(unexpected_cfgs)]
pub mod field;
use field::WideExact as E;
pub fn pairs(q:[E;1024],basis:[E;512],i:usize,left:u16,p0:E,p1:E)->(E,E) {
 if left==0 {(p0,p1)} else {
  let n=basis[i];
  let p0=p0.add(q[2*i].mul(n));
  let p1=p1.add(q[2*i+1].mul(n));
  pairs(q,basis,i+1,left-1,p0,p1)
 }
}
pub fn evaluate(q:[E;1024],basis:[E;512],y:E)->E {
 let (p0,p1)=pairs(q,basis,0,512,E::ZERO,E::ZERO);
 p0.add(y.mul(p1))
}
