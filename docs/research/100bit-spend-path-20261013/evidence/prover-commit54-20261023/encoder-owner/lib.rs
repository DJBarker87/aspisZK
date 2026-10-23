#![allow(unexpected_cfgs)]
pub mod field;
pub mod encoder54 {
use super::field::{M31,CM31,QM31,WideExact as E};
// Explicit finite collector; no iterator adapter occurs in the owner.
pub fn collect(c:&[E],stride:usize,offset:usize,i:usize,left:usize,mut out:Vec<E>)->Vec<E> {
 if left==0 {out} else {
  out.push(c[stride*i+offset]);
  collect(c,stride,offset,i+1,left-1,out)
 }
}
pub fn eval_rec(c:&[E],depth:usize,height:usize,nodes:&[M31;9])->E {
 if height==0 {return c[0];}
 let n=c.len()/2;
 let even=collect(c,2,0,0,n,Vec::new());
 let odd=collect(c,2,1,0,n,Vec::new());
 let a=eval_rec(&even,depth+1,height-1,nodes);
 let b=eval_rec(&odd,depth+1,height-1,nodes);
 a.add(E::from_qm31(QM31::from_cm31(CM31::from_m31(nodes[depth]))).mul(b))
}
pub fn channels(c:&[E;1024],nodes:&[M31;9])->[E;4] {
 let a=collect(c,4,0,0,256,Vec::new());
 let b=collect(c,4,1,0,256,Vec::new());
 let d=collect(c,4,2,0,256,Vec::new());
 let e=collect(c,4,3,0,256,Vec::new());
 [eval_rec(&a,0,8,nodes),eval_rec(&b,0,8,nodes),eval_rec(&d,0,8,nodes),eval_rec(&e,0,8,nodes)]
}
}
