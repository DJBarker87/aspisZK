#![allow(unexpected_cfgs)]
pub mod field;
pub mod scalar;
pub mod generic54 {
use super::field::M31;
use super::scalar::CodeField;
// Explicit finite collector; no iterator adapter occurs in the owner.
pub fn collect<E:CodeField>(c:&[E],stride:usize,offset:usize,i:usize,left:usize,mut out:Vec<E>)->Vec<E> {
 if left==0 {out} else {
  out.push(c[stride*i+offset]);
  collect(c,stride,offset,i+1,left-1,out)
 }
}
pub fn eval_rec<E:CodeField>(c:&[E],depth:usize,height:usize,nodes:&[M31;9])->E {
 if height==0 {return c[0];}
 let n=c.len()/2;
 let even=collect(c,2,0,0,n,Vec::new());
 let odd=collect(c,2,1,0,n,Vec::new());
 let a=eval_rec(&even,depth+1,height-1,nodes);
 let b=eval_rec(&odd,depth+1,height-1,nodes);
 a.add(E::from_m31(nodes[depth]).mul(b))
}
pub fn channels<E:CodeField>(c:&[E;1024],nodes:&[M31;9])->[E;4] {
 let a=collect(c,4,0,0,256,Vec::new());
 let b=collect(c,4,1,0,256,Vec::new());
 let d=collect(c,4,2,0,256,Vec::new());
 let e=collect(c,4,3,0,256,Vec::new());
 [eval_rec(&a,0,8,nodes),eval_rec(&b,0,8,nodes),eval_rec(&d,0,8,nodes),eval_rec(&e,0,8,nodes)]
}
pub fn phi_inverse<E:CodeField>(x:E,y:E,h:[E;4])->[E;4] {
 let [h0,h1,h2,h3]=h;
 let a=y.mul(h1);let b=x.mul(h2);let c=x.mul(y).mul(h3);
 [h0.add(a).add(b).add(c),h0.sub(a).add(b).sub(c),
 h0.sub(a).sub(b).add(c),h0.add(a).sub(b).sub(c)]
}
pub fn encode_with_nodes<E:CodeField>(c:&[E;1024],nodes:&[M31;9],x:E,y:E)->[E;4] {
 let h=channels(c,nodes);
 phi_inverse(x,y,h)
}
pub fn m31_channels(c:&[super::field::M31;1024],n:&[M31;9])->[super::field::M31;4] {channels(c,n)}
pub fn qm31_channels(c:&[super::field::QM31;1024],n:&[M31;9])->[super::field::QM31;4] {channels(c,n)}
pub fn m31_phi(x:M31,y:M31,h:[M31;4])->[M31;4] {phi_inverse(x,y,h)}
pub fn qm31_phi(x:super::field::QM31,y:super::field::QM31,h:[super::field::QM31;4])->[super::field::QM31;4] {phi_inverse(x,y,h)}
pub fn eval_at<E:CodeField>(c:&[E],j:usize,height:usize)->E {
 let nodes=super::nodes54::nodes(j);
 eval_rec(c,0,height,&nodes)
}
pub fn encode_at<E:CodeField>(c:&[E;1024],j:usize)->[E;4] {
 let z=super::nodes54::point(j);
 let nodes=super::nodes54::nodes(j);
 encode_with_nodes(c,&nodes,E::from_m31(z.a),E::from_m31(z.b))
}
}
pub mod nodes54 {
use super::field::{M31,CM31};
pub fn reverse(width:u8,value:usize)->usize {
 if width==0 {0} else {
  let w=width-1;
  (value%2)*(1usize<<(w as u32))+reverse(w,value/2)
 }
}
pub fn pow(base:CM31,exp:u64,acc:CM31)->CM31 {
 if exp==0 {acc} else {
  let next=if exp%2==1 {acc.mul(base)} else {acc};
  pow(base.mul(base),exp/2,next)
 }
}
pub fn tcheb(x:M31)->M31 {x.mul(x).double().sub(M31::ONE)}
pub fn repeat(x:M31,left:u8)->M31 {
 if left==0 {x} else {repeat(tcheb(x),left-1)}
}
pub fn point(j:usize)->CM31 {
 let r=reverse(18,j);
 pow(CM31::new(M31(2),M31(1268011823)),1024+4096*r as u64,CM31::ONE)
}
pub fn node(j:usize,depth:u8)->M31 {
 let step=1usize<<(depth as u32);
 let aligned=(j/step)*step;
 repeat(point(aligned).a,depth+1)
}
pub fn fill(j:usize,d:u8,left:u8,mut out:[M31;9])->[M31;9] {
 if left==0 {out} else {
  out[d as usize]=node(j,d);
  fill(j,d+1,left-1,out)
 }
}
pub fn nodes(j:usize)->[M31;9] {fill(j,0,9,[M31::ZERO;9])}
}

pub mod guarded55 {
use super::{scalar::CodeField,field::M31,generic54::collect};
// Fuel is a proof witness. The native length guard is retained verbatim;
// the exhaustion assertion is proved unreachable for the caller's lengths.
pub fn eval_rec<T:CodeField>(c:&[T],depth:usize,height:usize,nodes:&[M31;9])->T {
 if c.len()==1 {return c[0];}
 assert!(height>0);
 let n=c.len()/2;
 let even=collect(c,2,0,0,n,Vec::new());
 let odd=collect(c,2,1,0,n,Vec::new());
 let a=eval_rec(&even,depth+1,height-1,nodes);
 let b=eval_rec(&odd,depth+1,height-1,nodes);
 a.add(T::from_m31(nodes[depth]).mul(b))
}
}

pub mod nodes55 {
use super::field::CM31;
pub fn pow(base:CM31,exp:u64,acc:CM31)->CM31 {
 if exp==0 {acc} else {
  let next=if exp&1==1 {acc.mul(base)} else {acc};
  pow(base.square(),exp>>1u32,next)
 }
}
}
