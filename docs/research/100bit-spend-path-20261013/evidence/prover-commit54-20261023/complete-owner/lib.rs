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
pub fn phi_inverse(x:E,y:E,h:[E;4])->[E;4] {
 let [h0,h1,h2,h3]=h;
 let a=y.mul(h1);let b=x.mul(h2);let c=x.mul(y).mul(h3);
 [h0.add(a).add(b).add(c),h0.sub(a).add(b).sub(c),
 h0.sub(a).sub(b).add(c),h0.add(a).sub(b).sub(c)]
}
pub fn encode_with_nodes(c:&[E;1024],nodes:&[M31;9],x:E,y:E)->[E;4] {
 let h=channels(c,nodes);
 phi_inverse(x,y,h)
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
pub fn eval_at(c:&[field::WideExact],j:usize,height:usize)->field::WideExact {
 let nodes=nodes54::nodes(j);
 encoder54::eval_rec(c,0,height,&nodes)
}
pub fn encode_at(c:&[field::WideExact;1024],j:usize)->[field::WideExact;4] {
 let z=nodes54::point(j);
 let nodes=nodes54::nodes(j);
 let x=field::WideExact::from_qm31(field::QM31::from_cm31(field::CM31::from_m31(z.a)));
 let y=field::WideExact::from_qm31(field::QM31::from_cm31(field::CM31::from_m31(z.b)));
 encoder54::encode_with_nodes(c,&nodes,x,y)
}
pub mod leaves54 {
use super::field::WideExact as E;
pub fn folded_values(c:&[E;256],v:usize)->[E;4] {
 [super::eval_at(c,4*v,8),super::eval_at(c,4*v+1,8),
  super::eval_at(c,4*v+2,8),super::eval_at(c,4*v+3,8)]
}
pub fn column(mut out:[[E;29];4],h:&[E;4],l:usize,s:usize,left:u8)->[[E;29];4] {
 if left==0 {out} else {
  out[s][l]=h[s];
  column(out,h,l,s+1,left-1)
 }
}
pub fn opened(c:&[[E;1024];29],j:usize,l:usize,left:u8,out:[[E;29];4])->[[E;29];4] {
 if left==0 {out} else {
  let h=super::encode_at(&c[l],j);
  let out=column(out,&h,l,0,4);
  opened(c,j,l+1,left-1,out)
 }
}
pub fn opened_values(c:&[[E;1024];29],j:usize)->[[E;29];4] {
 opened(c,j,0,29,[[E::ZERO;29];4])
}
}
