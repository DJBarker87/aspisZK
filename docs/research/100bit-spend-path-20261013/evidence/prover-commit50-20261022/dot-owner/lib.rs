#![allow(unexpected_cfgs)]
pub mod field;
pub mod dot50 {
use super::field::{QM31 as K,CM31 as C,M31};
pub fn prepare_c(x:C)->[M31;3] {[x.a,x.b,x.a.add(x.b)]}
pub fn prepare(x:K)->[[M31;3];3] {
 let z=x.c0.add(x.c1);
 [prepare_c(x.c0),prepare_c(x.c1),prepare_c(z)]
}
}

pub mod channels {
use super::field::M31;
pub fn sum(a:[M31;3],b:[M31;3],i:usize,left:u8,total:u64)->u64 {
 if left==0 {total} else {
  let product=u64::from(a[i].0).wrapping_mul(u64::from(b[i].0));
  let next=total.wrapping_add(product);sum(a,b,i+1,left-1,next)
 }
}
pub fn dot3(a:[M31;3],b:[M31;3])->M31 {M31::reduce_u64(sum(a,b,0,3,0))}
}

pub mod totals50 {
use super::{field::M31,channels};
pub fn channel(a:[[[M31;3];3];3],b:[[[M31;3];3];3],c:usize,h:usize)->u64 {
 channels::sum([a[0][c][h],a[1][c][h],a[2][c][h]],
               [b[0][c][h],b[1][c][h],b[2][c][h]],0,3,0)
}
pub fn all(a:[[[M31;3];3];3],b:[[[M31;3];3];3])->[[u64;3];3] {
 [ [channel(a,b,0,0),channel(a,b,0,1),channel(a,b,0,2)],
   [channel(a,b,1,0),channel(a,b,1,1),channel(a,b,1,2)],
   [channel(a,b,2,0),channel(a,b,2,1),channel(a,b,2,2)] ]
}
}

pub mod reconstruction {
use super::field::{QM31 as K,CM31 as C,M31};
pub fn cm(s:[u64;3])->C {
 let m0=M31::reduce_u64(s[0]);let m1=M31::reduce_u64(s[1]);let m2=M31::reduce_u64(s[2]);
 C{a:m0.sub(m1),b:m2.sub(m0).sub(m1)}
}
pub fn mul_r(x:C)->C {
 let two_a=x.a.double();let real=two_a.sub(x.b);
 let two_b=x.b.double();let imag=x.a.add(two_b);
 C{a:real,b:imag}
}
pub fn q(s:[[u64;3];3])->K {
 let m0=cm(s[0]);let m1=cm(s[1]);let m2=cm(s[2]);
 K{c0:m0.add(mul_r(m1)),c1:m2.sub(m0).sub(m1)}
}
}

pub mod run50 {
use super::{field::QM31 as K,dot50,totals50,reconstruction};
pub fn prepare3(x:[K;3])->[[[super::field::M31;3];3];3] {
 [dot50::prepare(x[0]),dot50::prepare(x[1]),dot50::prepare(x[2])]
}
pub fn run(x:[K;3],y:[K;3])->K {
 let a=prepare3(x);let b=prepare3(y);
 reconstruction::q(totals50::all(a,b))
}
}

pub mod prepared50 {
use super::field::{M31,CM31 as C,QM31 as K};
pub fn prepare(x:K)->[[M31;3];3] {
 let a=super::dot50::prepare_c(x.c0);
 let b=super::dot50::prepare_c(x.c1);
 let c=super::dot50::prepare_c(x.c0.add(x.c1));
 [a,b,c]
}
pub fn cm(left:[M31;3],right:C)->C {
 let m0=left[0].mul(right.a);let m1=left[1].mul(right.b);
 let m2=left[2].mul(right.a.add(right.b));
 C{a:m0.sub(m1),b:m2.sub(m0).sub(m1)}
}
pub fn combine(m0:C,m1:C,m2:C)->K {
 K{c0:m0.add(super::reconstruction::mul_r(m1)),c1:m2.sub(m0).sub(m1)}
}
pub fn mul(left:[[M31;3];3],right:K)->K {
 let m0=cm(left[0],right.c0);let m1=cm(left[1],right.c1);
 let m2=cm(left[2],right.c0.add(right.c1));
 combine(m0,m1,m2)
}
}

pub mod eval50 {
use super::{field::{QM31 as K,M31},run50,prepared50};
pub fn block(p:[K;28],powers:[K;3],j:usize)->K {
 let start=j.wrapping_mul(4);
 p[start].add(run50::run(powers,[p[start.wrapping_add(1)],p[start.wrapping_add(2)],p[start.wrapping_add(3)]]))
}
pub fn go(p:[K;28],powers:[K;3],prepared:[[M31;3];3],left:u8,acc:K)->K {
 if left==0 {acc} else {
  let n=left-1;
  let product=prepared50::mul(prepared,acc);
  let value=block(p,powers,usize::from(n));
  go(p,powers,prepared,n,product.add(value))
 }
}
pub fn eval(p:[K;28],x:K)->K {
 let x2=x.square();let x3=x.mul(x2);let x4=x2.square();let powers=[x,x2,x3];
 let prepared=prepared50::prepare(x4);let acc=block(p,powers,6);
 go(p,powers,prepared,6,acc)
}
}
