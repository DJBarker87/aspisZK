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

pub mod sparse50 {
use super::field::QM31 as K;
pub fn factor(value:K,bit:usize)->K {if bit==0 {K::ONE.sub(value)} else {value}}
pub fn weight(point:[K;10],prefix:usize,width:u8,i:usize,left:u8,acc:K)->K {
 if left==0 {acc} else {
  let shift=usize::from(width).wrapping_sub(1).wrapping_sub(i);
  let bit=prefix.wrapping_shr(shift as u32)&1;
  let value=point[i];
  let factor=factor(value,bit);
  weight(point,prefix,width,i.wrapping_add(1),left-1,acc.mul(factor))
 }
}
pub fn row(prefix:usize,trailing:u8,suffix:usize)->usize {
 prefix.wrapping_shl(u32::from(trailing))|suffix
}
}

pub mod sparse_sum50 {
use super::{field::QM31 as K,sparse50};
pub fn sum(point:[K;10],column:[K;1024],width:u8,trailing:u8,suffix:usize,pref:usize,left:u16,acc:K)->K {
 if left==0 {acc} else {
  let weight=sparse50::weight(point,pref,width,0,width,K::ONE);
  let row=sparse50::row(pref,trailing,suffix);
  let value=column[row];let product=weight.mul(value);
  sum(point,column,width,trailing,suffix,pref.wrapping_add(1),left-1,acc.add(product))
 }
}
}

pub mod sparse_scan50 {
use super::field::QM31 as K;
pub fn one(x:K)->bool {
 x.c0.a.0==1 && x.c0.b.0==0 && x.c1.a.0==0 && x.c1.b.0==0
}
pub fn boolean(x:K)->bool {
 x.c0.b.0==0 && x.c1.a.0==0 && x.c1.b.0==0 && (x.c0.a.0==0 || x.c0.a.0==1)
}
pub fn width(point:[K;10],left:u8)->u8 {
 if left==0 {0} else {
  let n=left-1;let value=point[usize::from(n)];
  if boolean(value) {width(point,n)} else {left}
 }
}
pub fn suffix(point:[K;10],start:usize,left:u8)->usize {
 if left==0 {0} else {
  let n=left-1;
  let prev=suffix(point,start,n);
  let value=point[start.wrapping_add(usize::from(n))];
  prev.wrapping_shl(1)|usize::from(one(value))
 }
}
}

pub mod mle50 {
use super::{field::QM31 as K,sparse_scan50,sparse_sum50};
pub fn count(width:u8)->u16 {1u16.wrapping_shl(u32::from(width))}
pub fn mle(point:[K;10],column:[K;1024])->K {
 let width=sparse_scan50::width(point,10);let trailing=10-width;
 let suffix=sparse_scan50::suffix(point,usize::from(width),trailing);
 sparse_sum50::sum(point,column,width,trailing,suffix,0,count(width),K::ZERO)
}
}

pub mod linear50 {
use super::field::{QM31 as K,M31};
pub fn go(point:[K;10],left:u8,suffix:K,weighted:K)->(K,K) {
 if left==0 {(suffix,weighted)} else {
  let n=left-1;let next=suffix.add(point[usize::from(n)]);
  let weighted=if n==0 {weighted} else {weighted.add(next)};
  go(point,n,next,weighted)
 }
}
pub fn eval(point:[K;10])->(K,K) {
 let (suffix,weighted)=go(point,10,K::ZERO,K::ZERO);
 (suffix.mul_m31(M31(3)).add(weighted.mul_m31(M31(22))),
  suffix.mul_m31(M31(275)).add(weighted.mul_m31(M31(150))))
}
pub fn power26(x:K)->K {
 let x2=x.square();let x4=x2.square();let x8=x4.square();let x16=x8.square();
 x16.mul(x8).mul(x2)
}
}

pub mod mask_horner50 {
use super::{field::{QM31 as K,M31},prepared50};
pub fn go(q:[K;27],prepared:[[M31;3];3],left:u8,acc:K)->K {
 if left==0 {acc} else {
  let n=left-1;let value=prepared50::mul(prepared,acc).add(q[usize::from(n)]);
  go(q,prepared,n,value)
 }
}
pub fn eval(q:[K;27],x:K)->K {
 let prepared=prepared50::prepare(x);go(q,prepared,26,q[26])
}
}

pub mod tower50 {
use super::field::{QM31 as K,CM31 as C};
pub fn cm_i(x:C)->C {C{a:x.b.neg(),b:x.a}}
pub fn mul(x:K,coordinate:u8)->K {
 if coordinate==0 {x} else if coordinate==1 {K{c0:cm_i(x.c0),c1:cm_i(x.c1)}}
 else if coordinate==2 {K{c0:super::reconstruction::mul_r(x.c1),c1:x.c0}}
 else if coordinate==3 {K{c0:cm_i(super::reconstruction::mul_r(x.c1)),c1:cm_i(x.c0)}}
 else {panic!("tower coordinate out of range")}

}
}

pub mod mask_finish50 {
use super::{field::QM31 as K,linear50};
pub fn eval(shared:K,explicit_linear:K,g:K)->K {
 shared.add(K::ONE.add(linear50::power26(explicit_linear)).mul(g))
}
}

pub mod mask_coeff51 {
use super::{field::QM31 as K,tower50};
pub fn go(input:[K;26],exponents:[u8;26],left:u8,mut out:[K;27])->[K;27] {
 if left==0 {return out;}
 let i=26u8.wrapping_sub(left);
 let v=tower50::mul(input[i as usize],i%4);
 out[exponents[i as usize] as usize]=v;
 go(input,exponents,left.wrapping_sub(1),out)
}
pub fn eval(input:[K;26],exponents:[u8;26])->[K;27] {go(input,exponents,26,[K::ZERO;27])}
}

pub mod mask_columns51 {
use super::{field::QM31 as K,mle50};
pub fn go(point:[K;10],columns:[[K;1024];26],left:u8,mut out:[K;26])->[K;26]{
 if left==0{return out;}
 let i=26u8.wrapping_sub(left);
 out[i as usize]=mle50::mle(point,columns[i as usize]);
 go(point,columns,left.wrapping_sub(1),out)
}
pub fn eval(point:[K;10],columns:[[K;1024];26])->[K;26]{go(point,columns,26,[K::ZERO;26])}
}

pub mod coefficients51 {
use super::field::QM31 as K;
pub fn row(j:usize)->usize {(j/64)%4+4*((j/256)%4)+16*((j/16)%4)+64*(j%4)+256*((j/4)%4)}
pub fn cell(rows:[K;1024],j:usize)->K {rows[row(j)]}
pub fn go(rows:[K;1024],left:u16,mut out:[K;1024])->[K;1024]{
 if left==0{return out;}
 let i=1024u16.wrapping_sub(left);out[i as usize]=cell(rows,i as usize);
 go(rows,left.wrapping_sub(1),out)
}
pub fn eval(rows:[K;1024])->[K;1024]{go(rows,1024,[K::ZERO;1024])}
}

pub mod terminal_eq51 {
use super::field::QM31 as K;
pub fn factor(a:K,b:K)->K {let ab=a.mul(b);K::ONE.sub(a).sub(b).add(ab).add(ab)}
pub fn go(left:[K;10],right:[K;10],index:u8,product:K)->K {
 if index==10{return product;}
 let next=product.mul(factor(left[index as usize],right[index as usize]));
 go(left,right,index.wrapping_add(1),next)
}
pub fn eval(left:[K;10],right:[K;10])->K{let product=factor(left[0],right[0]);go(left,right,1,product)}
pub fn suffix(eq:K,composition:K,h1:K,active:K,mu:K)->K{
 eq.mul(composition).add(mu.mul(h1)).add(mu.mul(mu).mul(K::ONE.sub(active).mul(h1)))
}
}
