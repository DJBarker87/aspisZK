#![allow(unexpected_cfgs)]
pub mod field;
pub mod factors {
use super::field::QM31 as K;
pub fn point(a:K,b:K)->[K;4] {
 [K::ONE.sub(a).mul(K::ONE.sub(b)),a.mul(K::ONE.sub(b)),K::ONE.sub(a).mul(b),a.mul(b)]
}
pub fn circle(x:K,y:K)->[K;4] { [K::ONE,y,x,x.mul(y)] }
pub fn double(x:K)->K {x.mul(x).add(x.mul(x)).sub(K::ONE)}
pub fn product(q:[K;5],i:usize,left:u8,s:K)->K {
 if left==0 {s} else {
  let next=s.mul(q[i]);
  product(q,i+1,left-1,next)
 }
}

pub fn line(x:K,y:K)->[K;4] {[K::ONE,x,y,x.mul(y)]}
pub fn lines(mut out:[[K;4];5],d:usize,left:u8,x:K)->[[K;4];5] {
 if left==0 {out} else {
  let y=double(x);out[d]=line(x,y);let next=double(y);
  lines(out,d+1,left-1,next)
 }
}
pub fn circle_rows(x:K,y:K)->[[K;4];5] {
 let mut out=[[K::ZERO;4];5];out[0]=circle(x,y);
 lines(out,1,4,double(x))
}
}

pub mod point_rows {
use super::{field::QM31 as K,factors::point};
pub const TAU:[usize;5]=[3,4,2,0,1];
pub fn fill(p:[K;10],mut out:[[K;4];5],d:usize,left:u8)->[[K;4];5] {
 if left==0 {out} else {
 let t=TAU[d];let a=p[9-2*t];let b=p[8-2*t];
 out[d]=point(a,b);fill(p,out,d+1,left-1)
 }
}
pub fn all(p:[K;10])->[[K;4];5] {fill(p,[[K::ZERO;4];5],0,5)}
}

pub mod points {
use super::field::QM31 as K;
pub fn successor(p:[K;10],mut out:[K;10],left:u8,carry:K)->[K;10] {
 if left==0 {out} else {
  let coordinate=(left-1) as usize;
  let bit=p[coordinate];let bc=bit.mul(carry);
  out[coordinate]=bit.add(carry).sub(bc.add(bc));
  successor(p,out,left-1,bc)
 }
}
pub fn absorption(mut p:[K;10])->[K;10] {
 p[7]=K::ONE.sub(p[7]);
 p[6]=K::ONE.sub(p[6]);p
}
pub fn all(p:[K;10])->[[K;10];3] {
 [p,successor(p,p,10,K::ONE),absorption(p)]
}
}

pub mod stored {
use super::field::QM31 as K;
pub fn product(rows:[[K;4];5],j:usize,d:usize,left:u8,acc:K)->K {
 if left==0 {acc} else {
  let digit=(j>>((2*d) as u32))&3;
  let next=acc.mul(rows[d][digit]);product(rows,j,d+1,left-1,next)
 }
}
}

use field::M31;
pub fn square_ref(x:M31,left:u8)->M31 {
 if left==0 {x} else {square_ref(x.mul(x),left-1)}
}
pub fn inverse_ref(x:M31)->M31 {
 assert!(x.0!=0);
 let t2=x.mul(x).mul(x);
 let t4=square_ref(t2,2).mul(t2);
 let t8=square_ref(t4,4).mul(t4);
 let t16=square_ref(t8,8).mul(t8);
 let t24=square_ref(t16,8).mul(t8);
 let t28=square_ref(t24,4).mul(t4);
 let t29=t28.mul(t28).mul(x);
 let t30=t29.mul(t29);
 t30.mul(t30).mul(x)
}

pub mod kernels {
use super::{field::{QM31 as K,CM31 as C},inverse_ref};
pub fn square(x:K)->K {x.square()}
pub fn power(base:K,exp:u8,acc:K)->K {
 if exp==0 {acc} else {
  let next=if exp&1!=0 {acc.mul(base)} else {acc};
  power(base.square(),exp>>1u32,next)
 }
}
pub fn inverse_c(x:C)->C {
 let norm=x.a.mul(x.a).add(x.b.mul(x.b));
 let inv_norm=inverse_ref(norm);
 C{a:x.a.mul(inv_norm),b:x.b.neg().mul(inv_norm)}
}
pub fn mul_r(x:C)->C {
 let two_a=x.a.double();let real=two_a.sub(x.b);
 let two_b=x.b.double();let imag=x.a.add(two_b);
 C{a:real,b:imag}
}
pub fn inverse_q(x:K)->Option<K> {
 if x.is_zero() {None} else {
  let norm=x.c0.square().sub(mul_r(x.c1.square()));
  let ni=inverse_c(norm);
  Some(K{c0:x.c0.mul(ni),c1:x.c1.neg().mul(ni)})
 }
}
}

pub mod extras {
use super::{field::{QM31 as K,CM31 as C,M31},inverse_ref,kernels::power};
pub fn half()->K {K::from_cm31(C::from_m31(inverse_ref(M31(2))))}
pub fn libra(extra:[K;2],j:usize)->K {
 if j<56 {power(extra[j/28],(j%28) as u8,K::ONE)} else {K::ZERO}
}
}

pub mod owned {
use super::field::{QM31 as K,WideExact as E};
pub fn cell(kp:[E;7],raw:[K;7],kind:usize,left:u8,sum:E)->E {
 if left==0 {sum} else {
  let next=sum.add(kp[kind].mul_qm31(raw[kind]));
  cell(kp,raw,kind+1,left-1,next)
 }
}

pub const MASKS:[u16;64]=[
    6144, 6144, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145,
    6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6144, 4097, 2048, 6145, 2049, 2048, 6145,
    2049, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145,
    6145, 6145, 6145, 6145, 6145, 4097, 6145, 6145, 4097, 26214, 26214, 26214, 26214, 26214, 26214,
    1749,
];
pub fn row(j:usize)->usize {
 (j/64)%4+4*((j/256)%4)+16*((j/16)%4)+64*(j%4)+256*((j/4)%4)
}
pub fn inactive(j:usize)->bool {
 let r=row(j);(MASKS[r/16] >> ((r%16) as u32))&1==0
}
}

pub mod weights53 {
use super::{field::QM31 as K,points,point_rows,factors,stored,owned,extras};
pub type State=(u8,[[[K;4];5];5],[[K;10];3],[K;2]);
pub fn new(alpha:[K;10],x0:K,y0:K,x1:K,y1:K)->State {
 let p=points::all(alpha);
 let r0=point_rows::all(p[0]);let r1=point_rows::all(p[1]);let r2=point_rows::all(p[2]);
 let r3=factors::circle_rows(x0,y0);let r4=factors::circle_rows(x1,y1);
 (2,[r0,r1,r2,r3,r4],p,[alpha[8],alpha[9]])
}
pub fn raw(s:State,kind:usize,j:usize)->K {
 match kind {
  0=>if owned::inactive(j) {K::ONE} else {K::ZERO},
  4=>extras::libra(s.3,j),
  _=>{let k=if kind<4 {kind-1}else{kind-2};stored::product(s.1[k],j,0,5,K::ONE)}
 }
}
pub fn row(s:State,j:usize)->[K;7] {
 [raw(s,0,j),raw(s,1,j),raw(s,2,j),raw(s,3,j),raw(s,4,j),raw(s,5,j),raw(s,6,j)]
}
}

pub mod weights_material53 {
use super::{field::WideExact as E,weights53::{self,State},owned};
pub fn fill(st:State,kp:[E;7],mut out:[E;1024],j:usize,left:u16)->[E;1024] {
 if left==0 {out} else {
  let row=weights53::row(st,j);
  out[j]=owned::cell(kp,row,0,7,out[j]);fill(st,kp,out,j+1,left-1)
 }
}
pub fn all(st:State,kp:[E;7])->[E;1024] {fill(st,kp,[E::ZERO;1024],0,1024)}
}
