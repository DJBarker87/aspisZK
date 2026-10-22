#![allow(unexpected_cfgs)]
pub mod field;
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
