#![allow(dead_code)]
#[derive(Clone,Copy)]
pub struct C{pub a:u32,pub b:u32}
#[derive(Clone,Copy)]
pub struct Q{pub c0:C,pub c1:C}
pub trait Base{
 fn mul(a:u32,b:u32)->u32;
 fn add(a:u32,b:u32)->u32;
 fn neg(x:u32)->u32;
 fn inv(x:u32)->u32;
}
pub fn cm_inverse<O:Base>(x:C)->C{
 let norm=O::add(O::mul(x.a,x.a),O::mul(x.b,x.b));
 let inverse_norm=O::inv(norm);
 C{a:O::mul(x.a,inverse_norm),b:O::mul(O::neg(x.b),inverse_norm)}
}
pub trait Complex{
 fn zero(x:Q)->bool;
 fn square(x:C)->C;
 fn r(x:C)->C;
 fn sub(x:C,y:C)->C;
 fn inverse(x:C)->C;
 fn mul(x:C,y:C)->C;
 fn neg(x:C)->C;
}
pub fn qm_try_inverse<O:Complex>(x:Q)->Option<Q>{
 if O::zero(x){return None;}
 let norm=O::sub(O::square(x.c0),O::r(O::square(x.c1)));
 let inverse_norm=O::inverse(norm);
 Some(Q{c0:O::mul(x.c0,inverse_norm),c1:O::mul(O::neg(x.c1),inverse_norm)})
}
pub fn qm_inverse<O:Complex>(x:Q)->Q{qm_try_inverse::<O>(x).expect("cannot invert zero in QM31")}
