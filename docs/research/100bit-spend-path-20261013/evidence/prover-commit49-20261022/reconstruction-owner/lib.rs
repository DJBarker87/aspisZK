#![allow(unexpected_cfgs)]
pub mod field;
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
