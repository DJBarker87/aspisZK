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
