extern crate self as aspis_core;
pub mod field;
pub mod old;
pub mod new;
use crate::field::{QM31 as K,WideExact as E,M31};
pub const QUARTER:M31=M31(536870912);
pub const PERM:[usize;4]=[0,3,2,1];
pub struct Weights;
impl Weights {
    pub fn scalar_factor(f:&[K;4],p:&[E;4])->E {
        (0..4).fold(E::ZERO,|v,s|v.add(p[PERM[s]].mul_qm31(f[s]))).mul_m31(QUARTER)
    }
}
pub fn kpowers<const N:usize>(x:K)->[K;N] { let mut p=K::ONE;core::array::from_fn(|_| {let a=p;p=p.mul(x);a}) }
