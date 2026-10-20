pub mod field;
use field::{WideExact as E,M31};
const QUARTER:M31=M31(536870912);
const PERM:[usize;4]=[0,3,2,1];
pub fn low(ap0:&[E;4],ap1:&[E;4])->[E;16] {
            let low:[E;16]=core::array::from_fn(|s|ap0[PERM[s%4]].mul(ap1[PERM[s/4]]).mul_m31(QUARTER.mul(QUARTER)));
low
}
