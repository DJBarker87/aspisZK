use crate::field::{QM31 as K,WideExact as E,M31};
pub const QUARTER:M31=M31(536870912);
pub const PERM:[usize;4]=[0,3,2,1];
use crate::{Weights,kpowers};
pub fn factored_s2_libra_weights(ap0:&[E;4],ap1:&[E;4],extra:[K;2])->[E;4] {
    let mut weights=[E::ZERO;4];
    for side in 0..2 {
        let q=kpowers::<4>(extra[side]);
        let q4=q[2].square();let q8=q4.square();let q12=q8.mul(q4);let q16=q8.square();
        let low=Weights::scalar_factor(&q,ap0);
        let high_powers=[K::ONE,q4,q8,q12];
        let terms:[E;4]=core::array::from_fn(|r|ap1[PERM[r]].mul_qm31(high_powers[r]).mul_m31(QUARTER));
        let first2=terms[0].add(terms[1]);let first3=first2.add(terms[2]);let all=first3.add(terms[3]);
        if side==0 {
            weights[0]=low.mul(all);
            weights[1]=low.mul(first3).mul_qm31(q16);
        } else {
            weights[1]=weights[1].add(low.mul(ap1[PERM[3]].mul_m31(QUARTER)));
            weights[2]=low.mul(all).mul_qm31(q4);
            weights[3]=low.mul(first2).mul_qm31(q16.mul(q4));
        }
    }
    weights
}
