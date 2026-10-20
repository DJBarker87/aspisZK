use crate::field::{QM31 as K,WideExact as E,M31};
pub const QUARTER:M31=M31(536870912);
pub const PERM:[usize;4]=[0,3,2,1];
pub fn twofold_libra_weights(low:&[E;16],extra:[K;2])->[E;4] {
    let powers:[[K;28];2]=core::array::from_fn(|side| {
        let mut power=K::ONE;
        core::array::from_fn(|_| {let value=power;power=power.mul(extra[side]);value})
    });
    core::array::from_fn(|j| {
        let mut weight=E::ZERO;
        for s in 0..16 {
            let index=16*j+s;
            if index<56 {
                weight=weight.add(low[s].mul_qm31(powers[index/28][index%28]));
            }
        }
        weight
    })
}
