use crate::field::{M31, QM31, WideExact};
use crate::transport::Variant;
type K = QM31;
type E = WideExact;
pub const QUARTER:M31=M31(536870912);
pub const PERM:[usize;4]=[0,3,2,1];
pub fn kpowers<const N:usize>(x:K)->[K;N] { let mut p=K::ONE;core::array::from_fn(|_| {let a=p;p=p.mul(x);a}) }
fn twofold_libra_weights(low:&[E;16],extra:[K;2])->[E;4] {
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
pub struct Weights {
    pub variant:Variant,
    pub factors:[[[K;4];5];5],
    pub points:[[K;10];3],
    pub extra:[K;2],
}
impl Weights {
fn scalar_factor(f:&[K;4],p:&[E;4])->E {
        (0..4).fold(E::ZERO,|v,s|v.add(p[PERM[s]].mul_qm31(f[s]))).mul_m31(QUARTER)
    }
}
fn factored_s2_libra_weights(ap0:&[E;4],ap1:&[E;4],extra:[K;2])->[E;4] {
    let mut weights=[E::ZERO;4];
    for side in 0..2 {
        let q0=K::ONE;
        let q1=q0.mul(extra[side]);
        let q2=q1.mul(extra[side]);
        let q3=q2.mul(extra[side]);
        let _q4=q3.mul(extra[side]);
        let q=[q0,q1,q2,q3];
        let q4=q[2].square();let q8=q4.square();let q12=q8.mul(q4);let q16=q8.square();
        let low=Weights::scalar_factor(&q,ap0);
        let high_powers=[K::ONE,q4,q8,q12];
        let term0=ap1[PERM[0]].mul_qm31(high_powers[0]).mul_m31(QUARTER);
        let term1=ap1[PERM[1]].mul_qm31(high_powers[1]).mul_m31(QUARTER);
        let term2=ap1[PERM[2]].mul_qm31(high_powers[2]).mul_m31(QUARTER);
        let term3=ap1[PERM[3]].mul_qm31(high_powers[3]).mul_m31(QUARTER);
        let terms=[term0,term1,term2,term3];
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
impl Weights {
    pub fn selected_projection(&self, ap0:[E;4], ap1:[E;4], low:[E;16]) -> [E;4] {
        let libra=if self.variant==Variant::S2 {factored_s2_libra_weights(&ap0,&ap1,self.extra)}else{twofold_libra_weights(&low,self.extra)};
        libra
    }
}
pub fn field(bytes:&[u8],i:usize)->E { E::from_le_bytes(&bytes[i*32..(i+1)*32]).unwrap() }
