//! Exact retained block-terminal formula for the fixed base-field geometric rows.
//! No sampled coefficient is a base-field assumption: ONLY public node powers
//! are M31. All challenges, coin weights and outputs remain arbitrary QM31.
use super::corelib::field::{QM31 as K,CM31,M31,M31_HALF};
fn lift(x:M31)->K {K::from_cm31(CM31::from_m31(x))}
pub(super) struct Kernel { powers:[[K;3];4],abc:[K;3] }
impl Kernel {
    pub(super) fn new(alpha:[K;4],abc:[K;3])->Self {
        Self{powers:alpha.map(|a|{let a2=a.square();[a,a2,a2.mul(a)]}),abc}
    }
    #[inline(never)]
    pub(super) fn terminal(&self,node:M31)->[K;4] {
        let mut p=[M31::ONE;10];p[0]=node;
        for i in 1..10 {p[i]=p[i-1].mul(p[i-1]);}
        let [a,b,c]=self.abc;
        let [ax,a2,a3]=self.powers[0];
        let i0=K::ONE.add(a2.mul_m31(p[1]));
        let c0=a2.half();let s0=lift(p[1]).add(c0);
        let i1=a3.add(ax.mul_m31(p[1]));
        let c1=ax.half();let s1=a3.mul_m31(p[1]).add(c1);
        let u=a.mul(i0.add(i1.mul_m31(p[0])))
            .add(b.mul(s0.add(s1.mul_m31(p[0]))))
            .add(c.mul(i0.mul_m31(p[0]).add(i1.half())));
        let v=b.mul(c0.add(c1.mul_m31(p[0]))).sub(c.mul(i1).half());
        let mut identity=K::ONE;let mut ended=K::ZERO;let mut carry=K::ONE;
        let quarter=M31_HALF.mul(M31_HALF);
        for r in 1..4 {
            let z1=p[2*r];let z2=p[2*r+1];let z3=z1.mul(z2);
            let [ax,a2,a3]=self.powers[r];
            let same=K::ONE.add(a3.mul_m31(z1)).add(a2.mul_m31(z2)).add(ax.mul_m31(z3));
            let stop=lift(z1).add(a3.mul_m31(M31::ONE.add(z2)).half())
                .add(a2.mul_m31(z3)).add(ax.mul_m31(z2.mul(M31_HALF).add(quarter)));
            let next=ax.half().half();
            identity=identity.mul(same);
            ended=ended.mul(same).add(carry.mul(stop));
            carry=carry.mul(next);
        }
        let common=u.mul(identity).add(v.mul(ended));let active=v.mul(carry);
        let z=[M31::ONE,p[8],p[9],p[8].mul(p[9])];
        let stop=[z[1],M31::ONE.add(z[2]).mul(M31_HALF),z[3],z[2].mul(M31_HALF).add(quarter)];
        core::array::from_fn(|j| {
            let mut value=common.mul_m31(z[j]).add(active.mul_m31(stop[j]));
            for _ in 0..8 {value=value.half();}
            value
        })
    }
}
