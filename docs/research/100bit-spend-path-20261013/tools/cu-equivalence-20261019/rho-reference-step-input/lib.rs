pub mod field {
/// M31 base field element, canonical representation in [0, P).
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct M31(pub u32);
/// CM31 = M31[i] / (i^2 + 1). Element a + b*i.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct CM31 {
    pub a: M31,
    pub b: M31,
}
/// QM31 = CM31[u] / (u^2 - (2 + i)). Element c0 + c1*u. (stwo parameterization)
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct QM31 {
    pub c0: CM31,
    pub c1: CM31,
}
impl M31 {pub fn mul(self,_rhs:Self)->Self {unreachable!()}}
impl CM31 {
    #[inline(always)]
    pub fn mul_m31(self, rhs: M31) -> CM31 {
        CM31 {
            a: self.a.mul(rhs),
            b: self.b.mul(rhs),
        }
    }
}
impl QM31 {pub fn add(self,_rhs:Self)->Self {unreachable!()}
    /// Late-lift kernel: QM31 * M31 costs 2 scalar CM31 scalings.
    #[inline(always)]
    pub fn mul_m31(self, rhs: M31) -> QM31 {
        #[cfg(feature = "r0-op-count")]
        let _count = crate::r0_op_count::enter(crate::r0_op_count::Op::KMulF);
        QM31 {
            c0: self.c0.mul_m31(rhs),
            c1: self.c1.mul_m31(rhs),
        }
    }
}
}
pub fn step(weight:field::QM31,power:field::QM31,basis:field::M31)->field::QM31 {
weight.add(power.mul_m31(basis))
}
