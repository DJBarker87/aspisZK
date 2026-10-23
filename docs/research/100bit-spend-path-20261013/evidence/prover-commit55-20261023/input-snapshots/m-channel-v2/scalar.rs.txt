//! The generic field boundary shared by SPEC §§3–5.

use crate::field::{WideExact, CM31, M31, P, QM31};

/// A field with a unital M31 embedding (the Lean `[Algebra (ZMod P) E]`).
///
/// Implementors must obey field laws, return `None` exactly at zero from
/// `try_inv`, and make arithmetic non-panicking. The existing F/K/E tower
/// implements this interface. Its legacy public raw F/K representatives must
/// be canonical, as required by SPEC §1; WideExact enforces that invariant.
pub trait CodeField: Copy + Eq {
    const ZERO: Self;
    const ONE: Self;
    fn from_m31(value: M31) -> Self;
    fn add(self, rhs: Self) -> Self;
    fn sub(self, rhs: Self) -> Self;
    fn neg(self) -> Self;
    fn mul(self, rhs: Self) -> Self;
    fn try_inv(self) -> Option<Self>;
}

macro_rules! arithmetic {
    ($t:ty) => {
        const ZERO: Self = <$t>::ZERO;
        const ONE: Self = <$t>::ONE;
        fn add(self, rhs: Self) -> Self {
            <$t>::add(self, rhs)
        }
        fn sub(self, rhs: Self) -> Self {
            <$t>::sub(self, rhs)
        }
        fn neg(self) -> Self {
            <$t>::neg(self)
        }
        fn mul(self, rhs: Self) -> Self {
            <$t>::mul(self, rhs)
        }
    };
}

impl CodeField for M31 {
    arithmetic!(M31);
    fn from_m31(value: M31) -> Self {
        M31(value.0 % P)
    }
    fn try_inv(self) -> Option<Self> {
        #[cfg(feature = "r0-op-count")]
        let _count = crate::r0_op_count::enter(crate::r0_op_count::Op::FInvGeneric);
        if self == Self::ZERO {
            None
        } else {
            Some(self.pow(u64::from(P - 2)))
        }
    }
}
impl CodeField for CM31 {
    arithmetic!(CM31);
    fn from_m31(value: M31) -> Self {
        CM31::from_m31(<M31 as CodeField>::from_m31(value))
    }
    fn try_inv(self) -> Option<Self> {
        let norm = self.a.mul(self.a).add(self.b.mul(self.b));
        let inverse = <M31 as CodeField>::try_inv(norm)?;
        Some(Self {
            a: self.a.mul(inverse),
            b: self.b.neg().mul(inverse),
        })
    }
}
impl CodeField for QM31 {
    arithmetic!(QM31);
    fn from_m31(value: M31) -> Self {
        QM31::from_cm31(<CM31 as CodeField>::from_m31(value))
    }
    fn try_inv(self) -> Option<Self> {
        #[cfg(feature = "r0-op-count")]
        let _count = crate::r0_op_count::enter(crate::r0_op_count::Op::KInvGeneric);
        let r = CM31::new(M31(2), M31::ONE);
        let norm = self.c0.mul(self.c0).sub(r.mul(self.c1.mul(self.c1)));
        let inverse = <CM31 as CodeField>::try_inv(norm)?;
        Some(Self {
            c0: self.c0.mul(inverse),
            c1: self.c1.neg().mul(inverse),
        })
    }
}
impl CodeField for WideExact {
    arithmetic!(WideExact);
    fn from_m31(value: M31) -> Self {
        Self::from_qm31(<QM31 as CodeField>::from_m31(value))
    }
    fn try_inv(self) -> Option<Self> {
        #[cfg(feature = "r0-op-count")]
        let _count = crate::r0_op_count::enter(crate::r0_op_count::Op::EInvGeneric);
        let norm = self
            .c0()
            .mul(self.c0())
            .sub(Self::U.mul(self.c1().mul(self.c1())));
        let inverse = <QM31 as CodeField>::try_inv(norm)?;
        Some(Self::new(
            self.c0().mul(inverse),
            self.c1().neg().mul(inverse),
        ))
    }
}
