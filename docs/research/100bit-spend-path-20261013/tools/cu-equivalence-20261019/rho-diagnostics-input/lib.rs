pub mod field {
/// The Mersenne prime 2^31 - 1.
pub const P: u32 = 0x7fff_ffff;
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
/// `E = QM31[v]/(v² - u)`, where `u² = 2+i` and `i² = -1`.
///
/// Exactly two QM31 coordinates, `c0 + c1*v`, or eight canonical M31 limbs.
/// For digits `d[0..8]` in `[0, P)`, the exact decode formula is
///
/// ```text
/// decode4(a,b,c,d) = (a + b*i) + (c + d*i)*u
/// decode8(d) = decode4(d0,d1,d2,d3) + decode4(d4,d5,d6,d7)*v
/// ```
///
/// Thus limb order is `(c0.c0.a, c0.c0.b, c0.c1.a, c0.c1.b,
/// c1.c0.a, c1.c0.b, c1.c1.a, c1.c1.b)`, matching
/// `R0C/ModuloField.lean:digitsField_apply` (lines 38–40) and
/// `AspisV8R19/SamplerFieldDecode.lean:decode4` (line 10).
/// `WideTower.lean:qm31_wideU_not_isSquare` supplies the mathematical
/// non-residue fact; `wideExact_card` gives `|E| = P^8`.
/// These references specify the arithmetic; they do not prove this Rust code.
///
/// Coordinates are private to preserve canonicality. Algebraic constructors
/// reduce raw QM31 representatives; wire/digit decoders reject noncanonical
/// input. All operations are total except inversion, which returns `None` at
/// zero. This reference implementation makes no constant-time claim.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct WideExact {
    c0: QM31,
    c1: QM31,
}
impl M31 {
    pub const ZERO: M31 = M31(0);

}
impl CM31 {
    pub const ZERO: CM31 = CM31 {
        a: M31(0),
        b: M31(0),
    };
    #[inline(always)]
    pub fn from_m31(a: M31) -> CM31 {
        CM31 { a, b: M31::ZERO }
    }
}
impl QM31 {
    pub const ZERO: QM31 = QM31 {
        c0: CM31 {
            a: M31(0),
            b: M31(0),
        },
        c1: CM31 {
            a: M31(0),
            b: M31(0),
        },
    };
    #[inline(always)]
    pub fn from_cm31(c0: CM31) -> QM31 {
        QM31 { c0, c1: CM31::ZERO }
    }
}
#[inline(always)]
fn canonical_qm31(value: QM31) -> QM31 {
    let reduce = |x: M31| M31(x.0 % P);
    QM31 {
        c0: CM31 {
            a: reduce(value.c0.a),
            b: reduce(value.c0.b),
        },
        c1: CM31 {
            a: reduce(value.c1.a),
            b: reduce(value.c1.b),
        },
    }
}
impl WideExact {
    /// The field embedding `x -> x + 0*v`; canonicalizes raw QM31 limbs.
    #[inline(always)]
    pub fn from_qm31(value: QM31) -> Self {
        Self {
            c0: canonical_qm31(value),
            c1: QM31::ZERO,
        }
    }
}
}
pub mod scalar {use crate::field::{M31,CM31,QM31,WideExact,P};
pub trait CodeField {fn from_m31(value:M31)->Self;}
impl CodeField for M31{
    fn from_m31(value: M31) -> Self {
        M31(value.0 % P)
    }
}
impl CodeField for CM31{
    fn from_m31(value: M31) -> Self {
        CM31::from_m31(<M31 as CodeField>::from_m31(value))
    }
}
impl CodeField for QM31{
    fn from_m31(value: M31) -> Self {
        QM31::from_cm31(<CM31 as CodeField>::from_m31(value))
    }
}
impl CodeField for WideExact{
    fn from_m31(value: M31) -> Self {
        Self::from_qm31(<QM31 as CodeField>::from_m31(value))
    }
}
}
pub mod trace {use crate::field::WideExact as E;
#[inline(always)]
pub fn value(tag: u16, index: usize, x: E) {
    #[cfg(feature="prover")]
    VALUES.with(|v| v.borrow_mut().push((tag,index,x.to_le_bytes())));
    #[cfg(not(feature="prover"))]
    let _ = (tag,index,x);
}
}
pub fn from_m31(value:field::M31)->field::WideExact {<field::WideExact as scalar::CodeField>::from_m31(value)}
