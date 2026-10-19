pub trait Digest32: Copy {
    fn digest(&self, parts: &[&[u8]]) -> [u8; 32];
}
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
impl WideExact {pub fn from_qm31(_q:QM31)->Self{unreachable!()}}
}
pub mod aspis_core {pub use crate::{Digest32,field};}
pub mod sampler {pub fn qm31_sample(_block:&[u8;32])->crate::field::QM31{unreachable!()}}
pub mod trace {pub fn value(_tag:u16,_index:usize,_x:crate::field::WideExact){unreachable!()}}
pub mod transcript {use crate::{Digest32,aspis_core};use crate::field::WideExact as E;
pub struct Transcript<H: Digest32> { pub state:[u8;32], hash:H }
impl<H:Digest32> Transcript<H> {pub fn block(&mut self,_row:u8,_payload:&[u8])->[u8;32]{unreachable!()}
    /// Final query-residual batching: at most 22 coefficients, so a nonzero
    /// residual has at most 21 roots even when sampled from the K subfield.
    /// Gamma and both folding challenges continue to use E.
    pub fn scalar_k(&mut self,row:u8,payload:&[u8])->aspis_core::field::QM31 {
        let out=crate::sampler::qm31_sample(&self.block(row,payload));
        crate::trace::value(4,row as usize,E::from_qm31(out)); out
    }
}
}
