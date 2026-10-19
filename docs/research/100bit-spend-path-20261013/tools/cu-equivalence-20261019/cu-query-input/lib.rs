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
}
pub mod transport {
//! UNPROVED COST PROBE. S uses the D18 digit permutation; D uses retained D13.
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub enum Variant { S1, S2, D }
impl Variant {
    pub fn folds(self) -> usize { if self == Self::S1 { 1 } else { 2 } }
}
}
pub mod verifier {
use crate::{field::WideExact as E,transport::Variant};
#[cfg(not(feature = "private-leaf-salts"))]
pub const INITIAL_QUERY_BYTES:usize=480+128+2*6*7*32;
#[cfg(feature = "private-leaf-salts")]
pub const INITIAL_QUERY_BYTES:usize=480+128+64+2*6*7*32;
#[cfg(not(feature = "private-leaf-salts"))]
pub const SECOND_QUERY_BYTES:usize=4*32+6*7*32;
#[cfg(feature = "private-leaf-salts")]
pub const SECOND_QUERY_BYTES:usize=4*32+32+6*7*32;
pub struct View<'a> {
    pub variant:Variant,pub semantic:&'a[u8],pub y1:&'a[u8],pub inactive:E,
    pub round0:&'a[u8],pub folded_root:Option<&'a[u8;32]>,pub round1:&'a[u8],
    pub final_message:&'a[u8],pub query_bytes:&'a[u8],
}
impl<'a> View<'a> {
    pub fn query(&self,i:usize)->&'a[u8] {let width=INITIAL_QUERY_BYTES+if self.variant.folds()==2 {SECOND_QUERY_BYTES}else{0};&self.query_bytes[i*width..(i+1)*width]}
}
}
pub fn query<'a>(view:&verifier::View<'a>,index:usize)->&'a[u8] {view.query(index)}
