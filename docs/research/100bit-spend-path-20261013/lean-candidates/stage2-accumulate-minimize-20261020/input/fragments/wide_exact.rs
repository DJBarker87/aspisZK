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