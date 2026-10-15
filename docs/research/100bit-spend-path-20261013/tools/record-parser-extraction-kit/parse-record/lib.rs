#![no_std]
#![allow(dead_code)]
extern crate self as aspis_core;
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
    }
    mod wide_exact {
        use super::{CM31, M31, P, QM31};
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
        impl WideExact {
    pub const LIMB_COUNT: usize = 8;
    pub const BYTE_LEN: usize = 32;
    #[inline(always)]
    pub const fn c1(self) -> QM31 {
        self.c1
    }
    /// Decode eight base-P digits without reduction; rejects any digit >= P.
    /// This is `digitsField`, not the natural-number cast of a base-P rank.
    #[inline(always)]
    pub fn from_limbs(limbs: [u32; Self::LIMB_COUNT]) -> Option<Self> {
        if limbs[0] >= P || limbs[1] >= P || limbs[2] >= P || limbs[3] >= P
            || limbs[4] >= P || limbs[5] >= P || limbs[6] >= P || limbs[7] >= P {
            return None;
        }
        let [a, b, c, d, e, f, g, h] = limbs;
        Some(Self {
            c0: QM31 {
                c0: CM31 {
                    a: M31(a),
                    b: M31(b),
                },
                c1: CM31 {
                    a: M31(c),
                    b: M31(d),
                },
            },
            c1: QM31 {
                c0: CM31 {
                    a: M31(e),
                    b: M31(f),
                },
                c1: CM31 {
                    a: M31(g),
                    b: M31(h),
                },
            },
        })
    }
    /// Exactly 32 bytes: eight little-endian u32 limbs in `digitsField` order.
    /// Rejects both wrong lengths and noncanonical limbs, without slicing an
    /// unvalidated input. This is a field encoding, not the R-B block sampler.
    #[inline(always)]
    pub fn from_le_bytes(bytes: &[u8]) -> Option<Self> {
        if bytes.len() != Self::BYTE_LEN {
            return None;
        }
        let limbs = [
            u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]),
            u32::from_le_bytes([bytes[4], bytes[5], bytes[6], bytes[7]]),
            u32::from_le_bytes([bytes[8], bytes[9], bytes[10], bytes[11]]),
            u32::from_le_bytes([bytes[12], bytes[13], bytes[14], bytes[15]]),
            u32::from_le_bytes([bytes[16], bytes[17], bytes[18], bytes[19]]),
            u32::from_le_bytes([bytes[20], bytes[21], bytes[22], bytes[23]]),
            u32::from_le_bytes([bytes[24], bytes[25], bytes[26], bytes[27]]),
            u32::from_le_bytes([bytes[28], bytes[29], bytes[30], bytes[31]]),
        ];
        Self::from_limbs(limbs)
    }
        }
    }
    pub use wide_exact::WideExact;
}
pub mod r1_wire {
    use aspis_core::field::{QM31, WideExact};
pub const LANES: usize = 29;
pub const POINTS: usize = 3;
pub const CLAIMS: usize = POINTS * LANES;
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    Allocation,
    RowOrder { expected: u8, actual: u8 },
    InvalidRow,
    Tag { row: u8 },
    Length { row: u8 },
    NonCanonical { row: u8, value: usize },
    Boundary { round: usize },
    Terminal,
    EqualCirclePoints,
    TrailingBytes,
    Public,
}
/// P1 tag and exact payload length, including the message-free rows.
pub const fn row_shape(row: u8) -> Option<(u8, usize)> {
    match row {
        0 | 1 | 3..=13 => Some((0, 0)),
        2 => Some((1, 32)),
        14 => Some((3, 32)),
        15..=24 => Some((2, 28 * 32)),
        25 => Some((4, (CLAIMS + LANES) * 32)),
        26 => Some((5, LANES * 32)),
        _ => None,
    }
}
fn validate_record_fields(row: u8, payload: &[u8]) -> Result<(), Error> {
    for (value, bytes) in payload.chunks_exact(32).enumerate() {
        let x = WideExact::from_le_bytes(bytes).ok_or(Error::NonCanonical { row, value })?;
        if x.c1() != QM31::ZERO {
            return Err(Error::NonCanonical { row, value });
        }
    }
    Ok(())
}
/// Reject malformed framing and every noncanonical E limb before hashing.
/// UNPROVED P2 subset: reject any nonzero E high component at parse.
pub fn parse_record(row: u8, record: &[u8]) -> Result<&[u8], Error> {
    let (tag, size) = row_shape(row).ok_or(Error::InvalidRow)?;
    if record.len() != 5 + size {
        return Err(Error::Length { row });
    }
    if record[0] != tag {
        return Err(Error::Tag { row });
    }
    if u32::from_le_bytes(record[1..5].try_into().unwrap()) as usize != size {
        return Err(Error::Length { row });
    }
    let payload = &record[5..];
    if row >= 14 {
        validate_record_fields(row, payload)?;
    }
    Ok(payload)
}
}
