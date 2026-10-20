// Exact selected-source cut. Only namespaces/imports and public forwarding shim are added.
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
impl CM31 {
    #[inline(always)]
    pub fn new(a: M31, b: M31) -> CM31 {
        CM31 { a, b }
    }
}
/// QM31 = CM31[u] / (u^2 - (2 + i)). Element c0 + c1*u. (stwo parameterization)
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct QM31 {
    pub c0: CM31,
    pub c1: CM31,
}
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct WideExact {
    c0: QM31,
    c1: QM31,
}
impl WideExact {
    /// Construct `c0 + c1*v`, reducing each raw M31 representative modulo P.
    pub fn new(c0: QM31, c1: QM31) -> Self {
        Self {
            c0: canonical_qm31(c0),
            c1: canonical_qm31(c1),
        }
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
}
pub mod sampler {
use crate::field::{CM31, M31, P, QM31, WideExact};
/// Divide a little-endian word array by P, retaining every quotient word.
/// Dividends are below P * 2^32, so every division fits in u64.
fn qm31_div_pass(mut rank: [u32; 8]) -> ([u32; 8], u32) {
    let mut remainder = 0u64;
    let mut j = 8usize;
    while j > 0 {
        j -= 1;
        let dividend = (remainder << 32) | u64::from(rank[j]);
        rank[j] = (dividend / u64::from(P)) as u32;
        remainder = dividend % u64::from(P);
    }
    (rank, remainder as u32)
}
/// The low four base-P digits already represent rank modulo P^4.
fn qm31_digits(block: &[u8; 32]) -> [u32; 4] {
    let mut rank = [0u32; 8];
    let mut i = 0usize;
    while i < 8 {
        let start = 4 * i;
        rank[i] = u32::from_le_bytes([
            block[start],
            block[start + 1],
            block[start + 2],
            block[start + 3],
        ]);
        i += 1;
    }
    let mut digits = [0u32; 4];
    let mut i = 0usize;
    while i < 4 {
        let (quotient, digit) = qm31_div_pass(rank);
        rank = quotient;
        digits[i] = digit;
        i += 1;
    }
    digits
}
pub fn qm31_sample(block: &[u8; 32]) -> QM31 {
    let digits = qm31_digits(block);
    QM31 {
        c0: CM31::new(M31(digits[0]), M31(digits[1])),
        c1: CM31::new(M31(digits[2]), M31(digits[3])),
    }
}
/// Return the low eight base-P digits of the 256-bit little-endian block and
/// the remaining quotient. This uses eight long divisions by P rather than
/// first reducing the full block with 256 binary steps.
fn low_base_p_digits(block: &[u8; 32]) -> ([u32; 8], u32) {
    let mut rank = [0u32; 8];
    let mut i = 0usize;
    while i < 8 {
        let start = 4 * i;
        rank[i] = u32::from_le_bytes([
            block[start],
            block[start + 1],
            block[start + 2],
            block[start + 3],
        ]);
        i += 1;
    }

    let mut digits = [0u32; 8];
    let mut i = 0usize;
    while i < 8 {
        let (quotient, digit) = qm31_div_pass(rank);
        rank = quotient;
        digits[i] = digit;
        i += 1;
    }
    (digits, rank[0])
}
fn decode8(digits: [u32; 8]) -> WideExact {
    WideExact::new(
        QM31 {
            c0: CM31::new(M31(digits[0]), M31(digits[1])),
            c1: CM31::new(M31(digits[2]), M31(digits[3])),
        },
        QM31 {
            c0: CM31::new(M31(digits[4]), M31(digits[5])),
            c1: CM31::new(M31(digits[6]), M31(digits[7])),
        },
    )
}
/// Add a small integer to a base-P digit vector. Returns the carry beyond
/// the final digit, which is at most one for the values used by the sampler.
fn add_small_base_p(digits: &mut [u32; 8], mut addend: u32) -> bool {
    let mut i: usize = 0;
    while i < 8 {
        let sum = u64::from(digits[i]) + u64::from(addend);
        digits[i] = (sum % u64::from(P)) as u32;
        addend = (sum / u64::from(P)) as u32;
        i += 1;
    }
    debug_assert!(addend <= 1);
    addend != 0
}
/// `decode8(rank(block) mod P^8)`, byte-for-byte equivalent to the frozen
/// R0 sampler. The repeated divisions directly produce the low eight digits.
pub fn ordinary_sample(block: &[u8; 32]) -> WideExact {
    let (digits, _) = low_base_p_digits(block);
    decode8(digits)
}
/// `decode8((rank(block) mod (P^8 - 1)) + 1)`, byte-for-byte equivalent to
/// the frozen R0 sampler. Since `P^8 ≡ 1 (mod P^8 - 1)`, the high quotient can
/// be added to the low digits before the final increment. A carry past digit
/// seven contributes one more modulo `P^8 - 1`.
pub fn gamma_sample(block: &[u8; 32]) -> WideExact {
    let (mut digits, quotient) = low_base_p_digits(block);
    let wrapped = add_small_base_p(&mut digits, quotient + 1);
    if wrapped {
        let wrapped_again = add_small_base_p(&mut digits, 1);
        debug_assert!(!wrapped_again);
    }
    decode8(digits)
}
}
pub mod public_cut {
use crate::field::{QM31, WideExact};
pub fn gamma(block: &[u8; 32]) -> WideExact { crate::sampler::gamma_sample(block) }
pub fn ordinary(block: &[u8; 32]) -> WideExact { crate::sampler::ordinary_sample(block) }
pub fn qm31(block: &[u8; 32]) -> QM31 { crate::sampler::qm31_sample(block) }
pub fn block_samples(block: &[u8; 32]) -> (WideExact, WideExact, QM31) {
    (gamma(block), ordinary(block), qm31(block))
}
}
