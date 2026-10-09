//! R0's total, one-block field samplers and bounded q22 query scan.
//!
//! Field samples interpret all 32 bytes as a little-endian integer, reduce
//! modulo P^4, P^8, or P^8-1, and decode least-significant-first base-P
//! digits. These are the modulo laws in `R0C/ModuloField.lean` and
//! `R0P/SemD2.lean`, including their modulo bias; they are not exact-uniform
//! rejection samplers. Each field/circle method squeezes and advances once.
//! The query method instead consumes up to eight blocks, as in
//! `R0C/V3/Q22Law.lean:scanOut` and `AspisV8R19/Q22WordScan.lean:scan`.
//!
//! Use [`Transcript::r0_sample_row`] for one absorb on every row, including
//! rows with an empty message. Its labels and caller-supplied canonical
//! message bytes are **provisional pending S1's SPEC.md**. The primitive
//! `r0_challenge_*` methods do not absorb. No legacy methods are changed,
//! and this module does not select or migrate a production verifier.

use crate::circle::{secure_ood_circle_point_from_parameter, SecureCirclePoint};
use crate::field::{WideExact, CM31, M31, P, QM31};
use crate::transcript::{circle_fallback_point, QuerySampleError, Transcript};

// Little-endian base-2^32 limbs. Keeping the moduli private ensures the
// reducer's invariant 0 < n < 2^248 holds for every caller.
type Rank = [u32; 8];
const P4: Rank = [1, 0x7fff_fffe, 0x8000_0001, 0x0fff_ffff, 0, 0, 0, 0];
const P8: Rank = [
    1,
    0xffff_fffc,
    6,
    0x5fff_fff9,
    0x4000_0004,
    0x6fff_fffe,
    0xf000_0000,
    0x00ff_ffff,
];
const P8_MINUS_ONE: Rank = [
    0,
    0xffff_fffc,
    6,
    0x5fff_fff9,
    0x4000_0004,
    0x6fff_fffe,
    0xf000_0000,
    0x00ff_ffff,
];

pub const QUERY_COUNT: usize = 22;
pub const QUERY_BOUND: u32 = 1 << 18;
pub const QUERY_MAX_DRAWS: usize = 64;

/// Provisional row domain separation, pending S1's encoding/label spec.
pub mod label {
    /// Rows 0..32 use the currently unused labels 0x80..=0x9f. Invalid row
    /// indices return `None`; no wraparound or alias to a legacy label.
    #[allow(non_snake_case)]
    pub const fn R0_ROW(row: u8) -> Option<u8> {
        if row < 32 {
            Some(0x80 + row)
        } else {
            None
        }
    }
}

/// Selects the existing row fallback: parameter u for row 25, 1+u for 26.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CircleRow {
    First,
    Second,
}

/// The challenge shape selected by the 32-row R0 schedule.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum R0Challenge {
    Qm31(QM31),
    Circle(SecureCirclePoint),
    Wide(WideExact),
    Queries([u32; QUERY_COUNT]),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum R0RowError {
    /// Rejected before any transcript operation.
    InvalidRow { row: u8 },
    /// The verifier must reject. The row absorb and all eight query blocks
    /// have already been consumed; the transcript is not rolled back.
    Queries(QuerySampleError),
}

fn block_rank(block: &[u8; 32]) -> Rank {
    core::array::from_fn(|i| {
        let j = 4 * i;
        u32::from_le_bytes([block[j], block[j + 1], block[j + 2], block[j + 3]])
    })
}

/// Binary long division, without allocation or a variable number of
/// reductions. Before each bit, r < n; after shifting in a bit, r < 2n,
/// so one subtraction suffices. All three n are below 2^248, hence the
/// intermediate fits in 256 bits (including the incoming carry).
fn reduce_rank(rank: Rank, modulus: Rank) -> Rank {
    let mut remainder = [0u32; 8];
    for bit in (0..256).rev() {
        let mut carry = (rank[bit / 32] >> (bit % 32)) & 1;
        for limb in &mut remainder {
            let next = *limb >> 31;
            *limb = (*limb << 1) | carry;
            carry = next;
        }
        let mut difference = [0u32; 8];
        let mut borrow = false;
        for i in 0..8 {
            let (value, b0) = remainder[i].overflowing_sub(modulus[i]);
            let (value, b1) = value.overflowing_sub(u32::from(borrow));
            difference[i] = value;
            borrow = b0 || b1;
        }
        if !borrow {
            remainder = difference;
        }
    }
    remainder
}

/// Eight successive divisions by P. Called only with rank < P^8.
/// A limb dividend is < P*2^32 < 2^63, so u64 suffices.
fn base_p_digits(mut rank: Rank) -> [u32; 8] {
    core::array::from_fn(|_| {
        let mut remainder = 0u64;
        for limb in rank.iter_mut().rev() {
            let dividend = (remainder << 32) | u64::from(*limb);
            *limb = (dividend / u64::from(P)) as u32;
            remainder = dividend % u64::from(P);
        }
        remainder as u32
    })
}

fn decode4([a, b, c, d]: [u32; 4]) -> QM31 {
    QM31 {
        c0: CM31::new(M31(a), M31(b)),
        c1: CM31::new(M31(c), M31(d)),
    }
}

fn decode8([a, b, c, d, e, f, g, h]: [u32; 8]) -> WideExact {
    // R-A's constructor, with already canonical base-P digits. No fallible
    // decoder or unwrap on the sampler's total path.
    WideExact::new(decode4([a, b, c, d]), decode4([e, f, g, h]))
}

/// `decode4(digits(rank(block) mod P^4))`, exactly `SemD2.qm31Sample`.
pub fn qm31_sample(block: &[u8; 32]) -> QM31 {
    let d = base_p_digits(reduce_rank(block_rank(block), P4));
    decode4([d[0], d[1], d[2], d[3]])
}

/// `decode8(digits(rank(block) mod P^8))`, exactly `ModuloField.ordinary`.
pub fn ordinary_sample(block: &[u8; 32]) -> WideExact {
    decode8(base_p_digits(reduce_rank(block_rank(block), P8)))
}

/// `fieldRank((rank(block) mod (P^8-1)) + 1)`, always nonzero.
pub fn gamma_sample(block: &[u8; 32]) -> WideExact {
    let mut rank = reduce_rank(block_rank(block), P8_MINUS_ONE);
    let mut carry = true;
    for limb in &mut rank {
        let (sum, next) = limb.overflowing_add(u32::from(carry));
        *limb = sum;
        carry = next;
    }
    decode8(base_p_digits(rank))
}

/// One modulo-QM31 parameter, mapped to the circle or the existing fixed
/// row fallback. No retry, including for CM31 parameters and poles ±i.
/// Coordinates are QM31; `WideExact::from_qm31` is their model embedding.
pub fn circle_sample(block: &[u8; 32], row: CircleRow) -> SecureCirclePoint {
    secure_ood_circle_point_from_parameter(qm31_sample(block)).unwrap_or_else(|_| {
        circle_fallback_point(match row {
            CircleRow::First => 0,
            CircleRow::Second => 1,
        })
    })
}

fn query_words(block: &[u8; 32]) -> [u32; 8] {
    block_rank(block).map(|word| word & (QUERY_BOUND - 1))
}

// Fixed-capacity implementation of Q22WordScan.ScanState. Private fields
// preserve accepted_len <= 22 and draws <= 64 without public preconditions.
#[derive(Default)]
struct QueryScan {
    accepted: [u32; QUERY_COUNT],
    accepted_len: usize,
    draws: usize,
}

impl QueryScan {
    /// Checks before each word, with no check after the last word. In
    /// particular, success on word 8 is detected in the next block.
    fn scan(&mut self, block: &[u8; 32]) -> bool {
        for candidate in query_words(block) {
            if self.accepted_len == QUERY_COUNT || self.draws == QUERY_MAX_DRAWS {
                return true;
            }
            self.draws += 1;
            if !self.accepted[..self.accepted_len].contains(&candidate) {
                self.accepted[self.accepted_len] = candidate;
                self.accepted_len += 1;
            }
        }
        false
    }

    fn finish(self) -> Result<[u32; QUERY_COUNT], QuerySampleError> {
        if self.accepted_len == QUERY_COUNT {
            Ok(self.accepted)
        } else {
            Err(QuerySampleError::DrawLimitExhausted {
                accepted: self.accepted_len,
                max_draws: QUERY_MAX_DRAWS,
            })
        }
    }
}

impl Transcript {
    /// Unframed one-block QM31 draw. Every input block succeeds.
    pub fn r0_challenge_qm31(&mut self) -> QM31 {
        qm31_sample(&self.squeeze_block())
    }

    /// Unframed one-block ordinary WideExact draw, including zero.
    pub fn r0_challenge_ordinary(&mut self) -> WideExact {
        ordinary_sample(&self.squeeze_block())
    }

    /// Unframed one-block nonzero WideExact draw.
    pub fn r0_challenge_gamma(&mut self) -> WideExact {
        gamma_sample(&self.squeeze_block())
    }

    /// Unframed one-block circle draw with the selected fixed fallback.
    pub fn r0_challenge_circle(&mut self, row: CircleRow) -> SecureCirclePoint {
        circle_sample(&self.squeeze_block(), row)
    }

    /// Unframed ordered q22 sample. At most eight squeeze/advance pairs;
    /// a failed result is a verifier rejection. Unused words are discarded.
    ///
    /// Matches `challenge_queries_without_replacement(22, 1<<18, 64)` in
    /// output and final state, including its extra block after success at
    /// draws 24, 32, 40, 48, or 56. Success at draw 64 uses only eight blocks.
    pub fn r0_challenge_queries(&mut self) -> Result<[u32; QUERY_COUNT], QuerySampleError> {
        let mut scan = QueryScan::default();
        for _ in 0..8 {
            if scan.draws == QUERY_MAX_DRAWS {
                break;
            }
            // squeeze_block performs both squeeze and advance before scan.
            let block = self.squeeze_block();
            if scan.scan(&block) {
                break;
            }
        }
        scan.finish()
    }

    /// One provisional labeled absorb, then the sampler for this row:
    ///
    /// - 0..=24: λ, χ, θ, zc₀..₉, μ, η, semantic α₀..₉ (QM31).
    /// - 25..=26: first/second circle point.
    /// - 27: gamma (nonzero WideExact).
    /// - 28..=30: κ, τ, opening α₀ (ordinary WideExact).
    /// - 31: ordered query set S (22 fibres).
    ///
    /// Pass `&[]` on message-free rows: the absorb is still performed.
    /// Message encoding and labels are PROVISIONAL pending S1's SPEC.md;
    /// the caller supplies canonical bytes and is responsible for row order.
    /// An invalid row leaves the transcript unchanged. Query failure leaves
    /// it at the final advanced state and must cause verifier rejection.
    pub fn r0_sample_row(
        &mut self,
        row: u8,
        canonical_message: &[u8],
    ) -> Result<R0Challenge, R0RowError> {
        let label = label::R0_ROW(row).ok_or(R0RowError::InvalidRow { row })?;
        self.absorb(label, canonical_message);
        Ok(match row {
            0..=24 => R0Challenge::Qm31(self.r0_challenge_qm31()),
            25 => R0Challenge::Circle(self.r0_challenge_circle(CircleRow::First)),
            26 => R0Challenge::Circle(self.r0_challenge_circle(CircleRow::Second)),
            27 => R0Challenge::Wide(self.r0_challenge_gamma()),
            28..=30 => R0Challenge::Wide(self.r0_challenge_ordinary()),
            // Validated above, so the remaining row is 31.
            _ => R0Challenge::Queries(self.r0_challenge_queries().map_err(R0RowError::Queries)?),
        })
    }
}

/// SPEC §2 adapter for callers that materialize all eight squeeze/advance
/// pairs before scanning. Returns scanOut's selected state, which can precede
/// the eighth advance. The sampler and its stop test are shared with R-B.
pub fn queries_from_pairs(
    blocks: &[[u8; 32]; 8],
    advances: &[[u8; 32]; 8],
) -> Result<([u32; QUERY_COUNT], [u8; 32]), QuerySampleError> {
    let mut scan = QueryScan::default();
    let mut state = advances[7];
    for k in 0..8 {
        if scan.scan(&blocks[k]) {
            state = advances[k];
            break;
        }
    }
    Ok((scan.finish()?, state))
}

#[cfg(test)]
mod tests;
