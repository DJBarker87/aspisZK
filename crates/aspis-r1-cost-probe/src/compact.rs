//! ADOPTED R1 PROOF FORMAT (PREREG-PROOF-SIZE-2, 2026-10-19; prototype from
//! the proof-size feasibility test). UNPROVED: PROOF-SIZE-OBLIGATIONS.
//!
//! Compact QM31 storage for the 455 proof values that the shipped format
//! stores as 32-byte WideExact with the high QM31 half required to be zero:
//! every value of semantic rows 14..26 (426) and the 29 `y1` values. They are
//! stored as their 16-byte canonical QM31 encoding; `expand_*` rebuilds the
//! logical 32-byte form (zero high half) before any hashing, so every
//! Fiat-Shamir message and record keeps its shipped byte definition.
//!
//! Stored layout (`MAGIC`, variant S2 only):
//! header 16 | compact semantic 7,015 | compact y1 464 | inactive 32 |
//! round0 224 | folded root 32 | round1 224 | final 2,048 |
//! 22 openings x 832 (C1 values 480, C2 values 128, C1 salt, C2 salt,
//! folded values 128, folded salt) | six fixed node slots, batch A then
//! batch B, each batch C1, C2, folded (`SLOT_NODES`). Batch A = queries
//! 0..SPLIT, batch B = SPLIT..22. Fixed length (lead ruling 2026-10-19): each
//! slot holds its multiproof's nodes followed by zero bytes up to the slot's
//! worst-case node count; the padding must be zero and is hashed with the
//! rest of the stored bytes.
use crate::r1_wire::row_shape;
use alloc::vec::Vec;
use aspis_core::field::QM31;

pub const MAGIC: &[u8; 8] = b"R1P3CB18";
pub const HEADER: usize = 16;
pub const SPLIT: usize = 10;
pub const QUERIES: usize = 22;
pub const SEMANTIC_ROWS: u8 = 27;
/// Logical (shipped) semantic bytes: root 32 + 27 framed records.
pub const LOGICAL_SEMANTIC: usize = crate::verifier::SEMANTIC_BYTES;
/// Values with an implied zero high half: rows 14..=26.
pub const SEMANTIC_COMPACT_VALUES: usize = 1 + 10 * 28 + (87 + 29) + 29;
pub const COMPACT_SEMANTIC: usize = LOGICAL_SEMANTIC - 16 * SEMANTIC_COMPACT_VALUES;
pub const COMPACT_Y1: usize = 29 * 16;
pub const LOGICAL_Y1: usize = 29 * 32;
pub const OPENING: usize = 480 + 128 + 32 + 32 + 128 + 32;
pub const OFF_SEMANTIC: usize = HEADER;
pub const OFF_Y1: usize = OFF_SEMANTIC + COMPACT_SEMANTIC;
pub const OFF_INACTIVE: usize = OFF_Y1 + COMPACT_Y1;
pub const OFF_ROUND0: usize = OFF_INACTIVE + 32;
pub const OFF_FOLDED_ROOT: usize = OFF_ROUND0 + 224;
pub const OFF_ROUND1: usize = OFF_FOLDED_ROOT + 32;
pub const OFF_FINAL: usize = OFF_ROUND1 + 224;
pub const FINAL_LEN: usize = 64;
pub const OFF_OPENINGS: usize = OFF_FINAL + FINAL_LEN * 32;
pub const OFF_NODES: usize = OFF_OPENINGS + QUERIES * OPENING;
/// Bytes before the multiproof nodes (28,359).
pub const FIXED: usize = OFF_NODES;
/// Worst-case supplied nodes over all query sets (S1 counting bound).
pub const MAX_NODES: usize = 2 * (146 + 172) + (128 + 150);
pub const MAX_PROOF: usize = FIXED + 32 * MAX_NODES;
/// Worst-case node counts per slot: [C1 A, C2 A, folded A, C1 B, C2 B, folded B].
pub const SLOT_NODES: [usize; 6] = [146, 146, 128, 172, 172, 150];
/// Byte offset of each slot inside the stored proof.
pub const fn slot_offset(slot: usize) -> usize {
    let mut at = OFF_NODES;
    let mut i = 0;
    while i < slot {
        at += 32 * SLOT_NODES[i];
        i += 1;
    }
    at
}
/// The candidate's one stored length.
pub const PROOF_BYTES: usize = MAX_PROOF;
const _: () = assert!(slot_offset(6) == MAX_PROOF);
const _: () = assert!(SEMANTIC_COMPACT_VALUES == 426 && COMPACT_SEMANTIC == 7015);
const _: () = assert!(FIXED == 28_359 && MAX_PROOF == 57_607);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CodecError {
    Length,
    NonZeroHigh,
    NonCanonical,
}

/// Is a semantic row's payload made of implied-zero-high values?
#[inline(always)]
fn compact_row(row: u8) -> bool {
    row >= 14
}

/// Encoder (prover side): logical semantic bytes -> compact. Refuses any
/// value whose high half is not zero (such a value has no compact form).
pub fn compact_semantic(logical: &[u8], out: &mut Vec<u8>) -> Result<(), CodecError> {
    if logical.len() != LOGICAL_SEMANTIC {
        return Err(CodecError::Length);
    }
    out.extend_from_slice(&logical[..32]);
    let mut at = 32;
    for row in 0..SEMANTIC_ROWS {
        let size = row_shape(row).ok_or(CodecError::Length)?.1;
        out.extend_from_slice(&logical[at..at + 5]);
        at += 5;
        if compact_row(row) {
            compact_values(&logical[at..at + size], out)?;
        } else {
            out.extend_from_slice(&logical[at..at + size]);
        }
        at += size;
    }
    if at != logical.len() {
        return Err(CodecError::Length);
    }
    Ok(())
}

pub fn compact_values(logical: &[u8], out: &mut Vec<u8>) -> Result<(), CodecError> {
    if logical.len() % 32 != 0 {
        return Err(CodecError::Length);
    }
    for v in logical.chunks_exact(32) {
        if v[16..].iter().any(|&b| b != 0) {
            return Err(CodecError::NonZeroHigh);
        }
        out.extend_from_slice(&v[..16]);
    }
    Ok(())
}

/// Decoder (verifier side): compact values -> logical 32-byte values with a
/// zero high half. Canonicality is not checked here: the verifier checks the
/// stored `y1` values in its strict scan and the rebuilt semantic records in
/// the shipped `Prefix::parse` (one check per value, as in the shipped path).
#[inline(always)]
pub fn expand_values(encoded: &[u8], out: &mut [u8]) -> Result<(), CodecError> {
    if encoded.len() % 16 != 0 || out.len() != 2 * encoded.len() {
        return Err(CodecError::Length);
    }
    for (k, c) in encoded.chunks_exact(16).enumerate() { let o = &mut out[32 * k..32 * k + 32];
        o[..16].copy_from_slice(c);
        o[16..].fill(0);
    }
    Ok(())
}

/// Every stored compact value is a canonical QM31.
pub fn check_values(encoded: &[u8]) -> Result<(), CodecError> {
    for c in encoded.chunks_exact(16) {
  match QM31::from_le_bytes(c) { Some(_) => {} None => return Err(CodecError::NonCanonical) }
    }
    Ok(())
}

/// Decoder: compact semantic -> logical semantic (framing bytes copied;
/// the shipped `Prefix::parse` then checks tag, length and every limb).
pub fn expand_semantic(encoded: &[u8], out: &mut [u8]) -> Result<(), CodecError> {
    if encoded.len() != COMPACT_SEMANTIC || out.len() != LOGICAL_SEMANTIC {
        return Err(CodecError::Length);
    }
    out[..32].copy_from_slice(&encoded[..32]);
    let (mut src, mut dst) = (32, 32);
    for row in 0..SEMANTIC_ROWS {
        let Some((_, size)) = row_shape(row) else { return Err(CodecError::Length) };
        out[dst..dst + 5].copy_from_slice(&encoded[src..src + 5]);
        src += 5;
        dst += 5;
        if compact_row(row) {
            expand_values(&encoded[src..src + size / 2], &mut out[dst..dst + size])?;
            src += size / 2;
        } else {
            out[dst..dst + size].copy_from_slice(&encoded[src..src + size]);
            src += size;
        }
        dst += size;
    }
    if src != encoded.len() || dst != out.len() {
        return Err(CodecError::Length);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn layout_constants() {
        assert_eq!(LOGICAL_SEMANTIC, 13_831);
        assert_eq!(COMPACT_SEMANTIC + 16 * 426, 13_831);
        assert_eq!(OPENING, 832);
    }
    #[test]
    fn values_roundtrip_and_reject() {
        let mut logical = [0u8; 64];
        logical[0] = 5;
        logical[32] = 7;
        let mut c = Vec::new();
        compact_values(&logical, &mut c).unwrap();
        assert_eq!(c.len(), 32);
        let mut back = [0xffu8; 64];
        expand_values(&c, &mut back).unwrap();
        assert_eq!(back, logical);
        let mut high = logical;
        high[20] = 1;
        assert_eq!(compact_values(&high, &mut Vec::new()), Err(CodecError::NonZeroHigh));
        let mut bad = c.clone();
        bad[0..4].copy_from_slice(&0x7fff_ffffu32.to_le_bytes());
        assert_eq!(check_values(&bad), Err(CodecError::NonCanonical));
    }
}

/// Differential test of `check_values` and `expand_semantic` against the frozen bodies (compact.rs
/// 139-145, 148-172), comparing the result and the whole output buffer.
#[cfg(test)]
mod ok_or_explicit_match {
    extern crate std;
    use super::*;
    fn old_check_values(compact: &[u8]) -> Result<(), CodecError> {
        for c in compact.chunks_exact(16) {
            QM31::from_le_bytes(c).ok_or(CodecError::NonCanonical)?;
        }
        Ok(())
    }
    fn old_expand_semantic(compact: &[u8], out: &mut [u8]) -> Result<(), CodecError> {
        if compact.len() != COMPACT_SEMANTIC || out.len() != LOGICAL_SEMANTIC {
            return Err(CodecError::Length);
        }
        out[..32].copy_from_slice(&compact[..32]);
        let (mut src, mut dst) = (32, 32);
        for row in 0..SEMANTIC_ROWS {
            let size = row_shape(row).ok_or(CodecError::Length)?.1;
            out[dst..dst + 5].copy_from_slice(&compact[src..src + 5]);
            src += 5;
            dst += 5;
            if compact_row(row) {
                expand_values(&compact[src..src + size / 2], &mut out[dst..dst + size])?;
                src += size / 2;
            } else {
                out[dst..dst + size].copy_from_slice(&compact[src..src + size]);
                src += size;
            }
            dst += size;
        }
        if src != compact.len() || dst != out.len() {
            return Err(CodecError::Length);
        }
        Ok(())
    }
    fn next(s: &mut u64) -> u64 { *s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407); *s >> 11 }
    /// Little-endian 4-byte limbs, mostly canonical M31 values, with the edges 0, p - 1, p, p + 1 and 2^32 - 1;
    /// with probability 1/4 per 16-byte group the group is zero (so wide values with a zero high half occur).
    fn limbs(s: &mut u64, n: usize) -> std::vec::Vec<u8> {
        let mut out = std::vec::Vec::new();
        while out.len() < n {
            let zero = next(s) % 4 == 0;
            for _ in 0..4 {
                let v = if zero { 0 } else { match next(s) % 32 { 0 => 0, 1 => 0x7fff_fffe, 2 => 0x7fff_ffff, 3 => 0x8000_0000, 4 => u32::MAX, _ => (next(s) as u32) % 0x7fff_ffff } };
                out.extend_from_slice(&v.to_le_bytes());
            }
        }
        out.truncate(n);
        out
    }
    #[test]
    fn same_result_and_output() {
        let mut s = 5u64;
        let mut seen = [0usize; 2];
        for n in 0..20_000 {
            let b = limbs(&mut s, 16 * (n % 11) + if n % 17 == 0 { 3 } else { 0 });
            let r = check_values(&b);
            seen[r.is_ok() as usize] += 1;
            assert_eq!(r, old_check_values(&b));
        }
        assert!(seen[0] > 100 && seen[1] > 100);
        for n in 0..200 {
            let len_c = if n % 10 == 9 { COMPACT_SEMANTIC - 16 } else { COMPACT_SEMANTIC };
            let len_o = if n % 10 == 8 { LOGICAL_SEMANTIC + 1 } else { LOGICAL_SEMANTIC };
            let c = limbs(&mut s, len_c);
            let fill = (n % 3) as u8 * 0x55;
            let mut a = std::vec![fill; len_o];
            let mut b = a.clone();
            assert_eq!(expand_semantic(&c, &mut a), old_expand_semantic(&c, &mut b));
            assert_eq!(a, b);
        }
    }
}

/// Differential test of `expand_values` against the frozen body (compact.rs 126-136), comparing the
/// result and the whole output buffer on every length class (aligned or not, matching or not).
#[cfg(test)]
mod expand_values_indexed {
    extern crate std;
    use super::*;
    fn old_expand_values(compact: &[u8], out: &mut [u8]) -> Result<(), CodecError> {
        if compact.len() % 16 != 0 || out.len() != 2 * compact.len() {
            return Err(CodecError::Length);
        }
        for (c, o) in compact.chunks_exact(16).zip(out.chunks_exact_mut(32)) {
            o[..16].copy_from_slice(c);
            o[16..].fill(0);
        }
        Ok(())
    }
    #[test]
    fn same_output_and_error() {
        let mut state = 0x9e37_79b9_7f4a_7c15u64;
        for n in [0usize, 1, 15, 16, 17, 31, 32, 48, 160, 464, 1600, 16 * 426, 16 * 300] {
            for extra in [0usize, 1, 16, 32] {
                for fill in [0u8, 0xa5, 0xff] {
                    let input: std::vec::Vec<u8> = (0..n).map(|_| { state = state.wrapping_mul(6364136223846793005).wrapping_add(1); (state >> 56) as u8 }).collect();
                    for out_len in [2 * n, 2 * n + extra, (2 * n).saturating_sub(extra)] {
                        let mut a = std::vec![fill; out_len];
                        let mut b = a.clone();
                        assert_eq!(expand_values(&input, &mut a), old_expand_values(&input, &mut b), "{n} {out_len}");
                        assert_eq!(a, b, "{n} {out_len}");
                    }
                }
            }
        }
    }
}
