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
pub fn expand_values(compact: &[u8], out: &mut [u8]) -> Result<(), CodecError> {
    if compact.len() % 16 != 0 || out.len() != 2 * compact.len() {
        return Err(CodecError::Length);
    }
    for (c, o) in compact.chunks_exact(16).zip(out.chunks_exact_mut(32)) {
        o[..16].copy_from_slice(c);
        o[16..].fill(0);
    }
    Ok(())
}

/// Every stored compact value is a canonical QM31.
pub fn check_values(compact: &[u8]) -> Result<(), CodecError> {
    for c in compact.chunks_exact(16) {
        QM31::from_le_bytes(c).ok_or(CodecError::NonCanonical)?;
    }
    Ok(())
}

/// Decoder: compact semantic -> logical semantic (framing bytes copied;
/// the shipped `Prefix::parse` then checks tag, length and every limb).
pub fn expand_semantic(compact: &[u8], out: &mut [u8]) -> Result<(), CodecError> {
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
