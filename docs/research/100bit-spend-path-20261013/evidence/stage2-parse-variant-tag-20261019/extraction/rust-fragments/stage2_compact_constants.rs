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