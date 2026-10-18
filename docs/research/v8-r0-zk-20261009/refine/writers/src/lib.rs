//! Extraction-friendly copies of the honest pair-forest builder's simple writers
//! (t2b2b/DESIGN-BUILDER-MODEL.txt §6): value aux, occupancy aux, forest path aux,
//! and the bank merge.  Production originals (read-only, origin/codex/100bit-spend-path-20261013):
//!   write_value_aux        crates/aspis-statement/src/pool_v1/pair_trace.rs:401-437
//!   write_occupancy        crates/aspis-statement/src/pool_v1/pair_trace.rs:439-468
//!   relocation copy        crates/aspis-statement/src/pool_v1/pair_forest_trace.rs:225-227 (+48 rows)
//!   write_forest_path_aux  crates/aspis-statement/src/pool_v1/pair_forest_trace.rs:142-159
//!   node_right             crates/aspis-statement/src/pool_v1/pair_forest_trace.rs:131-140
//!   merge_..._banks_v1     crates/aspis-statement/src/pool_v1/pair_forest_trace.rs:281-314
//! Rules: no_std, monomorphic, u32 cells (canonical M31 values below P), plain while loops,
//! no closures, no iterator adapters, at most one loop nest per function, flat arrays.
//! Cells are written at their FINAL forest rows (the production writes legacy rows and the
//! relocation moves rows 960..975 to 1008..1023; +48 preserves the xor-12 geometry).
#![no_std]

/// The M31 modulus.
pub const P: u32 = 0x7fff_ffff;
/// MERKLE_NODE_COMPRESSION_V3_TWEAK (poseidon2.rs:465).
pub const TWEAK: u32 = 0x4153_1005;

/// M31 subtraction on canonical inputs (field.rs:94-119, non-audit branch).
pub fn m31_sub(a: u32, b: u32) -> u32 {
    let s = a + P - b;
    if s >= P {
        s - P
    } else {
        s
    }
}

/// Block 63 (rows 1008..1023), row-major: index = local_row * 16 + column.
pub const AUX_BLOCK_CELLS: usize = 256;

/// write_value_aux at the forest rows.  Requires values[j] < 2^30.
/// Value j's base local row is 2j (row 1008 + 2j): bits 0..9 at the base row,
/// bits 10..19 at base + 1, bits 20..29 at base xor 12, raw value at column 10.
pub fn write_value_block(values: [u32; 3]) -> [u32; AUX_BLOCK_CELLS] {
    let mut block = [0u32; AUX_BLOCK_CELLS];
    let mut j: usize = 0;
    while j < 3 {
        let raw = values[j];
        let base = 2 * j;
        let mut bit: u32 = 0;
        while bit < 30 {
            let row = if bit < 10 {
                base
            } else if bit < 20 {
                base + 1
            } else {
                base ^ 12
            };
            block[row * 16 + (bit % 10) as usize] = (raw >> bit) & 1;
            bit += 1;
        }
        block[base * 16 + 10] = raw;
        j += 1;
    }
    let partial = m31_sub(values[0], values[1]);
    block[6 * 16] = values[0];
    block[6 * 16 + 1] = values[1];
    block[6 * 16 + 2] = partial;
    block[7 * 16] = partial;
    block[7 * 16 + 1] = values[2];
    block
}

/// One pair-leaf occupancy record (pair_tree_profile.rs PoolV1PairLeafWitnessV1 fields used
/// by write_occupancy) plus the optional selected-side bit (0/1, or NO_SELECTED).
#[derive(Clone, Copy)]
pub struct OccRecord {
    pub occupied: u32,
    pub inverse: u32,
    pub commitment: [u32; 8],
    pub selected: u32,
    pub has_selected: bool,
}

/// write_occupancy into one local row (9 = row 1017 input, 10 = row 1018 output).
pub fn write_occupancy_row(
    block: [u32; AUX_BLOCK_CELLS],
    local_row: usize,
    occ: OccRecord,
) -> [u32; AUX_BLOCK_CELLS] {
    let mut block = block;
    let base = local_row * 16;
    block[base] = occ.occupied;
    block[base + 1] = occ.inverse;
    let mut lane: usize = 0;
    while lane < 8 {
        block[base + 2 + lane] = occ.commitment[lane];
        lane += 1;
    }
    if occ.has_selected {
        block[base + 10] = occ.selected;
    }
    block
}

/// The whole aux block 63 as the builder writes it: values, then the input and
/// output occupancy rows (pair_trace.rs:671-688 order).
pub fn write_aux_block(values: [u32; 3], input: OccRecord, output: OccRecord) -> [u32; AUX_BLOCK_CELLS] {
    let block = write_value_block(values);
    let block = write_occupancy_row(block, 9, input);
    write_occupancy_row(block, 10, output)
}

/// Blocks 57..62 (rows 912..1007), row-major: index = local_row * 16 + column.
pub const PATH_BLOCK_CELLS: usize = 96 * 16;

/// pool_v1_pair_forest_path_base_row_v1(level) - 912 for level < 24.
pub fn path_base_local_row(level: usize) -> usize {
    16 * (level / 4) + 1 + 4 * (level % 4)
}

/// write_forest_path_aux for one level < 24.
pub fn write_path_level(
    buf: [u32; PATH_BLOCK_CELLS],
    level: usize,
    bit: u32,
    current: [u32; 8],
    left: [u32; 8],
    right: [u32; 8],
) -> [u32; PATH_BLOCK_CELLS] {
    let mut buf = buf;
    let base = path_base_local_row(level) * 16;
    buf[base] = bit;
    let mut lane: usize = 0;
    while lane < 8 {
        buf[base + 1 + lane] = current[lane];
        buf[base + 16 + lane] = left[lane];
        buf[base + 16 + 8 + lane] = right[lane];
        lane += 1;
    }
    buf
}

/// All 24 path aux levels (relocate_and_extend, pair_forest_trace.rs:216-240).
pub fn write_path_block(
    bits: [u32; 24],
    current: [[u32; 8]; 24],
    left: [[u32; 8]; 24],
    right: [[u32; 8]; 24],
) -> [u32; PATH_BLOCK_CELLS] {
    let mut buf = [0u32; PATH_BLOCK_CELLS];
    let mut level: usize = 0;
    while level < 24 {
        buf = write_path_level(buf, level, bits[level], current[level], left[level], right[level]);
        level += 1;
    }
    buf
}

/// node_right lane 7: the relocation reads the right child back from a node's
/// pre-state by subtracting the tweak (pair_forest_trace.rs:131-140).
pub fn node_right_lane7(pre15: u32) -> u32 {
    m31_sub(pre15, TWEAK)
}

/// 16 columns x 1024 rows, column-major flat: index = column * 1024 + row.
pub const TRACE_CELLS: usize = 16 * 1024;

/// The shape check of merge_pool_v1_pair_forest_trace_banks_v1: the stable bank is
/// zero on rows 544..864 and the late bank is zero outside them.
pub fn merge_check(stable: &[u32; TRACE_CELLS], late: &[u32; TRACE_CELLS]) -> bool {
    let mut ok = true;
    let mut i: usize = 0;
    while i < TRACE_CELLS {
        let row = i % 1024;
        let in_late = row >= 544 && row < 864;
        if in_late {
            if stable[i] != 0 {
                ok = false;
            }
        } else if late[i] != 0 {
            ok = false;
        }
        i += 1;
    }
    ok
}

/// The copy of merge_pool_v1_pair_forest_trace_banks_v1: rows 544..864 from late.
pub fn merge_copy(stable: &[u32; TRACE_CELLS], late: &[u32; TRACE_CELLS]) -> [u32; TRACE_CELLS] {
    let mut out = [0u32; TRACE_CELLS];
    let mut i: usize = 0;
    while i < TRACE_CELLS {
        let row = i % 1024;
        out[i] = if row >= 544 && row < 864 { late[i] } else { stable[i] };
        i += 1;
    }
    out
}
