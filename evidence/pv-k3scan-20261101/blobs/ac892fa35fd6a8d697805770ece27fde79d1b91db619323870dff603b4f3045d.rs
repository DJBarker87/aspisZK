//! D13: fixed row → natural-coefficient permutation π.
//!
//! Historical order rule:
//! `docs/research/v8-full-view-zk-20260912/tools/r16_basis_transport.rs:10–63`.
//! The first 89 inactive rows legal in all sixteen semantic columns (excluding
//! row 1014) precede the remaining increasing rows, with pivot 1023 last.
//! Only that permutation is used: the historical pivot-sum replacement and
//! its subtractive dual are NOT part of D13.
//!
//! `aspis-statement/examples/r0_transport_inventory.rs` derives the pads from
//! `pool_v1_pair_forest_relation_free_mask_cells_v1` and
//! `pool_v1_pair_forest_copy_active_rows_v1`. Its `--check` and the statement
//! integration test audit this fixed no_std table without a dependency cycle.
use super::{Message, MESSAGE_LEN};

include!("transport_pads.rs");

pub const PADS: usize = 89;
pub const PIVOT: usize = 1023;
/// π⁻¹: coefficient index → semantic row.
pub const COEFFICIENT_TO_ROW: [u16; MESSAGE_LEN] = order();
/// π: semantic row → coefficient index.
pub const ROW_TO_COEFFICIENT: [u16; MESSAGE_LEN] = inverse();

const fn order() -> [u16; MESSAGE_LEN] {
    assert!(PAD_ROWS.len() == PADS);
    let mut out = [0; MESSAGE_LEN];
    let mut used = [false; MESSAGE_LEN];
    let mut j = 0;
    while j < PADS {
        let r = PAD_ROWS[j] as usize;
        assert!(r < PIVOT && r != 1014 && !used[r]);
        out[j] = PAD_ROWS[j];
        used[r] = true;
        j += 1;
    }
    let mut r = 0;
    while r < PIVOT {
        if !used[r] {
            out[j] = r as u16;
            j += 1;
        }
        r += 1;
    }
    assert!(j == PIVOT);
    out[PIVOT] = PIVOT as u16;
    out
}

const fn inverse() -> [u16; MESSAGE_LEN] {
    let mut out = [0; MESSAGE_LEN];
    let mut j = 0;
    while j < MESSAGE_LEN {
        out[COEFFICIENT_TO_ROW[j] as usize] = j as u16;
        j += 1;
    }
    out
}

/// t ∘ π⁻¹. The same permutation transports row-indexed linear weights;
/// pairing a transported message and weight preserves their row-space dot.
pub fn to_coefficients<T: Copy>(rows: &Message<T>) -> Message<T> {
    core::array::from_fn(|j| rows[usize::from(COEFFICIENT_TO_ROW[j])])
}

pub fn to_rows<T: Copy>(coefficients: &Message<T>) -> Message<T> {
    core::array::from_fn(|r| coefficients[usize::from(ROW_TO_COEFFICIENT[r])])
}
