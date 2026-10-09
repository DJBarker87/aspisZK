//! Candidate-only group contractions for R36.
//!
//! This file deliberately owns no geometry or transcript code.  Callers pass
//! the retained normal/carry/high coefficient arrays and the retained edge
//! relation.  Thus public support shape is the only thing that can change the
//! work; coefficient values never select a path.
use super::corelib;
use corelib::field::{
    qm31_dot, qm31_sum_products3_prepared, qm31_sum_products4, PreparedQm31Multiplier, M31, QM31,
};

pub(super) struct Plan {
    normal: [QM31; 16],
    carry: [QM31; 3],
    high: [QM31; 16],
    prepared_carry: [PreparedQm31Multiplier; 3],
}

impl Plan {
    pub(super) fn new(normal: [QM31; 16], carry: [QM31; 3], high: [QM31; 16]) -> Self {
        let prepared_carry = core::array::from_fn(|i| PreparedQm31Multiplier::new(carry[i]));
        Self {
            normal,
            carry,
            high,
            prepared_carry,
        }
    }

    /// Exact normal/carry row sums, using the existing lazy dot and prepared
    /// three-lane helper.  The split at three is part of the source shape.
    #[inline]
    fn row_sum(&self, row: &[QM31]) -> (QM31, QM31) {
        assert!(row.len() <= 16);
        let mut normal_values = [QM31::ZERO; 16];
        normal_values[..row.len()].copy_from_slice(row);
        let normal = qm31_dot(&self.normal[..row.len()], &normal_values[..row.len()]);
        let carry = match row.len() {
            0 => QM31::ZERO,
            1 => self.carry[0].mul(row[0]),
            2 => self.carry[0].mul(row[0]).add(self.carry[1].mul(row[1])),
            _ => qm31_sum_products3_prepared(&self.prepared_carry, &[row[0], row[1], row[2]]),
        };
        (normal, carry)
    }

    /// Exact replacement for the scalar four-term dot in `Kernel::contract`.
    /// `edges(j)` must return the same ordered `(source, M31 scale)` pairs as
    /// the retained implementation; no edge, mask, or terminal term is
    /// omitted here.
    pub(super) fn contract(
        &self,
        rows: &[[QM31; 16]; 64],
        edges: impl Fn(usize) -> &'static [(usize, M31)],
    ) -> [QM31; 4] {
        let sums: [(QM31, QM31); 64] = core::array::from_fn(|g| self.row_sum(&rows[g]));
        let mut out = [QM31::ZERO; 4];
        for group in 0..4 {
            let mut left = [QM31::ZERO; 4];
            let mut right = [QM31::ZERO; 4];
            for lane in 0..16 {
                let j = group * 16 + lane;
                let mut value = sums[j].0;
                for &(source, scale) in edges(j) {
                    if source < 64 {
                        value = value.add(sums[source].1.mul_m31(scale));
                    }
                }
                // Keep the four-lane accumulation shape used by the existing
                // helper; split each 16-lane group into four exact dots.
                let slot = lane % 4;
                left[slot] = self.high[lane];
                right[slot] = value;
                if slot == 3 {
                    out[group] = out[group].add(qm31_sum_products4(left, right));
                }
            }
        }
        for value in &mut out {
            for _ in 0..8 {
                *value = value.half();
            }
        }
        out
    }
}
