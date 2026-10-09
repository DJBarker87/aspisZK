//! Focused arithmetic control for `r17_group_dot_optimized.rs`.
extern crate aspis_core as corelib;
mod r17_group_dot_optimized;
use corelib::field::{
    qm31_dot, qm31_sum_products3_prepared, PreparedQm31Multiplier, CM31, M31, P, QM31,
};
use r17_group_dot_optimized::Plan;

fn sample(n: u32) -> QM31 {
    QM31 {
        c0: CM31::new(M31(n % P), M31((n * 3 + 7) % P)),
        c1: CM31::new(M31((n * 5 + 11) % P), M31((n * 7 + 13) % P)),
    }
}
static EDGE0: &[(usize, M31)] = &[(0, M31(3))];
static EDGES: [&[(usize, M31)]; 64] = [EDGE0; 64];

fn main() {
    for case in 0..32u32 {
        let normal = core::array::from_fn(|i| sample(case * 17 + i as u32));
        let carry = core::array::from_fn(|i| sample(case * 19 + i as u32 + 100));
        let high = core::array::from_fn(|i| sample(case * 23 + i as u32 + 200));
        let plan = Plan::new(normal, carry, high);
        let rows = core::array::from_fn(|g| {
            core::array::from_fn(|j| sample(case * 97 + (g * 16 + j) as u32 + 300))
        });
        let prepared = core::array::from_fn(|i| PreparedQm31Multiplier::new(carry[i]));
        let probe = [rows[0][0], rows[0][1], rows[0][2]];
        let oracle = carry
            .iter()
            .zip(probe.iter())
            .fold(QM31::ZERO, |s, (&w, &v)| s.add(w.mul(v)));
        assert_eq!(qm31_sum_products3_prepared(&prepared, &probe), oracle);
        let n_oracle = rows[0]
            .iter()
            .zip(normal.iter())
            .fold(QM31::ZERO, |s, (&v, &w)| s.add(w.mul(v)));
        assert_eq!(qm31_dot(&normal, &rows[0]), n_oracle);
        let actual = plan.contract(&rows, |j| EDGES[j]);
        let mut expected = [QM31::ZERO; 4];
        for group in 0..4 {
            for lane in 0..16 {
                let row = &rows[group * 16 + lane];
                let normal_sum = qm31_dot(&normal, row);
                let edge_carry = rows[0][..3]
                    .iter()
                    .zip(carry.iter())
                    .fold(QM31::ZERO, |s, (&v, &w)| s.add(w.mul(v)))
                    .mul_m31(M31(3));
                expected[group] = expected[group].add(high[lane].mul(normal_sum.add(edge_carry)));
            }
        }
        for value in &mut expected {
            for _ in 0..8 {
                *value = value.half();
            }
        }
        assert_eq!(actual, expected);
    }
    println!("PASS: 32 grouped-dot controls; exact modulo-field result and 8 halvings preserved");
    println!("BOUNDARY: zero-edge arithmetic control only; retained geometry, masks, map, transcript, proof premises unchanged");
}
