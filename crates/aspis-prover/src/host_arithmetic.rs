//! Prover-local selected mask/polynomial arithmetic. Field operation order
//! is copied literally; no Horner regrouping or raw-limb normalization occurs.
use aspis_core::field::{CM31, M31, QM31};
use aspis_core::state_only_hiding::{
    STATE_ONLY_HIDING_C1_COLUMNS, STATE_ONLY_HIDING_FACTOR_DEGREE,
    STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS, STATE_ONLY_HIDING_SUMCHECK_ROUNDS,
};
use aspis_core::state_only_sumcheck::StateOnlySumcheckPolynomial;
const FACTOR_EXPONENTS: [u8; STATE_ONLY_HIDING_C1_COLUMNS] =
    [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 13, 25];
const MASK_ONLY_FACTOR_EXPONENTS: [u8; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS] =
    [1, 3, 5, 7, 9, 11, 15, 17, 19, 21];
#[inline(always)]
fn cm31_mul_i(value: CM31) -> CM31 {
    CM31::new(value.b.neg(), value.a)
}

#[inline(always)]
fn cm31_mul_r(value: CM31) -> CM31 {
    CM31::new(value.a.double().sub(value.b), value.a.add(value.b.double()))
}

/// Multiply by one of `(1,i,u,iu)` without a generic QM31 product.
#[inline(always)]
fn mul_tower_basis(value: QM31, coordinate: usize) -> QM31 {
    match coordinate {
        0 => value,
        1 => QM31 {
            c0: cm31_mul_i(value.c0),
            c1: cm31_mul_i(value.c1),
        },
        2 => QM31 {
            c0: cm31_mul_r(value.c1),
            c1: value.c0,
        },
        3 => QM31 {
            c0: cm31_mul_i(cm31_mul_r(value.c1)),
            c1: cm31_mul_i(value.c0),
        },
        _ => panic!("state-only hiding tower coordinate out of range"),
    }
}

#[inline(always)]
fn selected_mask_linears(point: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS]) -> (QM31, QM31) {
    let mut suffix = QM31::ZERO;
    let mut weighted = QM31::ZERO;
    let mut variable = STATE_ONLY_HIDING_SUMCHECK_ROUNDS;
    while variable > 0 {
        variable -= 1;
        suffix = suffix.add(point[variable]);
        if variable != 0 {
            weighted = weighted.add(suffix);
        }
    }
    (
        suffix.mul_m31(M31(3)).add(weighted.mul_m31(M31(22))),
        suffix.mul_m31(M31(275)).add(weighted.mul_m31(M31(150))),
    )
}
#[inline(always)]
fn mask_power_26(value: QM31) -> QM31 {
    let x2 = value.square();
    let x4 = x2.square();
    let x8 = x4.square();
    let x16 = x8.square();
    x16.mul(x8).mul(x2)
}
#[inline(never)]
pub fn state_only_selected_mask_value(
    c1: &[QM31; STATE_ONLY_HIDING_C1_COLUMNS],
    mask_only_c1: &[QM31; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS],
    explicit_g: QM31,
    point: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS],
) -> QM31 {
    let (linear, explicit_linear) = selected_mask_linears(point);
    let mut coefficients = [QM31::ZERO; STATE_ONLY_HIDING_FACTOR_DEGREE + 1];
    let mut column = 0usize;
    while column < STATE_ONLY_HIDING_C1_COLUMNS {
        coefficients[usize::from(FACTOR_EXPONENTS[column])] =
            mul_tower_basis(c1[column], column & 3);
        column += 1;
    }
    let mut column = 0usize;
    while column < STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS {
        coefficients[usize::from(MASK_ONLY_FACTOR_EXPONENTS[column])] =
            mul_tower_basis(mask_only_c1[column], column & 3);
        column += 1;
    }

    let prepared_linear = PreparedQm31Multiplier::new(linear);
    let mut shared = coefficients[STATE_ONLY_HIDING_FACTOR_DEGREE];
    let mut exponent = STATE_ONLY_HIDING_FACTOR_DEGREE;
    while exponent > 0 {
        exponent -= 1;
        shared = prepared_linear.mul(shared).add(coefficients[exponent]);
    }

    shared.add(
        QM31::ONE
            .add(mask_power_26(explicit_linear))
            .mul(explicit_g),
    )
}
#[inline(never)]
pub fn evaluate_state_only_polynomial(
    polynomial: &StateOnlySumcheckPolynomial,
    challenge: QM31,
) -> QM31 {
    let x2 = challenge.square();
    let x3 = challenge.mul(x2);
    let x4 = x2.square();
    let powers = [challenge, x2, x3];
    let prepared_x4 = PreparedQm31Multiplier::new(x4);
    fn block_value(
        polynomial: &StateOnlySumcheckPolynomial,
        powers: [QM31; 3],
        block: usize,
    ) -> QM31 {
        let start = 4 * block;
        polynomial[start].add(qm31_sum_products3(
            powers,
            [
                polynomial[start + 1],
                polynomial[start + 2],
                polynomial[start + 3],
            ],
        ))
    }
    let mut accumulator = block_value(polynomial, powers, 6);
    let mut block = 6usize;
    while block > 0 {
        block -= 1;
        accumulator = prepared_x4
            .mul(accumulator)
            .add(block_value(polynomial, powers, block));
    }
    accumulator
}

// Private prepared carrier copied from field.rs. Explicit functions replace
// the two noncapturing closures whose precise Drop blocks fail preflight.
#[derive(Clone, Copy)]
struct PreparedQm31Multiplier {
    components: [[M31; 3]; 3],
}
#[inline(always)]
fn prepare_component(component: CM31) -> [M31; 3] {
    [component.a, component.b, component.a.add(component.b)]
}
#[inline(always)]
fn prepared_component_mul(left: [M31; 3], right: CM31) -> CM31 {
    let m0 = left[0].mul(right.a);
    let m1 = left[1].mul(right.b);
    let m2 = left[2].mul(right.a.add(right.b));
    CM31 {
        a: m0.sub(m1),
        b: m2.sub(m0).sub(m1),
    }
}
impl PreparedQm31Multiplier {
    #[inline(always)]
    fn new(value: QM31) -> Self {
        Self {
            components: [
                prepare_component(value.c0),
                prepare_component(value.c1),
                prepare_component(value.c0.add(value.c1)),
            ],
        }
    }
    #[inline(always)]
    fn mul(self, rhs: QM31) -> QM31 {
        let m0 = prepared_component_mul(self.components[0], rhs.c0);
        let m1 = prepared_component_mul(self.components[1], rhs.c1);
        let m2 = prepared_component_mul(self.components[2], rhs.c0.add(rhs.c1));
        QM31 {
            c0: m0.add(cm31_mul_r(m1)),
            c1: m2.sub(m0).sub(m1),
        }
    }
}
#[inline(always)]
fn reconstruct_component(channels: [u64; 3]) -> CM31 {
    let m0 = M31::reduce_u64(channels[0]);
    let m1 = M31::reduce_u64(channels[1]);
    let m2 = M31::reduce_u64(channels[2]);
    CM31 {
        a: m0.sub(m1),
        b: m2.sub(m0).sub(m1),
    }
}
#[inline(always)]
fn reconstruct_channels(sums: [[u64; 3]; 3]) -> QM31 {
    let m0 = reconstruct_component(sums[0]);
    let m1 = reconstruct_component(sums[1]);
    let m2 = reconstruct_component(sums[2]);
    QM31 {
        c0: m0.add(cm31_mul_r(m1)),
        c1: m2.sub(m0).sub(m1),
    }
}
#[inline(always)]
fn accumulate_channels(mut sums: [[u64; 3]; 3], left: QM31, right: QM31) -> [[u64; 3]; 3] {
    let left_sum = left.c0.add(left.c1);
    let right_sum = right.c0.add(right.c1);
    let a = [
        [left.c0.a, left.c0.b, left.c0.a.add(left.c0.b)],
        [left.c1.a, left.c1.b, left.c1.a.add(left.c1.b)],
        [left_sum.a, left_sum.b, left_sum.a.add(left_sum.b)],
    ];
    let b = [
        [right.c0.a, right.c0.b, right.c0.a.add(right.c0.b)],
        [right.c1.a, right.c1.b, right.c1.a.add(right.c1.b)],
        [right_sum.a, right_sum.b, right_sum.a.add(right_sum.b)],
    ];
    sums[0][0] += a[0][0].0 as u64 * b[0][0].0 as u64;
    sums[0][1] += a[0][1].0 as u64 * b[0][1].0 as u64;
    sums[0][2] += a[0][2].0 as u64 * b[0][2].0 as u64;
    sums[1][0] += a[1][0].0 as u64 * b[1][0].0 as u64;
    sums[1][1] += a[1][1].0 as u64 * b[1][1].0 as u64;
    sums[1][2] += a[1][2].0 as u64 * b[1][2].0 as u64;
    sums[2][0] += a[2][0].0 as u64 * b[2][0].0 as u64;
    sums[2][1] += a[2][1].0 as u64 * b[2][1].0 as u64;
    sums[2][2] += a[2][2].0 as u64 * b[2][2].0 as u64;
    sums
}
#[inline(always)]
fn qm31_sum_products3(left: [QM31; 3], right: [QM31; 3]) -> QM31 {
    let sums = accumulate_channels([[0u64; 3]; 3], left[0], right[0]);
    let sums = accumulate_channels(sums, left[1], right[1]);
    let sums = accumulate_channels(sums, left[2], right[2]);
    reconstruct_channels(sums)
}
