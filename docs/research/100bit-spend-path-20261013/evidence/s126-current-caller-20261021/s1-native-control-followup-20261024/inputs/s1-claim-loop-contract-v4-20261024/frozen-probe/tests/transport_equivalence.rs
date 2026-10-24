use aspis_core::field::{CM31, M31, QM31, P};
use aspis_r1_cost_probe::{transport::Variant, weights::Weights};

const DOCUMENTED_TAU: [usize; 5] = [3, 4, 2, 0, 1];

fn documented_inverse_row(j: usize) -> usize {
    let mut row = 0;
    for d in 0..5 {
        row |= ((j >> (2 * d)) & 3) << (2 * DOCUMENTED_TAU[d]);
    }
    row
}

fn independent_dense_row(j: usize) -> usize {
    ((j & 3) << 6)
        + (((j >> 2) & 3) << 8)
        + (((j >> 4) & 3) << 4)
        + ((j >> 6) & 3)
        + (((j >> 8) & 3) << 2)
}

fn next(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
    let mut value = *state;
    value = (value ^ (value >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    value = (value ^ (value >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    value ^ (value >> 31)
}

fn random_k(state: &mut u64) -> QM31 {
    let mut scalar = || M31((next(state) % u64::from(P)) as u32);
    QM31 {
        c0: CM31 { a: scalar(), b: scalar() },
        c1: CM31 { a: scalar(), b: scalar() },
    }
}

fn eq_at_row(points: &[QM31; 10], row: usize) -> QM31 {
    (0..10).fold(QM31::ONE, |weight, b| {
        let point = points[9 - b];
        weight.mul(if (row >> b) & 1 == 0 {
            QM31::ONE.sub(point)
        } else {
            point
        })
    })
}

#[test]
fn s_transport_is_a_bijection_and_matches_documented_pi_inverse() {
    let indices = core::array::from_fn::<_, 1024, _>(|j| j);
    for variant in [Variant::S1, Variant::S2] {
        let mut seen = [false; 1024];
        for j in 0..1024 {
            let row = variant.row(j);
            assert_eq!(row, documented_inverse_row(j), "{variant:?}, coefficient {j}");
            assert_eq!(row, independent_dense_row(j), "dense inverse, {variant:?}, coefficient {j}");
            assert!(!seen[row], "duplicate row {row} in {variant:?}");
            seen[row] = true;
        }
        assert!(seen.into_iter().all(|present| present));

        let coefficients: [u16; 1024] = core::array::from_fn(|j| (j as u16).wrapping_mul(197));
        let rows = variant.rows(&coefficients);
        assert_eq!(variant.coefficients(&rows), coefficients);
        assert_eq!(variant.rows(&variant.coefficients(&indices)), indices);
    }

    for j in 0..1024 {
        assert_eq!(Variant::D.row(j), aspis_core::r0::transport::COEFFICIENT_TO_ROW[j] as usize);
    }
}

#[test]
fn s1_s2_point_weights_match_independent_row_eq_products() {
    let mut state = 0x243f_6a88_85a3_08d3;
    for variant in [Variant::S1, Variant::S2] {
        for case in 0..8 {
            let alpha: [QM31; 10] = core::array::from_fn(|_| random_k(&mut state));
            let z = core::array::from_fn(|_| aspis_core::circle::SecureCirclePoint {
                x: random_k(&mut state),
                y: random_k(&mut state),
            });
            let weights = Weights::new(variant, &alpha, &z).unwrap();
            for kind in 1..=3 {
                let k = kind - 1;
                for j in 0..1024 {
                    let expected = eq_at_row(&weights.points[k], documented_inverse_row(j));
                    assert_eq!(weights.raw(kind, j), expected,
                        "{variant:?}, random vector {case}, point {k}, coefficient {j}");
                }
            }
        }
    }
}
