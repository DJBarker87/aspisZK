//! Exact binary-mask chord transport, using low-mask sharing and a 64-entry high stage.
use super::{dual_fold_four, edges, sample, transpose, EXT, K};
use std::{hint::black_box, time::Instant};

fn basis(a: K, b: K) -> ([K; 16], usize) {
    let a2 = a.mul(a);
    let b2 = b.mul(b);
    let ap = [K::ONE, a2.mul(a), a2, a];
    let bp = [K::ONE, b2.mul(b), b2, b];
    let mut out = [K::ZERO; 16];
    let mut n = 4;
    for j in 0..16 {
        out[j] = if j < 4 {
            ap[j]
        } else if j % 4 == 0 {
            bp[j / 4]
        } else {
            n += 1;
            ap[j % 4].mul(bp[j / 4])
        };
    }
    (out, n)
}
pub fn terminal(masks: &[u16; 64], [a, b, c]: [K; 3], alpha: [K; 4]) -> ([K; 4], usize, usize) {
    let (low, mut products) = basis(alpha[0], alpha[1]);
    let (high, np) = basis(alpha[2], alpha[3]);
    products += np;
    let mut xn = [K::ZERO; 16];
    let mut xc = [K::ZERO; 16];
    let mut yn = [K::ZERO; 16];
    let mut yc = [K::ZERO; 16];
    // Forward local operators: an overflow is an ACTIVE carry into the high row,
    // not an ordinary integer increment of that row.
    for input in 0..16 {
        let y = input & 1;
        let j = input >> 1;
        for (r, s) in edges(j) {
            let dest = 2 * (r % 8) + y;
            if r < 8 {
                xn[dest] = xn[dest].add(low[input].mul_m31(s));
            } else {
                xc[dest] = xc[dest].add(low[input].mul_m31(s));
            }
        }
        if y == 0 {
            yn[input + 1] = yn[input + 1].add(low[input]);
        } else {
            yn[input - 1] = yn[input - 1].add(low[input].half());
            // y²=(1-T2)/2. Preserve bit zero of the line index.
            for (r, s) in edges(j >> 1) {
                let line = (r << 1) | (j & 1);
                let dest = 2 * (line % 8);
                let v = low[input].mul_m31(s).half();
                if line < 8 {
                    yn[dest] = yn[dest].sub(v);
                } else {
                    yc[dest] = yc[dest].sub(v);
                }
            }
        }
    }
    let mut normal = [K::ZERO; 16];
    let mut carry = [K::ZERO; 16];
    for j in 0..16 {
        normal[j] = a.mul(low[j]).add(b.mul(xn[j])).add(c.mul(yn[j]));
        products += 3;
    }
    // x's carry exits only at low positions 0/1; y's only at 0/2.
    // These follow from the largest line destinations 8 and 9 above.
    debug_assert!(xc[2..].iter().all(|v| *v == K::ZERO));
    debug_assert!(yc
        .iter()
        .enumerate()
        .all(|(j, v)| j == 0 || j == 2 || *v == K::ZERO));
    carry[0] = b.mul(xc[0]).add(c.mul(yc[0]));
    carry[1] = b.mul(xc[1]);
    carry[2] = c.mul(yc[2]);
    products += 4;
    let mut distinct = Vec::<u16>::new();
    let mut groups = [0usize; 64];
    for (j, mask) in masks.iter().enumerate() {
        groups[j] = match distinct.iter().position(|m| m == mask) {
            Some(i) => i,
            None => {
                distinct.push(*mask);
                distinct.len() - 1
            }
        };
    }
    let sums: Vec<(K, K)> = distinct
        .iter()
        .map(|mask| {
            let mut n = K::ZERO;
            let mut c = K::ZERO;
            for j in 0..16 {
                if mask & (1 << j) != 0 {
                    n = n.add(normal[j]);
                    c = c.add(carry[j]);
                }
            }
            (n, c)
        })
        .collect();
    let mut out = [K::ZERO; 4];
    for j in 0..64 {
        let mut value = sums[groups[j]].0;
        for (r, s) in edges(j) {
            if r < 64 {
                value = value.add(sums[groups[r]].1.mul_m31(s));
            }
        }
        out[j >> 4] = out[j >> 4].add(value.mul(high[j & 15]));
        products += 1;
    }
    for value in &mut out {
        for _ in 0..8 {
            *value = value.half();
        }
    }
    (out, products, distinct.len())
}
fn reference(masks: &[u16; 64], l: [K; 3], alpha: [K; 4]) -> [K; 4] {
    let mut w = vec![K::ZERO; 2 * EXT];
    for j in 0..1024 {
        if masks[j >> 4] & (1 << (j & 15)) != 0 {
            w[j] = K::ONE;
        }
    }
    dual_fold_four(transpose(&w, l), alpha)
}
fn source_masks(path: &str, name: &str) -> [u16; 64] {
    let text = std::fs::read_to_string(path).unwrap();
    let line = text
        .lines()
        .find(|line| line.starts_with(&format!("pub(crate) const {name}:")))
        .unwrap();
    let values = line.split_once("= [").unwrap().1.split_once(']').unwrap().0;
    let active: Vec<u16> = values
        .split(',')
        .filter(|s| !s.trim().is_empty())
        .map(|s| s.trim().parse().unwrap())
        .collect();
    active
        .into_iter()
        .map(|v| !v)
        .collect::<Vec<_>>()
        .try_into()
        .unwrap()
}
pub fn run() {
    let l = [sample(11), sample(21), sample(31)];
    let mut cases = 0;
    for alpha in [
        [sample(41), sample(51), sample(61), sample(71)],
        [K::ZERO, K::ONE, K::ONE.neg(), K::ZERO],
    ] {
        for index in 0..1024 {
            let mut masks = [0u16; 64];
            masks[index >> 4] = 1 << (index & 15);
            assert_eq!(terminal(&masks, l, alpha).0, reference(&masks, l, alpha));
            cases += 1;
        }
    }
    let alpha = [sample(81), sample(91), sample(101), sample(111)];
    for seed in 0..32u32 {
        let masks = core::array::from_fn(|j| {
            if seed == 0 {
                0
            } else if seed == 1 {
                u16::MAX
            } else {
                (seed.wrapping_mul(65521).wrapping_add(j as u32 * 3449)) as u16
            }
        });
        let chord = if seed == 2 { [K::ZERO; 3] } else { l };
        assert_eq!(
            terminal(&masks, chord, alpha).0,
            reference(&masks, chord, alpha)
        );
        cases += 1;
    }
    println!("PASS {cases} grouped-mask cases including every binary weight basis twice, dense/empty masks, and degenerate challenges");
    for (path, name) in [
        (
            "crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal_constants.rs",
            "ACTIVE_ROW_MASKS",
        ),
        (
            "crates/aspis-statement/src/pool_v1/payment_semantic_terminal_constants.rs",
            "PRIVATE_TRANSFER_ACTIVE_ROW_MASKS",
        ),
        (
            "crates/aspis-statement/src/pool_v1/payment_semantic_terminal_constants.rs",
            "WITHDRAWAL_ACTIVE_ROW_MASKS",
        ),
    ] {
        let masks = source_masks(path, name);
        let (result, n, g) = terminal(&masks, l, alpha);
        assert_eq!(result, reference(&masks, l, alpha));
        let mut times = Vec::new();
        for _ in 0..200 {
            let now = Instant::now();
            black_box(terminal(black_box(&masks), black_box(l), black_box(alpha)));
            times.push(now.elapsed().as_nanos());
        }
        let mean = times.iter().sum::<u128>() / 200;
        times.sort();
        println!("source {name}: groups={g}, QM31 products={n}, mean={mean}ns p50={}ns p95={}ns max={}ns",times[100],times[189],times[199]);
    }
    println!("No dense 1024-entry transform in fast path; 142 generic QM31 products includes challenge powers; 170 mixed products; excludes additions/allocation; no CU claim");
    let masks = source_masks(
        "crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal_constants.rs",
        "ACTIVE_ROW_MASKS",
    );
    for seed in 0..20u32 {
        let ood_points = [
            super::circle::secure_ood_circle_point_from_parameter(sample(seed + 300)).unwrap(),
            super::circle::secure_ood_circle_point_from_parameter(sample(seed + 310)).unwrap(),
        ];
        let l = super::chord(ood_points[0], ood_points[1]);
        let alpha = core::array::from_fn(|j| sample(seed + 130 + j as u32));
        let eta = sample(seed + 150);
        let eta2 = eta.mul(eta);
        let kappa = sample(seed + 160);
        let scales = [K::ONE, kappa, kappa.mul(kappa)];
        let mut original = vec![K::ZERO; 2 * EXT];
        for index in 0..1024 {
            if masks[index >> 4] & (1 << (index & 15)) != 0 {
                original[index] = K::ONE;
            }
        }
        let mut actual = terminal(&masks, l, alpha).0;
        for claim in 0..3 {
            // Source MLE points are big-endian; fast product factors are low-bit first.
            let point: [K; 10] =
                core::array::from_fn(|j| sample(seed + 200 + claim as u32 * 20 + j as u32));
            let pairs = core::array::from_fn(|bit| [K::ONE.sub(point[9 - bit]), point[9 - bit]]);
            let contribution = super::block_terminal(&pairs, alpha, l).0;
            for slot in 0..4 {
                actual[slot] = actual[slot].add(scales[claim].mul(contribution[slot]));
            }
            for index in 0..1024 {
                let mut value = scales[claim];
                for coordinate in 0..10 {
                    value = value.mul(if index & (1 << (9 - coordinate)) != 0 {
                        point[coordinate]
                    } else {
                        K::ONE.sub(point[coordinate])
                    });
                }
                original[index] = original[index].add(value);
            }
        }
        // Retain both original circle-OOD covectors as a conservative control.
        // Their elimination would require the separate image-constraint identity.
        for (which, point) in ood_points.iter().enumerate() {
            let scale = sample(seed + 400 + which as u32);
            let mut factors = [K::ZERO; 10];
            factors[0] = point.y;
            factors[1] = point.x;
            for j in 2..10 {
                factors[j] = super::circle::double_x(factors[j - 1]);
            }
            let pairs = factors.map(|v| [K::ONE, v]);
            let contribution = super::block_terminal(&pairs, alpha, l).0;
            for slot in 0..4 {
                actual[slot] = actual[slot].add(scale.mul(contribution[slot]));
            }
            for index in 0..1024 {
                let value = super::phi(index >> 1, point.x).mul(if index & 1 == 0 {
                    K::ONE
                } else {
                    point.y
                });
                original[index] = original[index].add(scale.mul(value));
            }
        }
        let mut transformed = transpose(&original, l);
        transformed[1023] = transformed[1023].add(eta);
        transformed[1022] = transformed[1022].add(eta2.mul(l[1]));
        transformed[1021] = transformed[1021].sub(eta2.mul(l[2]));
        let a0_2 = alpha[0].mul(alpha[0]);
        let a0_3 = a0_2.mul(alpha[0]);
        let mut image = eta
            .mul(alpha[0])
            .add(eta2.mul(l[1].mul(a0_2).sub(l[2].mul(a0_3))))
            .mul(alpha[1].mul(alpha[2]).mul(alpha[3]));
        for _ in 0..8 {
            image = image.half();
        }
        actual[3] = actual[3].add(image);
        assert_eq!(actual, dual_fold_four(transformed, alpha));
    }
    println!("PASS 20 aggregate relation cases: big-endian three-MLE adapter + two circle-OOD tensors + actual forest mask + sparse image constraints, all four terminal values");
}
