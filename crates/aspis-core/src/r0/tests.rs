extern crate std;

use super::{basis::*, chord::*, domain::*, encoder::*, fold::*, *};
use crate::field::{WideExact as E, CM31, M31, P, QM31};
use sha2::{Digest, Sha256};
use std::{string::String, vec::Vec};

const KATS: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../results/r0-codes-20261009/kats.txt"
));
fn kat_tokens(name: &str) -> Vec<&str> {
    KATS.lines()
        .find_map(|line| {
            let mut parts = line.split_whitespace();
            (parts.next() == Some(name)).then(|| parts.collect())
        })
        .unwrap()
}
fn kat(name: &str) -> Vec<E> {
    kat_tokens(name)
        .chunks_exact(8)
        .map(|digits| E::from_limbs(core::array::from_fn(|i| digits[i].parse().unwrap())).unwrap())
        .collect()
}
fn indices(name: &str) -> Vec<usize> {
    kat_tokens(name)
        .iter()
        .map(|n| n.parse().unwrap())
        .collect()
}
fn message(seed: u64) -> Message<E> {
    core::array::from_fn(|j| {
        E::from_limbs(core::array::from_fn(|h| {
            let (j, h) = (j as u64, h as u64);
            (((j + 1) * (h + 2) * seed + j * j * (h + 1) + 17 * h + 11) % u64::from(P)) as u32
        }))
        .unwrap()
    })
}
fn alpha() -> E {
    E::from_limbs([2, 3, 5, 7, 11, 13, 17, 19]).unwrap()
}
fn dot<F: CodeField>(a: &[F], b: &[F]) -> F {
    a.iter().zip(b).fold(F::ZERO, |s, (&a, &b)| s.add(a.mul(b)))
}
fn points() -> (Point<E>, Point<E>) {
    let v = kat("points");
    (Point { x: v[0], y: v[1] }, Point { x: v[2], y: v[3] })
}
fn hash(matrix: &[M31]) -> String {
    let mut h = Sha256::new();
    for c in matrix {
        h.update(c.to_le_bytes());
    }
    h.finalize()
        .iter()
        .map(|b| std::format!("{b:02x}"))
        .collect()
}
fn random(seed: &mut u64) -> E {
    E::from_limbs(core::array::from_fn(|_| {
        *seed ^= *seed << 13;
        *seed ^= *seed >> 7;
        *seed ^= *seed << 17;
        (*seed % u64::from(P)) as u32
    }))
    .unwrap()
}
fn circle(t: E) -> Point<E> {
    let t2 = t.mul(t);
    let den = E::ONE.add(t2).try_inv().unwrap();
    Point {
        x: E::ONE.sub(t2).mul(den),
        y: t.add(t).mul(den),
    }
}
fn random_k_circle(seed: &mut u64) -> Point<E> {
    // Deterministic pseudorandom parameters in K\CM31, embedded into E.
    let v = random(seed);
    let mut k = v.c0();
    if k.c1 == CM31::ZERO {
        k.c1 = CM31::ONE;
    }
    circle(E::from_qm31(k))
}

#[test]
fn matrices_recurrence_identity_and_independent_hashes() {
    for size in [BasisSize::Final, BasisSize::Initial] {
        let basis = NaturalBasis::new(size).unwrap();
        let n = size.len();
        assert_eq!(
            hash(basis.matrix()),
            kat_tokens(&std::format!("matrix{n}"))[0]
        );
        assert_eq!(
            hash(basis.inverse_matrix()),
            kat_tokens(&std::format!("inverse{n}"))[0]
        );
        // Every entry of both products, exploiting only known triangularity.
        for i in 0..n {
            for j in 0..n {
                let (mut left, mut right) = (M31::ZERO, M31::ZERO);
                if i <= j {
                    for k in i..=j {
                        left = left
                            .add(basis.matrix()[i * n + k].mul(basis.inverse_matrix()[k * n + j]));
                        right = right
                            .add(basis.inverse_matrix()[i * n + k].mul(basis.matrix()[k * n + j]));
                    }
                }
                let expected = if i == j { M31::ONE } else { M31::ZERO };
                assert_eq!(left, expected, "M M^-1 [{i},{j}]");
                assert_eq!(right, expected, "M^-1 M [{i},{j}]");
            }
        }
        let x = alpha();
        for j in 0..n {
            let polynomial = (0..n).rev().fold(E::ZERO, |p, d| {
                p.mul(x).add(E::from_m31(basis.matrix()[d * n + j]))
            });
            assert_eq!(polynomial, natural(j, x));
        }
        let monomial = message(19)[..n].to_vec();
        let mut converted = std::vec![E::ZERO;n];
        let mut roundtrip = std::vec![E::ZERO;n];
        basis
            .monomial_to_natural(&monomial, &mut converted)
            .unwrap();
        basis
            .natural_to_monomial(&converted, &mut roundtrip)
            .unwrap();
        assert_eq!(roundtrip, monomial);
    }
    let x = M31(3);
    assert_eq!(doubled_factor(0, x), x);
    assert_eq!(doubled_factor(1, x), M31(17));
    assert_eq!(natural(2, x), M31(17));
    assert_ne!(natural(2, x), x.mul(x)); // N_2=2X²−1, not X².
    assert_eq!(natural(3, x), M31(51));
    assert_ne!(natural(3, x), M31(99)); // nor T_3=4X³−3X.
}

#[test]
fn encoder_transform_fold_and_final_kats() {
    let q = message(19);
    let w = message(37);
    let (z0, z1) = points();
    assert_eq!(
        [eval_message(&q, z0), eval_message(&q, z1)].as_slice(),
        kat("ood")
    );
    for (i, expected) in indices("indices").into_iter().zip(kat("initial")) {
        assert_eq!(
            exact_initial_encoder(&q, InitialIndex::new(i).unwrap()),
            expected
        );
    }
    let folded = fold_message(alpha(), &q);
    assert_eq!(folded.as_slice(), kat("fold_message"));
    assert_eq!(dual_fold(alpha(), &w).as_slice(), kat("dual_fold"));
    for (u, expected) in indices("fibres").into_iter().zip(kat("final")) {
        let u = FibreIndex::new(u).unwrap();
        assert_eq!(exact_final_encoder(&folded, u), expected);
        assert_eq!(
            fold_word(alpha(), |i| exact_initial_encoder(&q, i), u).unwrap(),
            expected
        );
    }
    let u = FibreIndex::new(123).unwrap();
    let z = fibre_point(u);
    let values = [q[0], q[1], q[2], q[3]];
    let channels = phi(z.x, z.y, values).unwrap();
    assert_eq!(channels.as_slice(), kat("phi"));
    assert_eq!(phi_inverse(z.x, z.y, channels), values);
    assert_eq!(
        fold_fibre(alpha(), u, values).unwrap(),
        kat("fold_fibre")[0]
    );
    assert_eq!(quarter::<M31>(), M31(536870912));
    assert_eq!(quarter::<E>().mul(E::from_m31(M31(4))), E::ONE);
    for d in 0..256 {
        assert_eq!(fold_message(E::ZERO, &q)[d], q[4 * d]);
        assert_eq!(dual_fold(E::ZERO, &w)[d], w[4 * d]);
    }
    // Random full-support E coefficients, arbitrary E challenges, including 0.
    let mut seed = 0x1248124812481248;
    for challenge in [E::ZERO, E::ONE, random(&mut seed)] {
        let q = core::array::from_fn(|_| random(&mut seed));
        let folded = fold_message(challenge, &q);
        for u in [0, 1, 19, 12345, 262143] {
            let u = FibreIndex::new(u).unwrap();
            assert_eq!(
                fold_word(challenge, |i| exact_initial_encoder(&q, i), u).unwrap(),
                exact_final_encoder(&folded, u)
            );
        }
    }
}

#[test]
fn full_domain_permutation_and_nonbase_chord_no_zeros() {
    let expected = kat("domain");
    for (j, i) in indices("indices").into_iter().enumerate() {
        let z = stored_point::<E>(InitialIndex::new(i).unwrap());
        assert_eq!(
            z,
            Point {
                x: expected[2 * j],
                y: expected[2 * j + 1]
            }
        );
    }
    let mut seed = 0xa341316c8013;
    let (z0, z1) = (random_k_circle(&mut seed), random_k_circle(&mut seed));
    assert_ne!(z0, z1);
    for z in [z0, z1] {
        assert!(z.is_on_circle());
        assert!(
            z.x.to_limbs()[1..].iter().any(|&d| d != 0)
                || z.y.to_limbs()[1..].iter().any(|&d| d != 0)
        );
    }
    let line = Secant::from_points(z0, z1);
    let mut seen = std::vec![false;WORD_LEN];
    let g = CM31::new(M31(2), M31(1268011823));
    for i in 0..WORD_LEN {
        let i = InitialIndex::new(i).unwrap();
        assert_eq!(child_index(parent_index(i), slot_index(i)), i);
        let n = natural_index(i);
        assert!(!seen[n]);
        seen[n] = true;
        let direct = g.pow(1024 * (2 * n as u64 + 1));
        let z = stored_point::<M31>(i);
        assert_eq!(
            z,
            Point {
                x: direct.a,
                y: direct.b
            }
        );
        assert!(z.is_on_circle());
        assert_ne!(z.x, M31::ZERO);
        assert_ne!(z.y, M31::ZERO);
        assert_ne!(
            line.eval(Point {
                x: E::from_m31(z.x),
                y: E::from_m31(z.y)
            }),
            E::ZERO
        );
        if slot_index(i).get() == 0 {
            let u = parent_index(i);
            let direct_line = g.pow(2048 + 8192 * rev18(u) as u64).a;
            assert_eq!(line_node::<M31>(u), direct_line);
        }
    }
    assert!(seen.into_iter().all(|x| x));
}

#[test]
fn chord_interpolation_transpose_and_functional_kats() {
    let basis = NaturalBasis::new(BasisSize::Initial).unwrap();
    let (z0, z1) = points();
    let line = Secant::from_points(z0, z1);
    assert_eq!([line.a, line.b, line.c].as_slice(), kat("secant"));
    let q = message(19);
    for (z1, name) in [
        (z1, "interpolant_x"),
        (
            Point {
                x: z0.x,
                y: z0.y.neg(),
            },
            "interpolant_y",
        ),
    ] {
        let values = [q[0], q[1]];
        let interpolation = interpolant(z0, z1, values).unwrap();
        assert_eq!(&interpolation[..3], kat(name));
        assert!(interpolation[3..].iter().all(|v| *v == E::ZERO));
        assert_eq!(eval_message(&interpolation, z0), values[0]);
        assert_eq!(eval_message(&interpolation, z1), values[1]);
        let pair = interpolation_pair(z0, z1, values).unwrap();
        assert_eq!(
            lift_linear(&basis, &pair.p0, &[pair.p1]).unwrap(),
            interpolation
        );
        let l = Secant::from_points(z0, z1);
        assert_eq!(l.eval(z0), E::ZERO);
        assert_eq!(l.eval(z1), E::ZERO);
    }
    let product = chord_message(&basis, line, &q).unwrap();
    assert_eq!(product.as_slice(), kat("chord_message"));
    let w = message(37);
    let weights = quotient_weights(&basis, line, &w).unwrap();
    assert_eq!(weights.as_slice(), kat("quotient_weights"));
    assert_eq!(dot(&w, &product), dot(&weights, &q));
    assert_eq!(
        [
            e1(&basis, &q).unwrap(),
            e2(&basis, line.b, line.c, &q).unwrap()
        ]
        .as_slice(),
        kat("functionals")
    );
    let row1 = FunctionalWeights::e1(&basis).unwrap();
    let row2 = FunctionalWeights::e2(&basis, line.b, line.c).unwrap();
    assert_eq!(row1, FunctionalWeights::row(|q| e1(&basis, q).unwrap()));
    assert_eq!(
        row2,
        FunctionalWeights::row(|q| e2(&basis, line.b, line.c, q).unwrap())
    );
    assert_eq!(dot(&row1, &q), e1(&basis, &q).unwrap());
    assert_eq!(dot(&row2, &q), e2(&basis, line.b, line.c, &q).unwrap());
    // Off-image high columns: the transpose must match the truncated map.
    for j in [0, 1, 2, 3, 1018, 1019, 1020, 1021, 1022, 1023] {
        let mut unit = [E::ZERO; 1024];
        unit[j] = E::ONE;
        assert_eq!(
            dot(&w, &chord_message(&basis, line, &unit).unwrap()),
            weights[j]
        );
    }
    let (p, r) = polynomial_pair(&basis, &q).unwrap();
    assert_eq!(lift_linear(&basis, &p, &r).unwrap(), q);
    assert_ne!(e1(&basis, &q).unwrap(), E::ZERO);
    // Check the exact monomial truncation independently at the top boundary.
    let mut oversized = std::vec![E::ZERO;514];
    oversized[511] = E::ONE;
    oversized[512] = alpha();
    oversized[513] = E::ONE;
    let lifted = lift_linear(&basis, &oversized, &[]).unwrap();
    let (p, r) = polynomial_pair(&basis, &lifted).unwrap();
    assert_eq!(p[511], E::ONE);
    assert!(p[..511].iter().all(|x| *x == E::ZERO));
    assert!(r.iter().all(|x| *x == E::ZERO));
}

// Test-only independent quotient construction by polynomial long division.
// No operational off-image decoder is implied by this oracle.
fn divide_exact(mut numerator: Vec<E>, denominator: &[E]) -> Vec<E> {
    let degree = denominator.iter().rposition(|&x| x != E::ZERO).unwrap();
    let inv = denominator[degree].try_inv().unwrap();
    let mut out = std::vec![E::ZERO;numerator.len()-degree];
    for j in (degree..numerator.len()).rev() {
        let c = numerator[j].mul(inv);
        out[j - degree] = c;
        for k in 0..=degree {
            numerator[j - degree + k] = numerator[j - degree + k].sub(c.mul(denominator[k]));
        }
    }
    assert!(numerator.iter().all(|&x| x == E::ZERO));
    out
}
fn quotient_pair(line: Secant<E>, p: &[E; 512], r: &[E; 512]) -> (Vec<E>, Vec<E>) {
    let Secant { a, b, c } = line;
    let mut even = std::vec![E::ZERO;514];
    let mut odd = std::vec![E::ZERO;513];
    for j in 0..512 {
        even[j] = even[j].add(a.mul(p[j])).sub(c.mul(r[j]));
        even[j + 1] = even[j + 1].add(b.mul(p[j]));
        even[j + 2] = even[j + 2].add(c.mul(r[j]));
        odd[j] = odd[j].add(a.mul(r[j])).sub(c.mul(p[j]));
        odd[j + 1] = odd[j + 1].add(b.mul(r[j]));
    }
    let den = [
        a.mul(a).sub(c.mul(c)),
        a.mul(b).add(a.mul(b)),
        b.mul(b).add(c.mul(c)),
    ];
    (divide_exact(even, &den), divide_exact(odd, &den))
}

#[test]
fn full_degree_interpolant_difference_quotient_is_encoded() {
    let basis = NaturalBasis::new(BasisSize::Initial).unwrap();
    let mut seed = 0xc42f258;
    let z0 = random_k_circle(&mut seed);
    let z1 = random_k_circle(&mut seed);
    // The second case forces delta's y branch (c=0), including its degree
    // 511 cancellation; do not replace it with a low-degree example.
    for z1 in [
        z1,
        Point {
            x: z0.x,
            y: z0.y.neg(),
        },
    ] {
        let line = Secant::from_points(z0, z1);
        let q: Message<_> = core::array::from_fn(|_| random(&mut seed));
        let values = [eval_message(&q, z0), eval_message(&q, z1)];
        let interpolation = interpolant(z0, z1, values).unwrap();
        let difference = core::array::from_fn(|j| q[j].sub(interpolation[j]));
        let (p, r) = polynomial_pair(&basis, &difference).unwrap();
        let (s, t) = quotient_pair(line, &p, &r);
        assert!(s
            .iter()
            .skip(512)
            .chain(t.iter().skip(512))
            .all(|&x| x == E::ZERO));
        let quotient = lift_linear(&basis, &s, &t).unwrap();
        assert_eq!(e1(&basis, &quotient).unwrap(), E::ZERO);
        assert_eq!(e2(&basis, line.b, line.c, &quotient).unwrap(), E::ZERO);
        // Coefficient equality tests the entire codeword, not just samples.
        assert_eq!(chord_message(&basis, line, &quotient).unwrap(), difference);
        for i in [0, 1, 2, 3, 123, 4000, 1048575] {
            let i = InitialIndex::new(i).unwrap();
            let divided =
                exact_initial_encoder(&difference, i).mul(line.line_word(i).try_inv().unwrap());
            assert_eq!(divided, exact_initial_encoder(&quotient, i));
        }
    }
}

fn generic_roundtrip<F: CodeField + core::fmt::Debug>() {
    let q = core::array::from_fn(|j| F::from_m31(M31(j as u32)));
    let alpha = F::from_m31(M31(7));
    let u = FibreIndex::new(17).unwrap();
    assert_eq!(
        fold_word(alpha, |i| exact_initial_encoder(&q, i), u).unwrap(),
        exact_final_encoder(&fold_message(alpha, &q), u)
    );
    assert_eq!(<F as CodeField>::try_inv(F::ZERO), None);
    let x = F::from_m31(M31(5));
    assert_eq!(x.mul(x.try_inv().unwrap()), F::ONE);
}
#[test]
fn generic_fields_and_rejection_without_panics() {
    generic_roundtrip::<M31>();
    generic_roundtrip::<CM31>();
    generic_roundtrip::<QM31>();
    generic_roundtrip::<E>();
    for i in [WORD_LEN, usize::MAX] {
        assert_eq!(InitialIndex::new(i), Err(Error::IndexOutOfRange));
    }
    for u in [FIBRE_COUNT, usize::MAX] {
        assert_eq!(FibreIndex::new(u), Err(Error::IndexOutOfRange));
    }
    for s in [4, usize::MAX] {
        assert_eq!(SlotIndex::new(s), Err(Error::IndexOutOfRange));
    }
    assert_eq!(
        phi(E::ZERO, E::ONE, [E::ZERO; 4]),
        Err(Error::ZeroDenominator)
    );
    assert_eq!(
        phi(E::ONE, E::ZERO, [E::ZERO; 4]),
        Err(Error::ZeroDenominator)
    );
    let (z0, _) = points();
    assert_eq!(
        interpolant(z0, z0, [E::ZERO; 2]),
        Err(Error::ZeroDenominator)
    );
    let basis = NaturalBasis::new(BasisSize::Final).unwrap();
    assert_eq!(
        basis.monomial_to_natural(&[E::ZERO; 255], &mut [E::ZERO; 256]),
        Err(Error::WrongLength)
    );
    assert_eq!(
        basis.natural_to_monomial(&[E::ZERO; 256], &mut []),
        Err(Error::WrongLength)
    );
    assert_eq!(lift_linear::<E>(&basis, &[], &[]), Err(Error::WrongLength));
    assert_eq!(
        chord_message(
            &basis,
            Secant {
                a: E::ONE,
                b: E::ZERO,
                c: E::ZERO
            },
            &message(19)
        ),
        Err(Error::WrongLength)
    );
    assert_eq!(
        quotient_weights(
            &basis,
            Secant {
                a: E::ONE,
                b: E::ZERO,
                c: E::ZERO
            },
            &message(19)
        ),
        Err(Error::WrongLength)
    );
    assert_eq!(FunctionalWeights::e1::<E>(&basis), Err(Error::WrongLength));
    assert_eq!(
        FunctionalWeights::e2(&basis, E::ONE, E::ZERO),
        Err(Error::WrongLength)
    );
    assert_eq!(e1(&basis, &message(19)), Err(Error::WrongLength));
    assert_eq!(
        e2(&basis, E::ONE, E::ZERO, &message(19)),
        Err(Error::WrongLength)
    );
}
