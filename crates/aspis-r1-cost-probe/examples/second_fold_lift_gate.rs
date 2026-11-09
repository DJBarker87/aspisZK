//! UNPROVED finite source-correspondence gate for the second-fold lift.
//!
//! This example checks exact finite-domain identities and two dense E-valued
//! messages. It is a measurement of the implementation's finite-domain
//! correspondence, not a universal decoder theorem or a security argument.

use aspis_core::{
    field::{CM31, M31, QM31, WideExact as E},
    r0::{basis, domain::FibreIndex, encoder, CodeField, FinalMessage},
};
use aspis_r1_cost_probe::{fast_domain, verifier};

const PARENTS: usize = 1 << 16;
const QUARTER: M31 = M31(536_870_912);

fn double(x: M31) -> M31 {
    x.mul(x).double().sub(M31::ONE)
}

fn wide(limbs: [u32; 8]) -> E {
    let cm = |a, b| CM31::new(M31(a), M31(b));
    E::new(
        QM31 { c0: cm(limbs[0], limbs[1]), c1: cm(limbs[2], limbs[3]) },
        QM31 { c0: cm(limbs[4], limbs[5]), c1: cm(limbs[6], limbs[7]) },
    )
}

fn dense_message(which: u32) -> FinalMessage<E> {
    core::array::from_fn(|i| {
        let b = which * 4096 + i as u32 * 8;
        wide([b + 1, b + 2, b + 3, b + 4, b + 5, b + 6, b + 7, b + 8])
    })
}

fn linear_folded_coefficients(q: &FinalMessage<E>, alpha: E) -> [E; 64] {
    let a2 = alpha.mul(alpha);
    let a3 = a2.mul(alpha);
    core::array::from_fn(|d| {
        q[4 * d]
            .add(alpha.mul(q[4 * d + 1]))
            .add(a2.mul(q[4 * d + 2]))
            .add(a3.mul(q[4 * d + 3]))
    })
}

fn dense_source_and_fold_checks() -> (usize, usize, usize) {
    let alpha_zero = E::ZERO;
    let alpha_wide = wide([7, 11, 13, 17, 19, 23, 29, 31]);
    let mut source_eval_count = 0usize;
    let mut lift_count = 0usize;
    let mut fold_count = 0usize;

    for which in 0..2 {
        let q = dense_message(which);

        // The four depth-2 stride messages each have 64 nonzero coefficients.
        // Evaluate them with the public R0 final encoder at T4(x_v), then
        // compare their four-channel reconstruction with the public source
        // exact final encoder at every one of the four child indices.
        let strides: [[E; 64]; 4] = core::array::from_fn(|s| {
            core::array::from_fn(|d| q[4 * d + s])
        });
        for v in 0..PARENTS {
            let u0 = FibreIndex::new(4 * v).expect("checked domain index");
            let x = fast_domain::line_node(u0);
            let t2x = double(x);
            let t4x = double(t2x);
            let hs: [E; 4] = core::array::from_fn(|s| {
                strides[s]
                    .iter()
                    .enumerate()
                    .fold(E::ZERO, |sum, (d, coefficient)| {
                        sum.add(coefficient.mul(E::from_m31(basis::natural(d, t4x))))
                    })
            });
            let child_x = [
                x,
                x.neg(),
                fast_domain::line_node(FibreIndex::new(4 * v + 2).unwrap()),
                fast_domain::line_node(FibreIndex::new(4 * v + 3).unwrap()),
            ];
            let child_values = [
                hs[0].add(E::from_m31(child_x[0]).mul(hs[1]))
                    .add(E::from_m31(double(child_x[0])).mul(hs[2]))
                    .add(E::from_m31(child_x[0].mul(double(child_x[0]))).mul(hs[3])),
                hs[0].add(E::from_m31(child_x[1]).mul(hs[1]))
                    .add(E::from_m31(double(child_x[1])).mul(hs[2]))
                    .add(E::from_m31(child_x[1].mul(double(child_x[1]))).mul(hs[3])),
                hs[0].add(E::from_m31(child_x[2]).mul(hs[1]))
                    .add(E::from_m31(double(child_x[2])).mul(hs[2]))
                    .add(E::from_m31(child_x[2].mul(double(child_x[2]))).mul(hs[3])),
                hs[0].add(E::from_m31(child_x[3]).mul(hs[1]))
                    .add(E::from_m31(double(child_x[3])).mul(hs[2]))
                    .add(E::from_m31(child_x[3].mul(double(child_x[3]))).mul(hs[3])),
            ];

            let mut actual = [E::ZERO; 4];
            for s in 0..4 {
                actual[s] = encoder::exact_final_encoder(
                    &q,
                    FibreIndex::new(4 * v + s).expect("checked child index"),
                );
                source_eval_count += 1;
                assert_eq!(actual[s], child_values[s], "stride lift mismatch at q={which}, parent={v}, slot={s}");
                lift_count += 1;
            }

            for alpha in [alpha_zero, alpha_wide] {
                let folded = linear_folded_coefficients(&q, alpha);
                let mut native = E::ZERO;
                for (d, coefficient) in folded.iter().enumerate() {
                    native = native.add(coefficient.mul(E::from_m31(basis::natural(d, t4x))));
                }
                let projected = verifier::line_fold(alpha, v, actual);
                assert_eq!(projected, native, "line fold mismatch at q={which}, parent={v}");
                fold_count += 1;
            }
        }
    }
    (source_eval_count, lift_count, fold_count)
}

fn domain_identities() -> (usize, usize, usize) {
    let mut geometry_count = 0usize;
    let mut basis_count = 0usize;
    let mut projection_count = 0usize;
    for v in 0..PARENTS {
        let p = 4 * v;
        let nodes = core::array::from_fn::<_, 4, _>(|s| {
            fast_domain::line_node(FibreIndex::new(p + s).expect("checked domain index"))
        });
        let [x, nx, ny, y] = nodes;
        assert_eq!(nx, x.neg(), "second child is not -x at parent {v}");
        assert_eq!(ny, y.neg(), "third child is not -y at parent {v}");
        assert_ne!(x.mul(y).mul(double(x)), M31::ZERO, "x*y*T2(x) is zero at {v}");
        let z = double(x);
        assert_eq!(double(y), z.neg(), "T2(y) != -T2(x) at parent {v}");
        let t4x = double(z);
        for node in nodes {
            assert_eq!(double(double(node)), t4x, "shared T4 node mismatch at parent {v}");
        }
        geometry_count += 1;

        for d in 0..64 {
            let target = basis::natural(d, t4x);
            for node in nodes {
                assert_eq!(basis::natural(4 * d, node), target, "4d lift mismatch at v={v}, d={d}");
                basis_count += 1;
            }
        }

        for j in 0..256 {
            let sum = nodes.iter().fold(M31::ZERO, |acc, node| {
                acc.add(basis::natural(j, *node))
            });
            let projected = sum.mul(QUARTER);
            let expected = if j & 3 == 0 { basis::natural(j, x) } else { M31::ZERO };
            assert_eq!(projected, expected, "four-child projection mismatch at v={v}, j={j}");
            projection_count += 1;
        }
    }
    (geometry_count, basis_count, projection_count)
}

fn main() {
    assert!(!cfg!(debug_assertions), "this gate must run optimized");
    let domain = domain_identities();
    let dense = dense_source_and_fold_checks();
    println!(
        "{{\"label\":\"UNPROVED SECOND-FOLD LIFT GATE\",\"geometry_parents\":{},\"basis_lift_checks\":{},\"projection_checks\":{},\"source_evaluations\":{},\"lift_checks\":{},\"fold_checks\":{},\"all_passed\":true}}",
        domain.0, domain.1, domain.2, dense.0, dense.1, dense.2
    );
}
