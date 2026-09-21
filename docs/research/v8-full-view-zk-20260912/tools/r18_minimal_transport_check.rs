//! Mechanical host controls for the optional R18 minimal-support transport.
//! The frozen original table and the source-derived current transport are
//! supplied by the stage; this checker does not choose or derive a map.
extern crate aspis_core as corelib;
extern crate aspis_statement;

#[path="r18_minimal_transport.rs"] mod minimal_transport;
#[path="r16_basis_transport.rs"] mod current_transport;
mod original { include!("r18_original_basis_tables.rs"); }

use corelib::field::{CM31, M31, QM31, P};
use aspis_statement::pool_v1::{
    pool_v1_pair_forest_relation_free_mask_cells_v1,
};

const N: usize = minimal_transport::N;
const PADS: usize = minimal_transport::PADS;
const PIVOT: usize = 1023;

trait Scalar: Copy + PartialEq {
    const ZERO: Self;
    fn add(self, rhs: Self) -> Self;
    fn sub(self, rhs: Self) -> Self;
}
impl Scalar for M31 {
    const ZERO: Self = M31::ZERO;
    fn add(self, rhs: Self) -> Self { self.add(rhs) }
    fn sub(self, rhs: Self) -> Self { self.sub(rhs) }
}
impl Scalar for QM31 {
    const ZERO: Self = QM31::ZERO;
    fn add(self, rhs: Self) -> Self { self.add(rhs) }
    fn sub(self, rhs: Self) -> Self { self.sub(rhs) }
}

fn forward<F: Scalar>(order: &[usize; N], inactive: &[bool; N], m: &[F; N]) -> [F; N] {
    let mut out = core::array::from_fn(|j| m[order[j]]);
    out[PIVOT] = (0..N).filter(|&r| inactive[r]).fold(F::ZERO, |a, r| a.add(m[r]));
    out
}
fn inverse<F: Scalar>(order: &[usize; N], inactive: &[bool; N], t: &[F; N]) -> [F; N] {
    let mut m = [F::ZERO; N];
    for (j, &r) in order.iter().enumerate() { m[r] = t[j]; }
    let other = (0..PIVOT).filter(|&r| inactive[r]).fold(F::ZERO, |a, r| a.add(m[r]));
    m[PIVOT] = t[PIVOT].sub(other);
    m
}
fn dual<F: Scalar>(order: &[usize; N], inactive: &[bool; N], w: &[F; N]) -> [F; N] {
    core::array::from_fn(|j| {
        let r = order[j];
        if r != PIVOT && inactive[r] { w[r].sub(w[PIVOT]) } else { w[r] }
    })
}
fn sample_qm(seed: usize) -> QM31 {
    QM31 { c0:CM31::new(sample_m31(seed),sample_m31(3*seed+7)),
        c1:CM31::new(sample_m31(5*seed+11),sample_m31(7*seed+13)) }
}
fn sample_m31(seed: usize) -> M31 { M31((seed as u64 % u64::from(P)) as u32) }

fn main() {
    let current = current_transport::transport();
    let mut current_order = [0usize; N];
    current_order.copy_from_slice(&current.order);
    let mut inactive = [false; N];
    inactive.copy_from_slice(&current.inactive);
    assert!(inactive[PIVOT]);
    assert_eq!(current_order[PIVOT], PIVOT);

    let original: [usize; PADS] = original::ORDER[..PADS].try_into().unwrap();
    assert_eq!(inactive,original::INACTIVE);
    assert_eq!(&current_order[..PADS], &original);
    let mut pads = [0usize; PADS];
    pads.copy_from_slice(&current_order[..PADS]);
    let order = minimal_transport::minimal_order(&pads).expect("minimal constructor");
    assert_eq!(current_order,order,"selected actual source constructor");

    let mut changed = [0usize; N];
    let changed_count = minimal_transport::changed_indices(&order, &mut changed);
    assert_eq!(changed_count, 163);
    let mut seen = [false; N];
    for &r in &order { assert!(r < N); assert!(!seen[r]); seen[r] = true; }
    assert!(seen.iter().all(|x| *x));
    assert_eq!(&order[..PADS], &original);
    assert_eq!(order[PIVOT], PIVOT);

    let cells = pool_v1_pair_forest_relation_free_mask_cells_v1().unwrap();
    let legal = |r: usize| (0..16).all(|c| cells.iter().any(|x|
        usize::from(x.column) == c && usize::from(x.row) == r));
    assert!((0..PADS).all(|j| inactive[order[j]] && legal(order[j])));
    assert!((0..PADS).all(|j| order[j] != PIVOT));
    for pad in 0..PADS {
        let mut unit = [QM31::ZERO; N];
        unit[order[pad]] = QM31::ONE;
        unit[PIVOT] = QM31::ONE.neg();
        let image = current.forward(&unit);
        let mut expected=vec![QM31::ZERO;N];expected[pad]=QM31::ONE;
        assert_eq!(image,expected,"balanced pad coefficient {pad}");
        assert_eq!(current.inverse(&image),unit);
    }

    for case in 0..16 {
        let qm: [QM31;N] = core::array::from_fn(|j| sample_qm(case * N + j));
        let qm_f = current.forward(&qm);
        assert_eq!(current.inverse(&qm_f), qm);
        assert_eq!(current.forward(&current.inverse(&qm)),qm);
        let m: [M31;N] = core::array::from_fn(|j| sample_m31(case * N + j));
        let m_f = current.forward(&m);
        assert_eq!(current.inverse(&m_f), m);
        assert_eq!(current.forward(&current.inverse(&m)),m);
        let weights: [QM31;N] = core::array::from_fn(|j| sample_qm(17 * N + case * N + j));
        let d = current.dual(&weights);
        let lhs = (0..N).fold(QM31::ZERO, |s, j| s.add(d[j].mul(qm_f[j])));
        let rhs = (0..N).fold(QM31::ZERO, |s, j| s.add(weights[j].mul(qm[j])));
        assert_eq!(lhs, rhs);
    }
    println!("PASS: frozen original first89; minimal order permutation; changed=163; current inactive/pivot; 16-column legality for all89 pads; 89 balanced unit images; M31/QM31 forward-inverse and arbitrary-weight dual controls");
    println!("BOUNDARY: optional host transport control only; no map selection, source/security claim, or verifier integration");
}
