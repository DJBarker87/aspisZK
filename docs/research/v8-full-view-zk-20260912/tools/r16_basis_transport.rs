//! Research-profile basis transport shared by candidate prover and verifier.
//! No production caller and no privacy claim. The source mask inventory
//! determines the immutable map; no prover-supplied permutation is accepted.
use aspis_core::field::{M31, QM31};
use aspis_statement::pool_v1::{
    pool_v1_pair_forest_copy_active_rows_v1, pool_v1_pair_forest_relation_free_mask_cells_v1,
};
use std::sync::OnceLock;

pub const N: usize = 1024;
pub const PIVOT: usize = 1023;
pub const PADS: usize = 89;

pub trait Scalar: Copy {
    const ZERO: Self;
    fn plus(self, rhs: Self) -> Self;
    fn minus(self, rhs: Self) -> Self;
}
impl Scalar for M31 {
    const ZERO: Self = M31::ZERO;
    fn plus(self, rhs: Self) -> Self {
        self.add(rhs)
    }
    fn minus(self, rhs: Self) -> Self {
        self.sub(rhs)
    }
}
impl Scalar for QM31 {
    const ZERO: Self = QM31::ZERO;
    fn plus(self, rhs: Self) -> Self {
        self.add(rhs)
    }
    fn minus(self, rhs: Self) -> Self {
        self.sub(rhs)
    }
}

pub struct Transport {
    pub(crate) order: Vec<usize>,
    pub(crate) inactive: Vec<bool>,
}
impl Transport {
    pub fn new() -> Self {
        let active = pool_v1_pair_forest_copy_active_rows_v1().unwrap();
        let inactive: Vec<_> = (0..N).map(|r| !active.contains(&(r as u16))).collect();
        let cells = pool_v1_pair_forest_relation_free_mask_cells_v1().unwrap();
        let legal = |r: usize| {
            (0..16).all(|c| {
                cells
                    .iter()
                    .any(|cell| usize::from(cell.column) == c && usize::from(cell.row) == r)
            })
        };
        assert!(inactive[PIVOT] && legal(PIVOT));
        let pads: Vec<_> = (0..PIVOT)
            .filter(|&r| inactive[r] && r != 1014 && legal(r))
            .take(PADS)
            .collect();
        assert_eq!(pads.len(), PADS);
        let mut order = pads.clone();
        order.extend((0..PIVOT).filter(|r| !pads.contains(r)));
        order.push(PIVOT);
        Self { order, inactive }
    }
    pub fn forward<F: Scalar>(&self, m: &[F]) -> Vec<F> {
        assert_eq!(m.len(), N);
        let mut out: Vec<_> = self.order.iter().map(|&r| m[r]).collect();
        out[PIVOT] = (0..N)
            .filter(|&r| self.inactive[r])
            .fold(F::ZERO, |a, r| a.plus(m[r]));
        out
    }
    pub fn inverse<F: Scalar>(&self, t: &[F]) -> Vec<F> {
        assert_eq!(t.len(), N);
        let mut m = vec![F::ZERO; N];
        for (j, &r) in self.order.iter().enumerate() {
            m[r] = t[j];
        }
        let other = (0..PIVOT)
            .filter(|&r| self.inactive[r])
            .fold(F::ZERO, |a, r| a.plus(m[r]));
        m[PIVOT] = t[PIVOT].minus(other);
        m
    }
    pub fn dual<F: Scalar>(&self, w: &[F]) -> Vec<F> {
        assert_eq!(w.len(), N);
        self.order
            .iter()
            .map(|&r| {
                if r != PIVOT && self.inactive[r] {
                    w[r].minus(w[PIVOT])
                } else {
                    w[r]
                }
            })
            .collect()
    }
}
pub fn transport() -> &'static Transport {
    static T: OnceLock<Transport> = OnceLock::new();
    T.get_or_init(Transport::new)
}
