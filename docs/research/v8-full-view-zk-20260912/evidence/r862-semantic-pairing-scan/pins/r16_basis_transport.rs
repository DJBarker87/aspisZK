//! Research-profile basis transport shared by candidate prover and verifier.
//! No production caller and no privacy claim. The source mask inventory
//! determines the immutable map; no prover-supplied permutation is accepted.
use aspis_core::field::{M31, QM31};
#[cfg(not(target_os="solana"))]
#[path="r18_minimal_transport.rs"] mod minimal;
#[cfg(not(target_os="solana"))]
use aspis_statement::pool_v1::{
    pool_v1_pair_forest_copy_active_rows_v1, pool_v1_pair_forest_relation_free_mask_cells_v1,
};
#[cfg(not(target_os="solana"))]
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
    #[cfg(not(target_os="solana"))]
    pub(crate) order: Vec<usize>,
    #[cfg(target_os="solana")]
    pub(crate) order: [usize; N],
    #[cfg(not(target_os="solana"))]
    pub(crate) inactive: Vec<bool>,
    #[cfg(target_os="solana")]
    pub(crate) inactive: [bool; N],
}
impl Transport {
    #[cfg(not(target_os="solana"))]
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
        let base=|j:usize|(j&1)|(((j>>1)&63)<<4)|(((j>>7)^7)<<1);
        let mut order:Vec<_>=(0..N).map(base).collect();
        order.swap(127,1023);
        order.swap(126,1021);
        assert_eq!(order[PIVOT],PIVOT);
        for j in 0..PADS {
            let row=order[j];
            assert_eq!(row,16*(j/2)+14+(j%2));
            assert!(inactive[row] && legal(row) && row!=1014 && row!=PIVOT);
        }
        assert_eq!(order.as_slice(),fixed::ORDER.as_slice(),"host/source versus frozen SBF order");
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
#[cfg(target_os="solana")]
pub fn transport() -> &'static Transport {
    static T: Transport = Transport { order: fixed::ORDER, inactive: fixed::INACTIVE };
    &T
}
#[cfg(not(target_os="solana"))]
pub fn transport() -> &'static Transport {
    static T: OnceLock<Transport> = OnceLock::new();
    T.get_or_init(Transport::new)
}

mod fixed { include!("r17_basis_tables.rs"); }
