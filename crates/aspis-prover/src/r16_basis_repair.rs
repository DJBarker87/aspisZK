//! Candidate only: reversible public basis transport, not a privacy theorem.
use crate::{
    circle_candidate::CircleEncoder,
    v8_privacy_affine_gate::{certify_fixed_affine, AffineCertificate},
};
use aspis_core::field::M31;
use aspis_statement::pool_v1::{
    pool_v1_pair_forest_copy_active_rows_v1, pool_v1_pair_forest_relation_free_mask_cells_v1,
};

const N: usize = 1024;
const PIVOT: usize = 1023;
const PADS: usize = 89;

#[test]
fn r16_source_low_factors_match_four_slot_polynomial_channels() {
    use aspis_core::circle_fri::selected_circle_fiber_points_shared;
    let encoder = CircleEncoder::new_for_domain_log(20);
    let mut roots = Vec::with_capacity(1 << 18);
    for start in (0u32..1 << 18).step_by(512) {
        let ids: Vec<_> = (start..start + 512).collect();
        let points = selected_circle_fiber_points_shared(20, &ids).unwrap();
        for (&id, p) in ids.iter().zip(points) {
            let root = p.x.mul(p.x).double().sub(M31::ONE);
            roots.push(root.0);
            for (slot, (x, y)) in [
                (p.x, p.y),
                (p.x, p.y.neg()),
                (p.x.neg(), p.y.neg()),
                (p.x.neg(), p.y),
            ]
            .into_iter()
            .enumerate()
            {
                let index = 4 * id as usize + slot;
                assert_eq!(encoder.encode_c1_basis_value(1, index).unwrap(), y);
                assert_eq!(encoder.encode_c1_basis_value(2, index).unwrap(), x);
                let mut factor = root;
                for bit in 2..7 {
                    assert_eq!(
                        encoder.encode_c1_basis_value(1 << bit, index).unwrap(),
                        factor
                    );
                    factor = factor.mul(factor).double().sub(M31::ONE);
                }
            }
        }
    }
    roots.sort_unstable();
    roots.dedup();
    assert_eq!(
        roots.len(),
        1 << 18,
        "all source fibre line roots must be distinct"
    );
}

struct Transport {
    order: Vec<usize>,
    inactive: Vec<bool>,
}
impl Transport {
    fn new() -> Self {
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
    fn forward(&self, m: &[M31]) -> Vec<M31> {
        assert_eq!(m.len(), N);
        let mut out: Vec<_> = self.order.iter().map(|&r| m[r]).collect();
        out[PIVOT] = (0..N)
            .filter(|&r| self.inactive[r])
            .fold(M31::ZERO, |a, r| a.add(m[r]));
        out
    }
    fn inverse(&self, t: &[M31]) -> Vec<M31> {
        assert_eq!(t.len(), N);
        let mut m = vec![M31::ZERO; N];
        for (j, &r) in self.order.iter().enumerate() {
            m[r] = t[j];
        }
        let other = (0..PIVOT)
            .filter(|&r| self.inactive[r])
            .fold(M31::ZERO, |a, r| a.add(m[r]));
        m[PIVOT] = t[PIVOT].sub(other);
        m
    }
    fn dual(&self, w: &[M31]) -> Vec<M31> {
        self.order
            .iter()
            .map(|&r| {
                if r != PIVOT && self.inactive[r] {
                    w[r].sub(w[PIVOT])
                } else {
                    w[r]
                }
            })
            .collect()
    }
}
fn dot(a: &[M31], b: &[M31]) -> M31 {
    a.iter()
        .zip(b)
        .fold(M31::ZERO, |s, (a, b)| s.add(a.mul(*b)))
}

#[test]
fn r16_transport_preserves_all_basis_vectors_and_dual_claims() {
    let t = Transport::new();
    let w: Vec<_> = (0..N).map(|i| M31((i * i + 17 * i + 3) as u32)).collect();
    let dual = t.dual(&w);
    for r in 0..N {
        let mut m = vec![M31::ZERO; N];
        m[r] = M31::ONE;
        let encoded = t.forward(&m);
        assert_eq!(t.inverse(&encoded), m);
        assert_eq!(dot(&w, &m), dot(&dual, &encoded));
    }
    for j in 0..PADS {
        let mut mask = vec![M31::ZERO; N];
        mask[t.order[j]] = M31::ONE;
        mask[PIVOT] = M31::ONE.neg();
        let mut expected = vec![M31::ZERO; N];
        expected[j] = M31::ONE;
        assert_eq!(t.forward(&mask), expected);
    }
}

#[test]
fn r16_known_bad_schedule_has_full_raw_mask_rank_after_transport() {
    let encoder = CircleEncoder::new_for_domain_log(20);
    let mut queries = vec![4usize, 6];
    queries.extend((0..20).map(|i| 1000 + 7919 * i));
    let mask: Vec<Vec<M31>> = queries
        .iter()
        .flat_map(|q| (0..4).map(move |s| 4 * q + s))
        .map(|index| {
            (0..PADS)
                .map(|j| encoder.encode_c1_basis_value(j, index).unwrap())
                .collect()
        })
        .collect();
    // Identity targets certify all 88 raw observation directions, not only
    // the selected-second fixture difference. This is still ONE schedule.
    let target: Vec<Vec<M31>> = (0..88)
        .map(|i| {
            (0..88)
                .map(|j| if i == j { M31::ONE } else { M31::ZERO })
                .collect()
        })
        .collect();
    match certify_fixed_affine(&mask, &target).unwrap() {
        AffineCertificate::Correction { rank, .. } => assert_eq!(rank, 88),
        other => panic!("candidate does not repair the retained schedule: {other:?}"),
    }
}
