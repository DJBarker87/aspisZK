//! Exact four-slot dot products with a batched base-field prefix.
use aspis_core::field::{M31, QM31, WideExact};
use crate::fast_pairing::EbyKDot;

/// Compute the verifier's four dot products while postponing canonical M31
/// reductions across groups of at most four base-field products.
///
/// Each limb product is at most `(P - 1)^2`; four products therefore sum to
/// less than `2^64`, since `4 * (P - 1)^2 < 2^64`. We reduce every batch with
/// `M31::reduce_u64` before adding it to the canonical running limb.
pub fn four_dots(q: &[u8], g: &[WideExact; 29]) -> [WideExact; 4] {
    core::array::from_fn(|slot| {
        let mut limbs = [M31::ZERO; WideExact::LIMB_COUNT];
        for start in (0..26).step_by(4) {
            let mut sums = [0u64; WideExact::LIMB_COUNT];
            for term in start..core::cmp::min(start + 4, 26) {
                let scalar = M31::from_le_bytes(
                    q[slot * 120 + term * 4..slot * 120 + term * 4 + 4]
                        .try_into()
                        .unwrap(),
                )
                .unwrap();
                let coefficient = g[term].to_limbs();
                for limb in 0..WideExact::LIMB_COUNT {
                    sums[limb] += u64::from(coefficient[limb]) * u64::from(scalar.0);
                }
            }
            for limb in 0..WideExact::LIMB_COUNT {
                limbs[limb] = limbs[limb].add(M31::reduce_u64(sums[limb]));
            }
        }

        let mut value = WideExact::from_limbs(core::array::from_fn(|i| limbs[i].0)).unwrap();
        let mut tail=EbyKDot::new();
        tail.push(g[28],QM31::from_le_bytes(&q[slot*120+104..slot*120+120]).unwrap()).unwrap();
        for term in 0..2 {
            let offset = 480 + slot * 32 + term * 16;
            tail.push(g[term+26],QM31::from_le_bytes(&q[offset..offset+16]).unwrap()).unwrap();
        }
        value.add(tail.finish())
    })
}
