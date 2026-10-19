//! Exact four-slot dot products with a partially reduced base-field prefix.
use aspis_core::field::{M31, QM31, WideExact};
use crate::fast_pairing::EbyKDot;

/// Compute the verifier's four dot products while postponing canonical M31
/// reductions across groups of at most four base-field products.
///
/// Each limb product is at most `(P - 1)^2`; four products therefore sum to
/// less than `2^64`, since `4 * (P - 1)^2 < 2^64`. One Mersenne fold
/// `(sum & P) + (sum >> 31)` preserves its residue and is below `2^34`.
/// Seven folded batches sum to less than `2^37`; canonicalize each limb once
/// after all 26 products. Every byte decoder and its order are unchanged.
pub fn four_dots(q: &[u8], g: &[WideExact; 29]) -> [WideExact; 4] {
    // The dot payload is exactly this prefix; paths and salts are consumed
    // separately. Expose its fixed extent to remove repeated slice bounds.
    let q:&[u8;608]=q[..608].try_into().unwrap();
    core::array::from_fn(|slot| {
        let mut limbs = [0u64; WideExact::LIMB_COUNT];
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
                limbs[limb] += (sums[limb] & 0x7fff_ffff) + (sums[limb] >> 31);
            }
        }

        let mut value = WideExact::from_limbs(core::array::from_fn(|i| M31::reduce_u64(limbs[i]).0)).unwrap();
        let mut tail=EbyKDot::new();
        tail.push(g[28],QM31::from_le_bytes(&q[slot*120+104..slot*120+120]).unwrap()).unwrap();
        for term in 0..2 {
            let offset = 480 + slot * 32 + term * 16;
            tail.push(g[term+26],QM31::from_le_bytes(&q[offset..offset+16]).unwrap()).unwrap();
        }
        value.add(tail.finish())
    })
}
