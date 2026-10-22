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
// Candidate entry delegates to the pinned fixed-call implementation.
// Candidate-only extracted single-slot helper.
fn four_dots_one<const SLOT: usize>(q: &[u8; 608], g: &[WideExact; 29]) -> WideExact {
    let slot = SLOT;
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
                sums[0] += u64::from(coefficient[0]) * u64::from(scalar.0);
                sums[1] += u64::from(coefficient[1]) * u64::from(scalar.0);
                sums[2] += u64::from(coefficient[2]) * u64::from(scalar.0);
                sums[3] += u64::from(coefficient[3]) * u64::from(scalar.0);
                sums[4] += u64::from(coefficient[4]) * u64::from(scalar.0);
                sums[5] += u64::from(coefficient[5]) * u64::from(scalar.0);
                sums[6] += u64::from(coefficient[6]) * u64::from(scalar.0);
                sums[7] += u64::from(coefficient[7]) * u64::from(scalar.0);
            }
            limbs[0] += (sums[0] & 0x7fff_ffff) + (sums[0] >> 31);
            limbs[1] += (sums[1] & 0x7fff_ffff) + (sums[1] >> 31);
            limbs[2] += (sums[2] & 0x7fff_ffff) + (sums[2] >> 31);
            limbs[3] += (sums[3] & 0x7fff_ffff) + (sums[3] >> 31);
            limbs[4] += (sums[4] & 0x7fff_ffff) + (sums[4] >> 31);
            limbs[5] += (sums[5] & 0x7fff_ffff) + (sums[5] >> 31);
            limbs[6] += (sums[6] & 0x7fff_ffff) + (sums[6] >> 31);
            limbs[7] += (sums[7] & 0x7fff_ffff) + (sums[7] >> 31);
        }

        let mut value = WideExact::from_limbs([
            M31::reduce_u64(limbs[0]).0,
            M31::reduce_u64(limbs[1]).0,
            M31::reduce_u64(limbs[2]).0,
            M31::reduce_u64(limbs[3]).0,
            M31::reduce_u64(limbs[4]).0,
            M31::reduce_u64(limbs[5]).0,
            M31::reduce_u64(limbs[6]).0,
            M31::reduce_u64(limbs[7]).0
        ]).unwrap();
        let mut tail=EbyKDot::new();
        tail.push(g[28],QM31::from_le_bytes(&q[slot*120+104..slot*120+120]).unwrap()).unwrap();
        let offset0 = 480 + slot * 32 + 0 * 16;
                tail.push(g[0 + 26], QM31::from_le_bytes(&q[offset0..offset0 + 16]).unwrap()).unwrap();
                let offset1 = 480 + slot * 32 + 1 * 16;
                tail.push(g[1 + 26], QM31::from_le_bytes(&q[offset1..offset1 + 16]).unwrap()).unwrap();
        value.add(tail.finish())
    
}

// Candidate-only explicit four-call version, preserving the callback order.
pub fn four_dots(q: &[u8], g: &[WideExact; 29]) -> [WideExact; 4] {
    let q: &[u8; 608] = q[..608].try_into().unwrap();
    [
        four_dots_one::<0>(q, g),
        four_dots_one::<1>(q, g),
        four_dots_one::<2>(q, g),
        four_dots_one::<3>(q, g),
    ]
}
