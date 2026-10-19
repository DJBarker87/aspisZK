//! Exact four-slot dot products with a partially reduced base-field prefix.
use aspis_core::field::{M31, QM31, WideExact,PreparedQm31Multiplier,qm31_sum_products3_prepared};

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
    // Each of these challenge operands is reused across all four slots.
    let tail=[g[28],g[26],g[27]];
    let left0=tail.map(|x|PreparedQm31Multiplier::new(x.c0()));
    let left1=tail.map(|x|PreparedQm31Multiplier::new(x.c1()));
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

        let value = WideExact::from_limbs(core::array::from_fn(|i| M31::reduce_u64(limbs[i]).0)).unwrap();
        let scalar=[QM31::from_le_bytes(&q[slot*120+104..slot*120+120]).unwrap(),
            QM31::from_le_bytes(&q[480+slot*32..496+slot*32]).unwrap(),
            QM31::from_le_bytes(&q[496+slot*32..512+slot*32]).unwrap()];
        let a=qm31_sum_products3_prepared(&left0,&scalar);
        let b=qm31_sum_products3_prepared(&left1,&scalar);
        let tail=WideExact::from_limbs([a.c0.a.0,a.c0.b.0,a.c1.a.0,a.c1.b.0,
            b.c0.a.0,b.c0.b.0,b.c1.a.0,b.c1.b.0]).unwrap();
        value.add(tail)
    })
}
