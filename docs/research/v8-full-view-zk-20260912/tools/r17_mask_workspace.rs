//! Allocation-free candidate for the R17 mask functional. Research only.
//! Callers provide both buffers; their acquisition/failure remains a separate
//! obligation. This does not change pads, coins, field values or chronology.
use super::corelib::field::{CM31, M31, M31_HALF, QM31 as K};
use super::r17_structured_g::{COINS, N, PER_ROUND, ROUNDS};

/// Fill the same 271 coin weights and 1024 output coordinates as the retained
/// mask_weights implementation. No Vec, allocator or iterator collection is
/// used here. Buffers must be disjoint (enforced by ordinary mutable borrows).
/// All entries are overwritten, so no previous workspace contents are reused.
pub(super) fn mask_weights_into(
    point: &[K; ROUNDS],
    coin_weights: &mut [K; COINS],
    weights: &mut [K; N],
) {
    let mut scale = K::ONE;
    let mut r = ROUNDS;
    while r != 0 {
        r -= 1;
        let start = 1 + r * PER_ROUND;
        let x = point[r];
        coin_weights[start] = scale.mul(K::ONE.sub(x.add(x)));
        let mut power = x.square();
        let mut i = 1;
        while i < PER_ROUND {
            coin_weights[start + i] = scale.mul(power.sub(x));
            power = power.mul(x);
            i += 1;
        }
        scale = scale.mul_m31(M31_HALF);
    }
    coin_weights[0] = scale;
    let mut j = 0;
    while j < N {
        weights[j] = K::ZERO;
        j += 1;
    }
    let mut i = 0;
    while i < COINS {
        let node = K::from_cm31(CM31::from_m31(M31((i + 1) as u32)));
        let a = coin_weights[i];
        let mut power = K::ONE;
        let mut j = 0;
        while j < N {
            weights[j] = weights[j].add(a.mul(power));
            power = power.mul(node);
            j += 1;
        }
        i += 1;
    }
}
