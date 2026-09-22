//! Staged-only semantic digest candidate.
//!
//! This file is injected into the semantic-terminal module by an experiment
//! harness. It deliberately does not alter the production implementation.
//! The event rows, branch conditions, expected digests, and Merkle tweak are
//! copied from `public_digest_packed_selector_tensor`.

use super::*;

#[inline(never)]
pub(super) fn public_digest_packed_selector_tensor_r20(
    public: SemanticPublic<'_>,
    openings: &StateOnlyPoseidonOpenings,
    selectors: &Selectors,
) -> [QM31; DIGEST_ELEMS / 4] {
    let mut hsum = [QM31::ZERO; 3];
    let mut expected_sum = [[QM31::ZERO; DIGEST_ELEMS / 4]; 3];

    // Record one source event into its destination local. The expected digest
    // is packed from canonical M31 limbs before applying the selector.
    let mut record = |group: usize, high: QM31, expected: &Digest, right_tweak: bool| {
        hsum[group] = hsum[group].add(high);
        for packed_group in 0..DIGEST_ELEMS / 4 {
            let start = 4 * packed_group;
            let limbs: [QM31; 4] = core::array::from_fn(|slot| {
                let lane = start + slot;
                let mut value = expected[lane];
                if right_tweak && lane + 1 == DIGEST_ELEMS {
                    value = value.add(MERKLE_NODE_COMPRESSION_V3_TWEAK);
                }
                lift_m31(value)
            });
            expected_sum[group][packed_group] =
                expected_sum[group][packed_group].add(high.mul(qm31_pack_base4(&limbs)));
        }
    };

    // Fixed digest events: local 11 / group 1.
    record(1, selectors.high[56], &public.anchor, false);
    record(1, selectors.high[26], &public.nullifier, false);
    if let Some(recipient) = public.recipient {
        record(1, selectors.high[29], &recipient, false);
    }
    record(1, selectors.high[32], &public.change, false);

    // Append levels: local 0 for empty-root branches, local 12 for frontier
    // branches. The empty-root branch retains the exact right-side tweak.
    let source = public.transition.live_snapshot;
    let after = public.transition.candidate_afterstate;
    let next_pair_index = source.next_pair_index;
    for level in 0..20 {
        let high = selectors.high[34 + level];
        if ((next_pair_index >> level) & 1) == 0 {
            record(0, high, &empty_root(level), true);
        } else {
            record(2, high, &source.frontier[level], false);
        }
    }

    record(1, selectors.high[53], &after.next_root, false);
    let carry = core::cmp::min(next_pair_index.trailing_ones() as usize, 20);
    if carry < 20 {
        record(
            1,
            selectors.high[33 + carry],
            &after.next_frontier[carry],
            false,
        );
    }

    let opened_group = |start: usize| -> [QM31; DIGEST_ELEMS / 4] {
        core::array::from_fn(|packed_group| {
            let limbs: [QM31; 4] =
                core::array::from_fn(|slot| openings.z[start + 4 * packed_group + slot]);
            qm31_pack_base4(&limbs)
        })
    };
    let opened0 = opened_group(RATE);
    let opened1 = opened_group(0);
    let opened2 = opened1;
    let opened = [opened0, opened1, opened2];

    let mut output = [QM31::ZERO; DIGEST_ELEMS / 4];
    let low0 = PreparedQm31Multiplier::new(selectors.low[0]);
    let low11 = PreparedQm31Multiplier::new(selectors.low[11]);
    let low12 = PreparedQm31Multiplier::new(selectors.low[12]);
    let lows = [low0, low11, low12];
    for group in 0..3 {
        for packed_group in 0..DIGEST_ELEMS / 4 {
            let residual = lows[group].mul(
                hsum[group]
                    .mul(opened[group][packed_group])
                    .sub(expected_sum[group][packed_group]),
            );
            output[packed_group] = output[packed_group].add(residual);
        }
    }
    output
}
