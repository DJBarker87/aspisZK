//! Pre-migration pair-forest compiler, retained verbatim as native
//! differential evidence (LOG D68.2): the legacy pair compiler and its writers,
//! the relocation (`relocate_and_extend`) with the forest path-aux and
//! forest-node writers, and the production bank merge.  Compiled only with the
//! audit feature `pool-v1-pair-forest-writer-reference`; the shipped compiler
//! is `super::compile_pool_v1_pair_forest_*_merged_c1_v1`.

use alloc::vec::Vec;

use aspis_core::field::M31;

use crate::poseidon2::{
    permute_optimized_with_trace, Digest, MERKLE_NODE_COMPRESSION_V3_TWEAK, POSEIDON2_ROUNDS,
};

use super::super::{
    pair_forest_hiding::{
        pool_v1_pair_forest_path_base_row_v1, POOL_V1_PAIR_FOREST_PRIVATE_DIRECTIONS_V1,
        POOL_V1_PAIR_FOREST_SUPER_ROOT_DEPTH_V1,
    },
    pair_trace::{
        build_pool_v1_pair_private_transfer_trace_v1, build_pool_v1_pair_withdrawal_trace_v1,
        PoolV1PairPrivateTransferWitnessV1, PoolV1PairTraceErrorV1,
        PoolV1PairTracePublicOutputsV1, PoolV1PairWithdrawalWitnessV1,
    },
    pair_tree_profile::{
        PoolV1PairLatePublicStatementV1, PoolV1PairLiveSnapshotV1, POOL_V1_PAIR_TRACE_COLUMNS,
        POOL_V1_PAIR_TRACE_ROWS,
    },
    payment_relation::{
        PoolV1PaymentRelationContextV1, PoolV1PrivateTransferPublicV1, PoolV1WithdrawalPublicV1,
    },
};
use super::{
    lane_root, temporary_context, PoolV1PairForestInputNoteWitnessV1,
    PoolV1PairForestMergedC1CompilationV1, PoolV1PairForestPrivateTransferWitnessV1,
    PoolV1PairForestTraceV1, PoolV1PairForestWithdrawalWitnessV1,
};
use crate::state_only_trace::StateOnlyTraceFoundation;

#[inline]
fn trace_digest(columns: &[Vec<M31>; 16], block: usize) -> Digest {
    core::array::from_fn(|lane| columns[lane][block * 16 + 11])
}

#[inline]
fn node_left(columns: &[Vec<M31>; 16], block: usize) -> Digest {
    core::array::from_fn(|lane| columns[lane][block * 16 + 12])
}

#[inline]
fn node_right(columns: &[Vec<M31>; 16], block: usize) -> Digest {
    core::array::from_fn(|lane| {
        let value = columns[8 + lane][block * 16];
        if lane == 7 {
            value.sub(MERKLE_NODE_COMPRESSION_V3_TWEAK)
        } else {
            value
        }
    })
}

fn write_forest_path_aux(
    columns: &mut [Vec<M31>; 16],
    level: usize,
    bit: M31,
    current: Digest,
    left: Digest,
    right: Digest,
) -> Result<(), PoolV1PairTraceErrorV1> {
    let base =
        pool_v1_pair_forest_path_base_row_v1(level).ok_or(PoolV1PairTraceErrorV1::HashSchedule)?;
    columns[0][base] = bit;
    for lane in 0..8 {
        columns[1 + lane][base] = current[lane];
        columns[lane][base + 1] = left[lane];
        columns[8 + lane][base + 1] = right[lane];
    }
    Ok(())
}

fn write_forest_node(
    columns: &mut [Vec<M31>; 16],
    block: usize,
    left: Digest,
    right: Digest,
) -> Result<Digest, PoolV1PairTraceErrorV1> {
    if !(54..=56).contains(&block) {
        return Err(PoolV1PairTraceErrorV1::HashSchedule);
    }
    let base = block * 16;
    let mut state = [M31::ZERO; 16];
    state[8..].copy_from_slice(&right);
    state[15] = state[15].add(MERKLE_NODE_COMPRESSION_V3_TWEAK);
    for lane in 0..8 {
        columns[lane][base + 12] = left[lane];
        state[lane] = state[lane].add(left[lane]);
    }
    for lane in 0..16 {
        columns[lane][base] = if lane < 8 { M31::ZERO } else { state[lane] };
    }
    let mut rounds = 0;
    permute_optimized_with_trace(&mut state, |transition| {
        rounds += 1;
        if transition.round & 1 == 1 {
            let row = base + usize::from(transition.round) / 2 + 1;
            for lane in 0..16 {
                columns[lane][row] = transition.output[lane];
            }
        }
    });
    if rounds != POSEIDON2_ROUNDS {
        return Err(PoolV1PairTraceErrorV1::HashSchedule);
    }
    Ok(core::array::from_fn(|lane| state[lane]))
}

fn relocate_and_extend(
    mut legacy: super::pair_trace::PoolV1PairTraceV1,
    input: &PoolV1PairForestInputNoteWitnessV1,
    expected_global_anchor: Digest,
) -> Result<PoolV1PairForestTraceV1, PoolV1PairTraceErrorV1> {
    if input
        .super_root_siblings
        .iter()
        .flatten()
        .any(|limb| limb.0 >= aspis_core::field::P)
    {
        return Err(PoolV1PairTraceErrorV1::WitnessDigest);
    }
    let old = legacy.stable.c1.clone();
    for column in &mut legacy.stable.c1 {
        column[864..].fill(M31::ZERO);
    }
    let mut directions = [M31::ZERO; POOL_V1_PAIR_FOREST_PRIVATE_DIRECTIONS_V1];
    directions[..21].copy_from_slice(&legacy.private_directions);
    for level in 0..21 {
        let target = 4 + level;
        let previous = if level == 0 { 3 } else { target - 1 };
        let current = trace_digest(&old, previous);
        let left = node_left(&old, target);
        let right = node_right(&old, target);
        let bit = directions[level];
        write_forest_path_aux(&mut legacy.stable.c1, level, bit, current, left, right)?;
    }
    for column in 0..16 {
        legacy.stable.c1[column][1008..1024].copy_from_slice(&old[column][960..976]);
    }
    let mut current = trace_digest(&legacy.stable.c1, 24);
    for level in 0..POOL_V1_PAIR_FOREST_SUPER_ROOT_DEPTH_V1 {
        let bit = M31(u32::from(input.super_root_directions[level]));
        directions[21 + level] = bit;
        let sibling = input.super_root_siblings[level];
        let (left, right) = if bit == M31::ZERO {
            (current, sibling)
        } else {
            (sibling, current)
        };
        write_forest_path_aux(&mut legacy.stable.c1, 21 + level, bit, current, left, right)?;
        current = write_forest_node(&mut legacy.stable.c1, 54 + level, left, right)?;
    }
    if current != expected_global_anchor {
        return Err(PoolV1PairTraceErrorV1::AnchorMismatch);
    }
    let public_outputs = match legacy.public_outputs {
        PoolV1PairTracePublicOutputsV1::PrivateTransfer {
            nullifier,
            recipient_commitment,
            change_commitment,
            output_pair,
            ..
        } => PoolV1PairTracePublicOutputsV1::PrivateTransfer {
            anchor: current,
            nullifier,
            recipient_commitment,
            change_commitment,
            output_pair,
        },
        PoolV1PairTracePublicOutputsV1::Withdrawal {
            nullifier,
            change_commitment,
            output_pair,
            ..
        } => PoolV1PairTracePublicOutputsV1::Withdrawal {
            anchor: current,
            nullifier,
            change_commitment,
            output_pair,
        },
    };
    Ok(PoolV1PairForestTraceV1 {
        stable: legacy.stable,
        late: legacy.late,
        variant: legacy.variant,
        private_directions: directions,
        value_bits: legacy.value_bits,
        public_outputs,
        afterstate: legacy.afterstate,
    })
}

pub fn merge_pool_v1_pair_forest_trace_banks_v1(
    trace: &PoolV1PairForestTraceV1,
) -> Result<StateOnlyTraceFoundation, PoolV1PairTraceErrorV1> {
    if trace.stable.c1.len() != POOL_V1_PAIR_TRACE_COLUMNS
        || trace
            .stable
            .c1
            .iter()
            .any(|column| column.len() != POOL_V1_PAIR_TRACE_ROWS)
        || trace
            .late
            .iter()
            .any(|column| column.len() != POOL_V1_PAIR_TRACE_ROWS)
    {
        return Err(PoolV1PairTraceErrorV1::Shape);
    }
    for column in 0..POOL_V1_PAIR_TRACE_COLUMNS {
        if trace.stable.c1[column][544..864]
            .iter()
            .any(|value| *value != M31::ZERO)
            || trace.late[column][..544]
                .iter()
                .chain(&trace.late[column][864..])
                .any(|value| *value != M31::ZERO)
        {
            return Err(PoolV1PairTraceErrorV1::Shape);
        }
    }
    let mut merged = trace.stable.clone();
    for column in 0..POOL_V1_PAIR_TRACE_COLUMNS {
        merged.c1[column][544..864].copy_from_slice(&trace.late[column][544..864]);
    }
    Ok(merged)
}

pub fn compile_pool_v1_pair_forest_private_transfer_merged_c1_v1(
    public: &PoolV1PrivateTransferPublicV1,
    witness: &PoolV1PairForestPrivateTransferWitnessV1,
    context: PoolV1PaymentRelationContextV1<'_>,
    snapshot: PoolV1PairLiveSnapshotV1,
) -> Result<PoolV1PairForestMergedC1CompilationV1, PoolV1PairTraceErrorV1> {
    let lane_anchor = lane_root(&witness.input.pair)?;
    let temporary_public = PoolV1PrivateTransferPublicV1 {
        anchor_root: lane_anchor,
        ..*public
    };
    let legacy = build_pool_v1_pair_private_transfer_trace_v1(
        &temporary_public,
        &PoolV1PairPrivateTransferWitnessV1 {
            input: witness.input.pair,
            recipient: witness.recipient,
            change: witness.change,
        },
        temporary_context(context, lane_anchor),
        snapshot,
    )?;
    let trace = relocate_and_extend(legacy, &witness.input, public.anchor_root)?;
    let semantic_c1 = merge_pool_v1_pair_forest_trace_banks_v1(&trace)?;
    Ok(PoolV1PairForestMergedC1CompilationV1 {
        public_statement: PoolV1PairLatePublicStatementV1 {
            live_snapshot: snapshot,
            candidate_afterstate: trace.afterstate,
        },
        trace,
        semantic_c1,
    })
}

pub fn compile_pool_v1_pair_forest_withdrawal_merged_c1_v1(
    public: &PoolV1WithdrawalPublicV1,
    witness: &PoolV1PairForestWithdrawalWitnessV1,
    context: PoolV1PaymentRelationContextV1<'_>,
    snapshot: PoolV1PairLiveSnapshotV1,
) -> Result<PoolV1PairForestMergedC1CompilationV1, PoolV1PairTraceErrorV1> {
    let lane_anchor = lane_root(&witness.input.pair)?;
    let temporary_public = PoolV1WithdrawalPublicV1 {
        anchor_root: lane_anchor,
        ..*public
    };
    let legacy = build_pool_v1_pair_withdrawal_trace_v1(
        &temporary_public,
        &PoolV1PairWithdrawalWitnessV1 {
            input: witness.input.pair,
            change: witness.change,
        },
        temporary_context(context, lane_anchor),
        snapshot,
    )?;
    let trace = relocate_and_extend(legacy, &witness.input, public.anchor_root)?;
    let semantic_c1 = merge_pool_v1_pair_forest_trace_banks_v1(&trace)?;
    Ok(PoolV1PairForestMergedC1CompilationV1 {
        public_statement: PoolV1PairLatePublicStatementV1 {
            live_snapshot: snapshot,
            candidate_afterstate: trace.afterstate,
        },
        trace,
        semantic_c1,
    })
}
