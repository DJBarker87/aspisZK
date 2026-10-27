//! Production-inactive eight-lane forest trace compiler.
//!
//! This preserves the legacy pair compiler and relocates only its auxiliary
//! tail. Three private witness directions and siblings extend the historical
//! input path to the global forest root. The live append remains the existing
//! depth-20 selected output-lane transition in blocks `34..=53`.

use alloc::{vec, vec::Vec};

use aspis_core::field::{M31, QM31};

use crate::{
    logup::{
        build_copy_logup_helper, compress_tagged_tuple, verify_copy_logup_constraints, CopyLogUpRow,
    },
    poseidon2::{evaluate_trace_round_pair, Digest, MERKLE_NODE_COMPRESSION_V3_TWEAK, RATE},
    state_only_trace::StateOnlyTraceFoundation,
    trace_v4::TraceCell,
};

use super::{
    incremental_merkle::IncrementalMerkleTreeV1,
    pair_forest_copy_builder::{merge_banks, CopyBanks, CopyRecords},
    pair_forest_hiding::{
        build_pool_v1_pair_forest_copy_row_schedule_v1, POOL_V1_PAIR_FOREST_COPY_ROW_LINKS_V1,
        POOL_V1_PAIR_FOREST_INPUT_OCCUPANCY_AUX_ROW_V1,
        POOL_V1_PAIR_FOREST_OUTPUT_OCCUPANCY_AUX_ROW_V1, POOL_V1_PAIR_FOREST_PRIVATE_DIRECTIONS_V1,
        POOL_V1_PAIR_FOREST_SUPER_ROOT_DEPTH_V1, POOL_V1_PAIR_FOREST_VALUE_AUX_ROW_START_V1,
    },
    pair_terminal::PoolV1PairVerifiedAfterstateV1,
    pair_trace::{
        build_pool_v1_pair_copy_registry_v1, pair_empty_roots, validate_common, value_bits,
        PoolV1PairCopyLinkV1, PoolV1PairCopyTupleV1, PoolV1PairCopyWeightV1,
        PoolV1PairInputNoteWitnessV1, PoolV1PairTraceBankV1,
        PoolV1PairTraceCellV1, PoolV1PairTraceErrorV1, PoolV1PairTracePublicOutputsV1,
        PoolV1PairTraceVariantV1, PoolV1PairTupleLimbV1, POOL_V1_PAIR_COPY_TAG_BASE_V1,
        POOL_V1_PAIR_VALUE_BITS, POOL_V1_PAIR_VALUE_COUNT,
    },
    pair_tree_hiding::PoolV1PairCopyRowLinkKindV1,
    pair_tree_profile::{
        PoolV1PairLatePublicStatementV1, PoolV1PairLeafWitnessV1, PoolV1PairLiveSnapshotV1,
        POOL_V1_PAIR_TRACE_COLUMNS, POOL_V1_PAIR_TRACE_ROWS,
    },
    payment_relation::{
        validate_pool_v1_private_transfer_public_v1, validate_pool_v1_withdrawal_public_v1,
        PoolV1OutputNoteWitnessV1, PoolV1PaymentRelationContextV1, PoolV1PaymentRuntimeBindingV1,
        PoolV1PrivateTransferPublicV1, PoolV1WithdrawalPublicV1,
    },
    pool_v1_nullifier, pool_v1_tree_parent,
};
use crate::VALUE_LIMIT;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PairForestInputNoteWitnessV1 {
    pub pair: PoolV1PairInputNoteWitnessV1,
    pub super_root_siblings: [Digest; POOL_V1_PAIR_FOREST_SUPER_ROOT_DEPTH_V1],
    /// Private input-lane path bits. They are intentionally independent of the
    /// operationally selected output lane.
    pub super_root_directions: [bool; POOL_V1_PAIR_FOREST_SUPER_ROOT_DEPTH_V1],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PairForestPrivateTransferWitnessV1 {
    pub input: PoolV1PairForestInputNoteWitnessV1,
    pub recipient: PoolV1OutputNoteWitnessV1,
    pub change: PoolV1OutputNoteWitnessV1,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PairForestWithdrawalWitnessV1 {
    pub input: PoolV1PairForestInputNoteWitnessV1,
    pub change: PoolV1OutputNoteWitnessV1,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PoolV1PairForestTraceV1 {
    pub stable: StateOnlyTraceFoundation,
    pub late: [Vec<M31>; POOL_V1_PAIR_TRACE_COLUMNS],
    pub variant: PoolV1PairTraceVariantV1,
    pub private_directions: [M31; POOL_V1_PAIR_FOREST_PRIVATE_DIRECTIONS_V1],
    pub value_bits: [[M31; POOL_V1_PAIR_VALUE_BITS]; POOL_V1_PAIR_VALUE_COUNT],
    pub public_outputs: PoolV1PairTracePublicOutputsV1,
    pub afterstate: super::pair_terminal::PoolV1PairVerifiedAfterstateV1,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PoolV1PairForestMergedC1CompilationV1 {
    pub trace: PoolV1PairForestTraceV1,
    pub semantic_c1: StateOnlyTraceFoundation,
    pub public_statement: PoolV1PairLatePublicStatementV1,
}

fn lane_root(input: &PoolV1PairInputNoteWitnessV1) -> Result<Digest, PoolV1PairTraceErrorV1> {
    let mut current = input
        .pair_leaf
        .leaf_digest()
        .map_err(PoolV1PairTraceErrorV1::PairLeaf)?;
    for level in 0..20 {
        let sibling = input.membership.siblings[level];
        current = if ((input.membership.index >> level) & 1) == 0 {
            pool_v1_tree_parent(&current, &sibling)
        } else {
            pool_v1_tree_parent(&sibling, &current)
        };
    }
    Ok(current)
}

fn temporary_context<'a>(
    context: PoolV1PaymentRelationContextV1<'a>,
    anchor_root: Digest,
) -> PoolV1PaymentRelationContextV1<'a> {
    PoolV1PaymentRelationContextV1 {
        runtime_binding: PoolV1PaymentRuntimeBindingV1 {
            anchor_root,
            ..context.runtime_binding
        },
        spent_nullifiers: context.spent_nullifiers,
    }
}

/// The pre-migration compiler (legacy writers and relocation), retained only
/// as native differential evidence for the migration (LOG D68.2).
#[cfg(feature = "pool-v1-pair-forest-writer-reference")]
#[path = "pair_forest_trace_reference.rs"]
pub mod reference;
// The retained reference text names `super::pair_trace` (its original path).
#[cfg(feature = "pool-v1-pair-forest-writer-reference")]
use super::pair_trace;

/// Merge the stable and late banks (rows 544..864 from the late bank). The
/// shape check and the copy are the extracted `merge_check` / `merge_copy`
/// (LOG D68.2); a failed shape check is `Shape`, as before.
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
    let c1 = merge_banks(&trace.stable.c1, &trace.late).ok_or(PoolV1PairTraceErrorV1::Shape)?;
    Ok(StateOnlyTraceFoundation { c1 })
}

/// Replay every one of the 57 forest permutation blocks from its committed
/// row-0/row-12 inputs with the production round equations, independently of
/// the extracted writers that filled them (the forest counterpart of the
/// legacy compiler's physical-row replay).
fn validate_forest_poseidon_row(
    columns: &[Vec<M31>; 16],
    block: usize,
    local_row: usize,
    expected: [M31; 16],
) -> Result<(), PoolV1PairTraceErrorV1> {
    for lane in 0..16 {
        if columns[lane][block * 16 + local_row] != expected[lane] {
            return Err(PoolV1PairTraceErrorV1::BlockMismatch {
                block: block as u8,
                local_row: local_row as u8,
                lane: lane as u8,
            });
        }
    }
    Ok(())
}

fn validate_forest_poseidon_block(
    columns: &[Vec<M31>; 16],
    block: usize,
) -> Result<(), PoolV1PairTraceErrorV1> {
    let base = block * 16;
    let mut state = core::array::from_fn(|lane| columns[lane][base]);
    for lane in 0..RATE {
        state[lane] = state[lane].add(columns[lane][base + 12]);
    }
    let mut result = Ok(());
    let mut local_row = 0;
    while local_row < 11 && result.is_ok() {
        match evaluate_trace_round_pair(state, local_row) {
            Some((_, second)) => {
                result = validate_forest_poseidon_row(columns, block, local_row + 1, second);
                state = second;
            }
            None => result = Err(PoolV1PairTraceErrorV1::HashSchedule),
        }
        local_row += 1;
    }
    local_row = 13;
    while local_row < 16 && result.is_ok() {
        result = validate_forest_poseidon_row(columns, block, local_row, [M31::ZERO; 16]);
        local_row += 1;
    }
    result
}

fn validate_forest_poseidon_rows(banks: &CopyBanks) -> Result<(), PoolV1PairTraceErrorV1> {
    let mut result = Ok(());
    let mut block = 0;
    while block < 57 && result.is_ok() {
        let columns = if (34..54).contains(&block) {
            &banks.late
        } else {
            &banks.stable
        };
        result = validate_forest_poseidon_block(columns, block);
        block += 1;
    }
    result
}

/// The checked live append (blocks 34..53): the afterstate comes from the
/// incremental tree, and the copy-built append root must equal its root.
fn late_append(
    records: &CopyRecords,
    snapshot: PoolV1PairLiveSnapshotV1,
    output_pair: Digest,
) -> Result<PoolV1PairVerifiedAfterstateV1, PoolV1PairTraceErrorV1> {
    if snapshot.sequence != snapshot.next_pair_index {
        return Err(PoolV1PairTraceErrorV1::SnapshotBindingMismatch);
    }
    let empty = pair_empty_roots();
    let source = IncrementalMerkleTreeV1::from_parts_with_empty_roots(
        snapshot.next_pair_index,
        snapshot.current_root,
        snapshot.frontier,
        &empty,
    )
    .map_err(PoolV1PairTraceErrorV1::Tree)?;
    let (next, _) = source
        .append_one_with_empty_roots(output_pair, &empty)
        .map_err(PoolV1PairTraceErrorV1::Tree)?;
    if records.append_root() != next.root {
        return Err(PoolV1PairTraceErrorV1::SnapshotBindingMismatch);
    }
    Ok(PoolV1PairVerifiedAfterstateV1 {
        next_pair_index: next.next_leaf_index,
        next_root: next.root,
        next_frontier: next.frontier,
    })
}

/// The public values a forest compilation is checked against.
struct ForestPublic {
    anchor: Digest,
    nullifier: Digest,
    recipient_commitment: Option<Digest>,
    change_commitment: Digest,
    asset: M31,
}

/// Build the forest compilation from the extracted copies (LOG D68.2), after
/// the caller's statement, binding and conservation checks.  The digest checks
/// run in the pre-migration order: input commitment, pair leaf, lane anchor,
/// nullifier, recipient, change, output pair, live append, super-root
/// canonicity, global anchor.  `recipient` is `Some` exactly for a transfer.
fn compile_forest_from_copies(
    input: &PoolV1PairForestInputNoteWitnessV1,
    out_value: u32,
    recipient: Option<&PoolV1OutputNoteWitnessV1>,
    change: &PoolV1OutputNoteWitnessV1,
    public: ForestPublic,
    lane_anchor: Digest,
    snapshot: PoolV1PairLiveSnapshotV1,
) -> Result<PoolV1PairForestMergedC1CompilationV1, PoolV1PairTraceErrorV1> {
    let pair = &input.pair;
    let records = CopyRecords::new(input, out_value, recipient, change, &snapshot, public.asset);
    if pair.pair_leaf.selected_commitment(pair.selected_second) != &records.input_leaf() {
        return Err(PoolV1PairTraceErrorV1::SelectedCommitmentMismatch);
    }
    if records.path_digest(1)
        != pair
            .pair_leaf
            .leaf_digest()
            .map_err(PoolV1PairTraceErrorV1::PairLeaf)?
    {
        return Err(PoolV1PairTraceErrorV1::SelectedCommitmentMismatch);
    }
    if records.path_digest(21) != lane_anchor {
        return Err(PoolV1PairTraceErrorV1::AnchorMismatch);
    }
    let nullifier = records.nullifier();
    if nullifier != public.nullifier
        || nullifier != pool_v1_nullifier(&pair.nullifier_key, &pair.salt)
    {
        return Err(PoolV1PairTraceErrorV1::NullifierMismatch);
    }
    let change_commitment = records.change();
    let recipient_commitment = match public.recipient_commitment {
        Some(expected) => {
            let recipient_commitment = records.recipient();
            if recipient_commitment != expected {
                return Err(PoolV1PairTraceErrorV1::RecipientCommitmentMismatch);
            }
            Some(recipient_commitment)
        }
        None => None,
    };
    if change_commitment != public.change_commitment {
        return Err(PoolV1PairTraceErrorV1::ChangeCommitmentMismatch);
    }
    match recipient_commitment {
        Some(recipient_commitment) => {
            PoolV1PairLeafWitnessV1::two_outputs(recipient_commitment, change_commitment)
        }
        None => PoolV1PairLeafWitnessV1::single_output(change_commitment),
    }
    .map_err(PoolV1PairTraceErrorV1::PairLeaf)?;
    let output_pair = records.output_pair();
    let afterstate = late_append(&records, snapshot, output_pair)?;
    if input
        .super_root_siblings
        .iter()
        .flatten()
        .any(|limb| limb.0 >= aspis_core::field::P)
    {
        return Err(PoolV1PairTraceErrorV1::WitnessDigest);
    }
    let anchor = records.path_digest(24);
    if anchor != public.anchor {
        return Err(PoolV1PairTraceErrorV1::AnchorMismatch);
    }
    let banks = records.banks().ok_or(PoolV1PairTraceErrorV1::Shape)?;
    validate_forest_poseidon_rows(&banks)?;
    let private_directions = core::array::from_fn(|level| {
        M31(if level == 0 {
            u32::from(pair.selected_second)
        } else if level <= 20 {
            (pair.membership.index >> (level - 1)) & 1
        } else {
            u32::from(input.super_root_directions[level - 21])
        })
    });
    let (variant, public_outputs) = match recipient_commitment {
        Some(recipient_commitment) => (
            PoolV1PairTraceVariantV1::PrivateTransfer,
            PoolV1PairTracePublicOutputsV1::PrivateTransfer {
                anchor,
                nullifier,
                recipient_commitment,
                change_commitment,
                output_pair,
            },
        ),
        None => (
            PoolV1PairTraceVariantV1::Withdrawal,
            PoolV1PairTracePublicOutputsV1::Withdrawal {
                anchor,
                nullifier,
                change_commitment,
                output_pair,
            },
        ),
    };
    let CopyBanks {
        stable,
        late,
        merged,
    } = banks;
    Ok(PoolV1PairForestMergedC1CompilationV1 {
        public_statement: PoolV1PairLatePublicStatementV1 {
            live_snapshot: snapshot,
            candidate_afterstate: afterstate,
        },
        trace: PoolV1PairForestTraceV1 {
            stable: StateOnlyTraceFoundation { c1: stable },
            late,
            variant,
            private_directions,
            value_bits: [
                value_bits(pair.value),
                value_bits(out_value),
                value_bits(change.value),
            ],
            public_outputs,
            afterstate,
        },
        semantic_c1: StateOnlyTraceFoundation { c1: merged },
    })
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
    validate_pool_v1_private_transfer_public_v1(&temporary_public)
        .map_err(PoolV1PairTraceErrorV1::Statement)?;
    validate_common(
        temporary_public.pool,
        temporary_public.deployment_domain,
        temporary_public.anchor_sequence,
        temporary_public.anchor_root,
        temporary_public.nullifier,
        temporary_public.asset_id,
        &witness.input.pair,
        temporary_context(context, lane_anchor),
    )?;
    if snapshot.pool != public.pool || snapshot.deployment_domain != public.deployment_domain {
        return Err(PoolV1PairTraceErrorV1::SnapshotBindingMismatch);
    }
    if witness.recipient.value == 0
        || witness.change.value == 0
        || witness.recipient.value >= VALUE_LIMIT
        || witness.change.value >= VALUE_LIMIT
        || witness.recipient.value.checked_add(witness.change.value)
            != Some(witness.input.pair.value)
    {
        return Err(PoolV1PairTraceErrorV1::Conservation);
    }
    compile_forest_from_copies(
        &witness.input,
        witness.recipient.value,
        Some(&witness.recipient),
        &witness.change,
        ForestPublic {
            anchor: public.anchor_root,
            nullifier: public.nullifier,
            recipient_commitment: Some(public.recipient_commitment),
            change_commitment: public.change_commitment,
            asset: public.asset_id,
        },
        lane_anchor,
        snapshot,
    )
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
    validate_pool_v1_withdrawal_public_v1(&temporary_public)
        .map_err(PoolV1PairTraceErrorV1::Statement)?;
    validate_common(
        temporary_public.pool,
        temporary_public.deployment_domain,
        temporary_public.anchor_sequence,
        temporary_public.anchor_root,
        temporary_public.nullifier,
        temporary_public.asset_id,
        &witness.input.pair,
        temporary_context(context, lane_anchor),
    )?;
    if snapshot.pool != public.pool || snapshot.deployment_domain != public.deployment_domain {
        return Err(PoolV1PairTraceErrorV1::SnapshotBindingMismatch);
    }
    if witness.change.value == 0
        || witness.change.value >= VALUE_LIMIT
        || public.amount.checked_add(witness.change.value) != Some(witness.input.pair.value)
    {
        return Err(PoolV1PairTraceErrorV1::Conservation);
    }
    compile_forest_from_copies(
        &witness.input,
        public.amount,
        None,
        &witness.change,
        ForestPublic {
            anchor: public.anchor_root,
            nullifier: public.nullifier,
            recipient_commitment: None,
            change_commitment: public.change_commitment,
            asset: public.asset_id,
        },
        lane_anchor,
        snapshot,
    )
}

fn tuple_cells(row: usize, start: usize, count: usize, tweak_right: bool) -> PoolV1PairCopyTupleV1 {
    let bank = if (544..864).contains(&row) {
        PoolV1PairTraceBankV1::Late
    } else {
        PoolV1PairTraceBankV1::Stable
    };
    let mut limbs = [PoolV1PairTupleLimbV1::Zero; 16];
    for lane in 0..count {
        let column = start + lane;
        let offset = if tweak_right && lane + 1 == count {
            M31::ZERO.sub(MERKLE_NODE_COMPRESSION_V3_TWEAK)
        } else {
            M31::ZERO
        };
        limbs[lane] = PoolV1PairTupleLimbV1::Cell {
            source: PoolV1PairTraceCellV1 {
                bank,
                cell: TraceCell {
                    row: row as u16,
                    column: column as u8,
                },
            },
            offset,
        };
    }
    PoolV1PairCopyTupleV1 {
        row: row as u16,
        limbs,
    }
}

fn translate_aux_tuple(mut tuple: PoolV1PairCopyTupleV1) -> PoolV1PairCopyTupleV1 {
    if usize::from(tuple.row) >= 864 {
        tuple.row += 48;
    }
    let mut i=0usize;
    while i<16 {
        match tuple.limbs[i] {
            PoolV1PairTupleLimbV1::Cell {mut source,offset} => {
                if usize::from(source.cell.row)>=864 {source.cell.row+=48;}
                tuple.limbs[i]=PoolV1PairTupleLimbV1::Cell {source,offset};
            }
            PoolV1PairTupleLimbV1::Zero => {}
        }
        i+=1;
    }
    tuple
}

fn path_kind(kind: PoolV1PairCopyRowLinkKindV1) -> bool {
    matches!(
        kind,
        PoolV1PairCopyRowLinkKindV1::PrivatePathCurrent { .. }
            | PoolV1PairCopyRowLinkKindV1::PrivatePathLeft { .. }
            | PoolV1PairCopyRowLinkKindV1::PrivatePathRight { .. }
    )
}

pub fn build_pool_v1_pair_forest_copy_registry_v1(
) -> Result<Vec<PoolV1PairCopyLinkV1>, PoolV1PairTraceErrorV1> {
    let legacy = build_pool_v1_pair_copy_registry_v1()?;
    let schedule = build_pool_v1_pair_forest_copy_row_schedule_v1()
        .map_err(|_| PoolV1PairTraceErrorV1::CopyLayout)?;
    let mut output = Vec::with_capacity(schedule.len());
    let mut schedule_index=0usize;
    while schedule_index<schedule.len() {
        let scheduled=schedule[schedule_index];
        let (producer, consumer, weight) = if path_kind(scheduled.kind) {
            match scheduled.kind {
                PoolV1PairCopyRowLinkKindV1::PrivatePathCurrent { .. } => (
                    tuple_cells(usize::from(scheduled.producer_row), 0, 8, false),
                    tuple_cells(usize::from(scheduled.consumer_row), 1, 8, false),
                    PoolV1PairCopyWeightV1::One,
                ),
                PoolV1PairCopyRowLinkKindV1::PrivatePathLeft { .. } => (
                    tuple_cells(usize::from(scheduled.producer_row), 0, 8, false),
                    tuple_cells(usize::from(scheduled.consumer_row), 0, 8, false),
                    PoolV1PairCopyWeightV1::One,
                ),
                PoolV1PairCopyRowLinkKindV1::PrivatePathRight { .. } => (
                    tuple_cells(usize::from(scheduled.producer_row), 8, 8, false),
                    tuple_cells(usize::from(scheduled.consumer_row), 8, 8, true),
                    PoolV1PairCopyWeightV1::One,
                ),
                _ => return Err(PoolV1PairTraceErrorV1::CopyLayout),
            }
        } else {
            let mut found=None;
            let mut i=0usize;
            while i<legacy.len() && found.is_none() {
                if legacy[i].kind==scheduled.kind {found=Some(legacy[i]);}
                i+=1;
            }
            let old=match found {Some(v)=>v,None=>return Err(PoolV1PairTraceErrorV1::CopyLayout)};
            (
                translate_aux_tuple(old.producer),
                translate_aux_tuple(old.consumer),
                old.weight,
            )
        };
        if producer.row != scheduled.producer_row || consumer.row != scheduled.consumer_row {
            return Err(PoolV1PairTraceErrorV1::CopyLayout);
        }
        let id = output.len() as u16;
        output.push(PoolV1PairCopyLinkV1 {
            id,
            tag: M31(POOL_V1_PAIR_COPY_TAG_BASE_V1 + u32::from(id)),
            kind: scheduled.kind,
            weight,
            producer,
            consumer,
        });
            schedule_index+=1;
    }
    if output.len() != POOL_V1_PAIR_FOREST_COPY_ROW_LINKS_V1 {
        return Err(PoolV1PairTraceErrorV1::CopyLayout);
    }
    Ok(output)
}

fn tuple_value(trace: &PoolV1PairForestTraceV1, tuple: PoolV1PairCopyTupleV1) -> [M31; 16] {
    tuple.limbs.map(|limb| match limb {
        PoolV1PairTupleLimbV1::Zero => M31::ZERO,
        PoolV1PairTupleLimbV1::Cell { source, offset } => {
            let columns = match source.bank {
                PoolV1PairTraceBankV1::Stable => &trace.stable.c1,
                PoolV1PairTraceBankV1::Late => &trace.late,
            };
            columns[source.cell.column as usize][source.cell.row as usize].add(offset)
        }
    })
}

fn copy_weight(
    weight: PoolV1PairCopyWeightV1,
    append_index: u64,
    variant: PoolV1PairTraceVariantV1,
) -> M31 {
    match weight {
        PoolV1PairCopyWeightV1::One => M31::ONE,
        PoolV1PairCopyWeightV1::PrivateTransferOnly => M31(u32::from(
            variant == PoolV1PairTraceVariantV1::PrivateTransfer,
        )),
        PoolV1PairCopyWeightV1::WithdrawalOnly => {
            M31(u32::from(variant == PoolV1PairTraceVariantV1::Withdrawal))
        }
        PoolV1PairCopyWeightV1::AppendCurrentLeft { level } => {
            M31(1 - ((append_index >> level) & 1) as u32)
        }
        PoolV1PairCopyWeightV1::AppendCurrentRight { level } => {
            M31(((append_index >> level) & 1) as u32)
        }
    }
}

pub fn pool_v1_pair_forest_copy_rows_v1(
    trace: &PoolV1PairForestTraceV1,
    append_index: u64,
    lambda: QM31,
) -> Result<Vec<CopyLogUpRow>, PoolV1PairTraceErrorV1> {
    let empty = CopyLogUpRow {
        producer_values: [QM31::ZERO; 2],
        producer_weights: [M31::ZERO; 2],
        consumer_values: [QM31::ZERO; 2],
        consumer_weights: [M31::ZERO; 2],
    };
    let mut rows = vec![empty; 1024];
    for link in build_pool_v1_pair_forest_copy_registry_v1()? {
        let weight = copy_weight(link.weight, append_index, trace.variant);
        for (tuple, producer) in [(link.producer, true), (link.consumer, false)] {
            let row = &mut rows[tuple.row as usize];
            let (values, weights) = if producer {
                (&mut row.producer_values, &mut row.producer_weights)
            } else {
                (&mut row.consumer_values, &mut row.consumer_weights)
            };
            let slot = weights
                .iter()
                .position(|value| *value == M31::ZERO)
                .ok_or(PoolV1PairTraceErrorV1::CopyLayout)?;
            values[slot] = compress_tagged_tuple(link.tag, &tuple_value(trace, tuple), lambda);
            weights[slot] = weight;
        }
    }
    Ok(rows)
}

pub fn verify_pool_v1_pair_forest_copy_registry_v1(
    trace: &PoolV1PairForestTraceV1,
    append_index: u64,
    lambda: QM31,
    chi: QM31,
) -> Result<(), PoolV1PairTraceErrorV1> {
    let rows = pool_v1_pair_forest_copy_rows_v1(trace, append_index, lambda)?;
    let helper =
        build_copy_logup_helper(&rows, chi).map_err(|_| PoolV1PairTraceErrorV1::CopyImbalance)?;
    verify_copy_logup_constraints(&rows, &helper, chi)
        .map_err(|_| PoolV1PairTraceErrorV1::CopyImbalance)
}

const _: () = assert!(POOL_V1_PAIR_FOREST_VALUE_AUX_ROW_START_V1 == 1008);
const _: () = assert!(POOL_V1_PAIR_FOREST_INPUT_OCCUPANCY_AUX_ROW_V1 == 1017);
const _: () = assert!(POOL_V1_PAIR_FOREST_OUTPUT_OCCUPANCY_AUX_ROW_V1 == 1018);
