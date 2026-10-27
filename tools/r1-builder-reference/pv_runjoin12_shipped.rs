//! Owned borrow adapter only: executes the unmodified shipped records leaf.
//! Parent and this child are available only under cfg(aeneas_ref).
use super::*;

pub(super) fn records_owned(
    input: PoolV1PairForestInputNoteWitnessV1,
    out: u32,
    rec: Option<PoolV1OutputNoteWitnessV1>,
    chg: PoolV1OutputNoteWitnessV1,
    snapshot: PoolV1PairLiveSnapshotV1,
    asset: M31,
) -> (RW, RP) {
    super::super::records(&input, out, rec.as_ref(), &chg, &snapshot, asset)
}

// Variant-specific adapters expose the shipped call with a fixed Option tag.
// They contain no mapping algorithm or replacement helper.
pub(super) fn records_transfer_owned(
    input: super::super::PoolV1PairForestInputNoteWitnessV1,
    out: u32,
    recipient: super::super::PoolV1OutputNoteWitnessV1,
    change: super::super::PoolV1OutputNoteWitnessV1,
    snapshot: super::super::PoolV1PairLiveSnapshotV1,
    asset: super::super::M31,
) -> (super::super::RW, super::super::RP) {
    super::super::records(&input, out, Some(&recipient), &change, &snapshot, asset)
}

pub(super) fn records_withdrawal_owned(
    input: super::super::PoolV1PairForestInputNoteWitnessV1,
    out: u32,
    change: super::super::PoolV1OutputNoteWitnessV1,
    snapshot: super::super::PoolV1PairLiveSnapshotV1,
    asset: super::super::M31,
) -> (super::super::RW, super::super::RP) {
    super::super::records(&input, out, None, &change, &snapshot, asset)
}
