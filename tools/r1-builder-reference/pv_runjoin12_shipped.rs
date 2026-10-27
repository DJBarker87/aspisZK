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
