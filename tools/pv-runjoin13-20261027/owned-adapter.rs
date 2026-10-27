//! Proof-only ownership adapter. No mapper algorithm is transcribed here.
use super::*;
#[inline(never)]
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
// Keep the foreign adapter in the pinned extractor's dependency analysis.
pub(super) fn keep_records_owned(
    input: PoolV1PairForestInputNoteWitnessV1,
    out: u32,
    rec: Option<PoolV1OutputNoteWitnessV1>,
    chg: PoolV1OutputNoteWitnessV1,
    snapshot: PoolV1PairLiveSnapshotV1,
    asset: M31,
) -> (RW, RP) {
    records_owned(input, out, rec, chg, snapshot, asset)
}
