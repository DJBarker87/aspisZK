# PCWI_ HANDOFF (job P3z: op50 = transcription)

Target not yet established. op50 stays OPEN until the owner accepts ReviewedTranscription-LaneDecode; nothing in the ledger, trust rows, RSL, contract or shipped source was touched; nothing pushed or merged.

## Established (exit 0, axioms propext/Classical.choice/Quot.sound only, no sorry/native_decide, heartbeats default)
- PRVEq_Op50_q1.lean (scope PCWI_L002, 6.7 s, peak RSS 2.6 GB, swap 0): `decode_lane_ref_eq b : exists r, NCV_Reference.decode_lane_ref b = ok r /\ LCmp (decodeLane K0 (bytesOf b)) r` for every b. No premise on b. The proof splits on HdrOK (p12/p13 for the failing case), then ref_pass (compiled definition = stage copy zT0..zT5), the master zero test (zs_iff, zero_eq, bytes32_eq), the tree guards (treeBad_false_iff, ref_tree_bad/ok), word64 and the capacity guard (sim3), the root digest (sim4, digest_eq), and frontier plus the empty-root check (sim5, frontier_eq, eq_digest_eq, emp20).
- PRVEq_Op50_q2.lean (scope PCWI_L004, 10.1 s, peak RSS 6.7 GB, swap 0): `op50_eq_transcription c b`: for every host context and input, `(NOC_HostCtx.sdk c).op50 b = ok (laneOut r)` with the same r that satisfies the q1 equality. Uses op50_slot (rfl) via NNH_LaneModel.decode.
- q2 imports the NNH/NOC closure: peak RSS 6.7 GB is under the 8 GiB cap but close; do not add imports to it.

## Not established / unchanged
The fidelity of the hand transcription to the Rust text and of decDig to decode_digest_canonical (PCVY_TRANSCRIPTION_REVIEW.md); this is the owner-pending trust row. Nothing here shows the row accepted.

## Scopes
4 of 10 Lean scopes (2 exit 1: layout of a structure instance; SDK type names), 0 extraction. One scope at a time; caps unraised.
