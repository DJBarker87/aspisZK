import V7SnapshotReturnR23.Funs

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V7SnapshotReturnR23Capture

open V7SnapshotReturnR23

/-- The generated source helper isolates the only observer branch: when
    capture is enabled, it returns `some` of exactly the source snapshot. -/
theorem generated_capture_true_returns_some
    (view : v6_transcript.V6QueryBatchPrechallengeView)
    (snapshot : v6_transcript.V6QueryBatchPrechallengeSnapshot)
    (hSnapshot : v6_transcript.snapshot_query_batch_prechallenge view = ok snapshot) :
    v6_transcript.capture_v6_query_batch_prechallenge true view =
      ok (some snapshot) := by
  simp only [v6_transcript.capture_v6_query_batch_prechallenge, ↓reduceIte,
    hSnapshot, bind_tc_ok]

#print axioms generated_capture_true_returns_some

end V7SnapshotReturnR23Capture
