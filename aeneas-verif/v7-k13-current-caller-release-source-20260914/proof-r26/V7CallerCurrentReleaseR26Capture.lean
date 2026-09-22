import V7CallerCurrentReleaseR26.Funs

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V7CallerCurrentReleaseR26Capture

open V7CallerCurrentReleaseR26

/-- Invert a successful `Result` bind without unfolding its continuation. -/
theorem bind_eq_ok_iff {A B : Type} (input : Result A)
    (next : A → Result B) (output : B) :
    Bind.bind input next = .ok output ↔
      ∃ value, input = .ok value ∧ next value = .ok output := by
  cases input <;> simp [Bind.bind, Aeneas.Std.bind]

/-- The actual generated production helper preserves its source branch: when
capture is enabled, every successful return is `some` of the snapshot computed
from the same prechallenge view. -/
theorem capture_true_success_is_source_snapshot
    (view : v6_transcript.V6QueryBatchPrechallengeView)
    (output : Option v6_transcript.V6QueryBatchPrechallengeSnapshot)
    (success : v6_transcript.capture_v6_query_batch_prechallenge true view = ok output) :
    ∃ snapshot,
      output = some snapshot ∧
      v6_transcript.snapshot_query_batch_prechallenge view = ok snapshot := by
  unfold v6_transcript.capture_v6_query_batch_prechallenge at success
  simp only [↓reduceIte] at success
  rw [bind_eq_ok_iff] at success
  obtain ⟨snapshot, snapshotRun, outputRun⟩ := success
  exact ⟨snapshot, Aeneas.Std.Result.ok.inj outputRun.symm, snapshotRun⟩

/-- Conversely, a successful source snapshot computation is returned verbatim
by the enabled capture helper. -/
theorem capture_true_returns_source_snapshot
    (view : v6_transcript.V6QueryBatchPrechallengeView)
    (snapshot : v6_transcript.V6QueryBatchPrechallengeSnapshot)
    (snapshotRun : v6_transcript.snapshot_query_batch_prechallenge view = ok snapshot) :
    v6_transcript.capture_v6_query_batch_prechallenge true view = ok (some snapshot) := by
  simp only [v6_transcript.capture_v6_query_batch_prechallenge, ↓reduceIte,
    snapshotRun, bind_tc_ok]

#print axioms bind_eq_ok_iff
#print axioms capture_true_success_is_source_snapshot
#print axioms capture_true_returns_source_snapshot

end V7CallerCurrentReleaseR26Capture
