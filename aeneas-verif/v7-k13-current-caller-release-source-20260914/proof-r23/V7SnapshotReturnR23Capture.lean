import V7SnapshotReturnR23SnapshotPrechallengeSource

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V7SnapshotReturnR23Capture

open V7SnapshotReturnR23
open V7SnapshotReturnR23FieldBridge

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

/-- With capture enabled, the concrete source helper returns a snapshot whose
    terminal discrepancy is the exact 256-term prequery residual. -/
theorem generated_capture_true_snapshot_witness
    (view : v6_transcript.V6QueryBatchPrechallengeView)
    (coefficient weight : Nat → ExactQM31)
    (hRunning : GeneratedCanonicalQM31 view.running_claim)
    (hCoefficientCanonical : ∀ i, i < 256 →
      GeneratedCanonicalQM31 view.final256_coefficients.val[i]!)
    (hCoefficientExact : ∀ i, i < 256 →
      generatedQm31ToExact view.final256_coefficients.val[i]! = coefficient i)
    (hWeight : ∀ i : Std.U32, i.val < 256 → ∃ raw,
      sumcheck.WeightAccumulator.impl.weight_at view.weights i = ok raw ∧
      GeneratedCanonicalQM31 raw ∧ generatedQm31ToExact raw = weight i.val) :
    ∃ snapshot,
      v6_transcript.capture_v6_query_batch_prechallenge true view = ok (some snapshot) ∧
      V7SnapshotReturnR23SnapshotPrechallengeSource.CopiedFields view snapshot ∧
      GeneratedCanonicalQM31 snapshot.terminal_discrepancy ∧
      generatedQm31ToExact snapshot.terminal_discrepancy =
        generatedQm31ToExact view.running_claim -
          V7SnapshotReturnR23PrequeryDot256Source.dotPrefix coefficient weight 256 := by
  obtain ⟨snapshot, hSnapshotRun, hCopied, hCanonical, hExact⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (V7SnapshotReturnR23SnapshotPrechallengeSource.generated_snapshot_prechallenge_corresponds
        view coefficient weight hRunning hCoefficientCanonical hCoefficientExact hWeight)
  exact ⟨snapshot, generated_capture_true_returns_some view snapshot hSnapshotRun,
    hCopied, hCanonical, hExact⟩

#print axioms generated_capture_true_returns_some
#print axioms generated_capture_true_snapshot_witness

end V7SnapshotReturnR23Capture
