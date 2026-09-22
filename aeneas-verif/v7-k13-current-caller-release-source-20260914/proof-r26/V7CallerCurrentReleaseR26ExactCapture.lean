import V7CallerCurrentReleaseR26SnapshotPrechallengeSource
import V7CallerCurrentReleaseR26Capture

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V7CallerCurrentReleaseR26ExactCapture

open V7CallerCurrentReleaseR26
open V7CallerCurrentReleaseR26FieldBridge

/-- The full-wrapper extraction's enabled capture branch returns a real source
snapshot and preserves the symbolic 256-term terminal discrepancy. -/
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
      V7CallerCurrentReleaseR26SnapshotPrechallengeSource.CopiedFields view snapshot ∧
      GeneratedCanonicalQM31 snapshot.terminal_discrepancy ∧
      generatedQm31ToExact snapshot.terminal_discrepancy =
        generatedQm31ToExact view.running_claim -
          V7CallerCurrentReleaseR26PrequeryDot256Source.dotPrefix coefficient weight 256 := by
  obtain ⟨snapshot, hSnapshotRun, hCopied, hCanonical, hExact⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (V7CallerCurrentReleaseR26SnapshotPrechallengeSource.generated_snapshot_prechallenge_corresponds
        view coefficient weight hRunning hCoefficientCanonical hCoefficientExact hWeight)
  exact ⟨snapshot,
    V7CallerCurrentReleaseR26Capture.capture_true_returns_source_snapshot
      view snapshot hSnapshotRun,
    hCopied, hCanonical, hExact⟩

#print axioms generated_capture_true_snapshot_witness

end V7CallerCurrentReleaseR26ExactCapture
