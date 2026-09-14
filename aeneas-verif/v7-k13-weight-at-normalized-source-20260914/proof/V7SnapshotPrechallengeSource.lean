import V7PrequeryDot256Source

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V7SnapshotPrechallengeSource

open V7WeightAtReleaseFieldBridge

abbrev QM31 := V7WeightAtRelease.field.QM31
abbrev ExactQM31 := V7WeightAtReleaseFieldBridge.ExactQM31
abbrev View := V7WeightAtRelease.v6_transcript.V6QueryBatchPrechallengeView
abbrev Snapshot := V7WeightAtRelease.v6_transcript.V6QueryBatchPrechallengeSnapshot

structure CopiedFields (view : View) (out : Snapshot) : Prop where
  transcript_state : out.transcript_state = view.transcript_state
  running_claim : out.running_claim = view.running_claim
  gamma : out.gamma = view.gamma
  alpha0 : out.alpha0 = view.alpha0
  queries : out.queries = view.queries
  selector : out.selector = view.selector
  compact_counter : out.compact_counter = view.compact_counter
  frontier_nodes : out.frontier_nodes = view.frontier_nodes

/-- The literal current-source snapshot consumes the genuine 256-entry helper,
    subtracts its exact result from the running claim, and copies every other
    prechallenge field without alteration. -/
theorem generated_snapshot_prechallenge_corresponds
    (view : View) (coefficient weight : Nat → ExactQM31)
    (hRunning : GeneratedCanonicalQM31 view.running_claim)
    (hCoefficientCanonical : ∀ i, i < 256 →
      GeneratedCanonicalQM31 view.final256_coefficients.val[i]!)
    (hCoefficientExact : ∀ i, i < 256 →
      generatedQm31ToExact view.final256_coefficients.val[i]! = coefficient i)
    (hWeight : ∀ i : Std.U32, i.val < 256 → ∃ raw,
      V7WeightAtRelease.sumcheck.WeightAccumulator.weight_at view.weights i = ok raw ∧
      GeneratedCanonicalQM31 raw ∧ generatedQm31ToExact raw = weight i.val) :
    V7WeightAtRelease.v6_transcript.snapshot_query_batch_prechallenge view
      ⦃ out => CopiedFields view out ∧
        GeneratedCanonicalQM31 out.terminal_discrepancy ∧
        generatedQm31ToExact out.terminal_discrepancy =
          generatedQm31ToExact view.running_claim -
            V7PrequeryDot256Source.dotPrefix coefficient weight 256 ⦄ := by
  obtain ⟨dot, hDotRun, hDotCanonical, hDotExact⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (V7PrequeryDot256Source.generated_prequery_dot_256_corresponds
        view.weights view.final256_coefficients coefficient weight
        hCoefficientCanonical hCoefficientExact hWeight)
  obtain ⟨discrepancy, hSubRun, hDiscrepancyCanonical, hDiscrepancyExact⟩ :=
    generated_qm31_sub_corresponds view.running_claim dot hRunning hDotCanonical
  unfold V7WeightAtRelease.v6_transcript.snapshot_query_batch_prechallenge
  rw [hDotRun]
  simp only [bind_tc_ok]
  rw [hSubRun]
  simp only [bind_tc_ok, Aeneas.Std.WP.spec_ok]
  refine ⟨?_, hDiscrepancyCanonical, ?_⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rw [hDiscrepancyExact, hDotExact]

#print axioms generated_snapshot_prechallenge_corresponds

end V7SnapshotPrechallengeSource
