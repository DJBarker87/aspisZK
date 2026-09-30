import V7ProductionCallbacksR30FoldQueriesCanonical
import V7ProductionCallbacksR30CoordinatesCanonical

/-! Canonical values returned by the literal production query-fold callback. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
open Aeneas Aeneas.Std Result ControlFlow Error

namespace V7ProductionCallbacksR30QueryValuesCanonical
open V7ProductionCallbacksR30MutableCanonical
open V7ProductionCallbacksR30QueryGammaCanonical
open V7ProductionCallbacksR30FoldQueriesCanonical
open V7CallerCurrentReleaseR26FieldBridge
local instance : Inhabited V7CallerCurrentReleaseR26.field.QM31 :=
  V7ProductionCallbacksR30FoldQueriesCanonical.instInhabitedQM31

private theorem bind_eq_ok_iff {Input Output : Type}
    (input : Result Input) (next : Input → Result Output) (output : Output) :
    (do let value ← input; next value) = ok output ↔
      ∃ value, input = ok value ∧ next value = ok output := by
  cases input <;> simp [Bind.bind, Aeneas.Std.bind]

theorem successful_authenticate_and_fold_queries_values_canonical
    (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
    (wire : V7ProductionCallbacksR29.aspis_core.v7_onefold.V7CompactOneFoldWire)
    (view : V7ProductionCallbacksR29.aspis_core.v6_transcript.V6QueryBatchView)
    (authenticated : V7ProductionCallbacksR29.aspis_core.v6_query_batch.V6AuthenticatedQueryBatch)
    (run : V7ProductionCallbacksR29.v7_verifier.authenticate_and_fold_queries
      hash wire view = ok (.Ok authenticated)) :
    SliceAll GeneratedCanonicalQM31 authenticated.values.to_slice := by
  unfold V7ProductionCallbacksR29.v7_verifier.authenticate_and_fold_queries at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨coordinateResult, coordinateRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨coordinateBranch, coordinateBranchRun, run⟩ := run
  cases coordinateResult with
  | Ok coordinates =>
      have coordinateBranchExact : coordinateBranch = .Continue coordinates := by
        simpa [core.result.Result.Insts.CoreOpsTry.branch] using
          (Result.ok.inj coordinateBranchRun).symm
      rw [coordinateBranchExact] at run
      simp only at run
      rw [bind_eq_ok_iff] at run
      obtain ⟨combinedResult, combinedRun, run⟩ := run
      rw [bind_eq_ok_iff] at run
      obtain ⟨combinedBranch, combinedBranchRun, run⟩ := run
      cases combinedResult with
      | Ok combined =>
          have combinedBranchExact : combinedBranch = .Continue combined := by
            simpa [core.result.Result.Insts.CoreOpsTry.branch] using
              (Result.ok.inj combinedBranchRun).symm
          rw [combinedBranchExact] at run
          simp only at run
          rw [bind_eq_ok_iff] at run
          obtain ⟨folded, foldedRun, run⟩ := run
          have combinedCanonical := successful_query_gamma_canonical
            hash wire view.queries view.gamma_powers combined combinedRun
          have foldedCanonical := successful_fold_queries_canonical
            combined coordinates view.alpha0 folded combinedCanonical foldedRun
          have authenticatedExact : authenticated =
              { values := folded, line_x := coordinates.line_x } := by
            exact (core.result.Result.Ok.inj (Result.ok.inj run)).symm
          rw [authenticatedExact]
          exact foldedCanonical
      | Err error =>
          have combinedBranchExact : combinedBranch = .Break (.Err error) := by
            simpa [core.result.Result.Insts.CoreOpsTry.branch] using
              (Result.ok.inj combinedBranchRun).symm
          rw [combinedBranchExact] at run
          simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from] at run
  | Err error =>
      have coordinateBranchExact : coordinateBranch = .Break (.Err error) := by
        simpa [core.result.Result.Insts.CoreOpsTry.branch] using
          (Result.ok.inj coordinateBranchRun).symm
      rw [coordinateBranchExact] at run
      simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from] at run

/-- The production observer uses the callback implementation above through
its generated external binding.  This theorem follows the observer's literal
wrapper, retaining the canonical source-coordinate line at its query-fold
boundary. -/
theorem successful_production_observer_authenticate_and_fold_queries_values_canonical
    (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
    (wire : aspis_core.v7_onefold.V7CompactOneFoldWire)
    (view : V7ProductionSnapshotObserverR28.aspis_core.v6_transcript.V6QueryBatchView)
    (authenticated : V7ProductionSnapshotObserverR28.aspis_core.v6_query_batch.V6AuthenticatedQueryBatch)
    (run : V7ProductionSnapshotObserverR28.v7_verifier.authenticate_and_fold_queries
      hash wire view = ok (.Ok authenticated)) :
    SliceAll GeneratedCanonicalQM31 authenticated.values.to_slice := by
  unfold V7ProductionSnapshotObserverR28.v7_verifier.authenticate_and_fold_queries at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨coordinateResult, coordinateRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨coordinateBranch, coordinateBranchRun, run⟩ := run
  cases coordinateResult with
  | Ok coordinates =>
      have coordinateBranchExact : coordinateBranch = .Continue coordinates := by
        simpa [core.result.Result.Insts.CoreOpsTry.branch] using
          (Result.ok.inj coordinateBranchRun).symm
      rw [coordinateBranchExact] at run
      simp only at run
      rw [bind_eq_ok_iff] at run
      obtain ⟨combinedResult, combinedRun, run⟩ := run
      rw [bind_eq_ok_iff] at run
      obtain ⟨combinedBranch, combinedBranchRun, run⟩ := run
      cases combinedResult with
      | Ok combined =>
          have combinedBranchExact : combinedBranch = .Continue combined := by
            simpa [core.result.Result.Insts.CoreOpsTry.branch] using
              (Result.ok.inj combinedBranchRun).symm
          rw [combinedBranchExact] at run
          simp only at run
          rw [bind_eq_ok_iff] at run
          obtain ⟨folded, foldedRun, run⟩ := run
          have combinedCanonical := successful_query_gamma_canonical
            hash wire view.queries view.gamma_powers combined combinedRun
          have foldedCanonical := successful_fold_queries_canonical
            combined coordinates view.alpha0 folded combinedCanonical foldedRun
          have authenticatedExact : authenticated =
              { values := folded, line_x := coordinates.line_x } := by
            exact (core.result.Result.Ok.inj (Result.ok.inj run)).symm
          rw [authenticatedExact]
          exact foldedCanonical
      | Err error =>
          have combinedBranchExact : combinedBranch = .Break (.Err error) := by
            simpa [core.result.Result.Insts.CoreOpsTry.branch] using
              (Result.ok.inj combinedBranchRun).symm
          rw [combinedBranchExact] at run
          simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from] at run
  | Err error =>
      have coordinateBranchExact : coordinateBranch = .Break (.Err error) := by
        simpa [core.result.Result.Insts.CoreOpsTry.branch] using
          (Result.ok.inj coordinateBranchRun).symm
      rw [coordinateBranchExact] at run
      simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from] at run

theorem successful_production_observer_query_fold_values_canonical
    (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
    (wire : aspis_core.v7_onefold.V7CompactOneFoldWire)
    (view : V7ProductionSnapshotObserverR28.aspis_core.v6_transcript.V6QueryBatchView)
    (authenticated : V7ProductionSnapshotObserverR28.aspis_core.v6_query_batch.V6AuthenticatedQueryBatch)
    (run : V7ProductionSnapshotObserverR28.v7_verifier.observe_v7_read_only_with_statement_digest.closure_1.Insts.CoreOpsFunctionFnOnceTupleSharedV6QueryBatchViewResultV6AuthenticatedQueryBatchV6WireError.call_once
      (hash, wire) view = ok (.Ok authenticated)) :
    SliceAll GeneratedCanonicalQM31 authenticated.values.to_slice := by
  change V7ProductionSnapshotObserverR28.v7_verifier.authenticate_and_fold_queries
    hash wire view = ok (.Ok authenticated) at run
  exact successful_production_observer_authenticate_and_fold_queries_values_canonical
    hash wire view authenticated run

#print axioms successful_authenticate_and_fold_queries_values_canonical
#print axioms successful_production_observer_query_fold_values_canonical
end V7ProductionCallbacksR30QueryValuesCanonical
