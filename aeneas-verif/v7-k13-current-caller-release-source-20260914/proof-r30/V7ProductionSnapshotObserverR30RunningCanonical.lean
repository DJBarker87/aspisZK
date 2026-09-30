import V7ProductionCallbacksR30QueryValuesCanonical
import V7ProductionSnapshotObserverR30CurrentTailCanonical
import V7CallerCurrentReleaseR26QueryScaleExactLoop
import V7CallerCurrentReleaseR26Qm31DotShortOuterLoop

/-! Discharge the terminal running-claim canonicality premise from source traces. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV7ProductionSnapshotObserverR30RunningCanonical
open V7ProductionCallbacksR30MutableCanonical
open V7ProductionCallbacksR30QueryValuesCanonical
open AspisV7ProductionSnapshotObserverR28SourceBridge
open AspisV7ProductionSnapshotObserverR28ToR26Prechallenge
open AspisV7ProductionSnapshotObserverR30InitialFoldTail
open AspisV7ProductionSnapshotObserverR30CurrentTailCanonical
open V7CallerCurrentReleaseR26
open V7CallerCurrentReleaseR26AcceptedInnerDispatch
open V7CallerCurrentReleaseR26AcceptedInnerToPrechallenge
open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26RelationDecodeSemantics
open V7CallerCurrentReleaseR26RelationEvaluatorSemantics
open V7CallerCurrentReleaseR30OuterAccumulator
open V7CallerCurrentReleaseR30CircleAccumulator
open V7CallerCurrentReleaseR30InitialPrechallengeDispatch
open V7CallerCurrentReleaseR30InitialFoldOrigin
open V7CallerCurrentReleaseR30CircleArithmeticCanonical
open V7CallerCurrentReleaseR30RelationFieldsCanonical
open V7ProductionSnapshotObserverR30RelationRowsCanonical
open V7ProductionSnapshotObserverR30InitialClaimCanonical
open V7CallerCurrentReleaseR26QueryScaleExactLoop
open V7CallerCurrentReleaseR26Qm31DotShortOuterLoop

local instance : Inhabited field.QM31 :=
  V7ProductionCallbacksR30FoldQueriesCanonical.instInhabitedQM31

theorem accepted_current_fold_tail_values_canonical
    {hash : HashFn} {wire : Wire}
    {context : v6_transcript.V6TranscriptContext}
    {hidingContext : HidingContext}
    {inactiveRowGroups : Array Std.U8 64#usize}
    {inactiveGroupMasks : Slice Std.U16} {checkPow : Bool}
    {statement : Statement}
    {transcript : AspisV7ProductionSnapshotObserverR28SourceBridge.Transcript}
    {snapshot : AspisV7ProductionSnapshotObserverR28SourceBridge.Snapshot}
    {inner : AcceptedInnerDispatch terminalInst queryFoldInst prechallengeInst
      hash wire context hidingContext inactiveRowGroups inactiveGroupMasks
      checkPow statement (hash, wire) () true transcript (some snapshot)}
    {chain : AcceptedInnerPrechallengeChain inner}
    {prepared : AcceptedPreparedAccumulator chain.outer}
    {accumulator : AcceptedCircleAccumulator prepared}
    {dispatch : AcceptedInitialPrechallengeDispatch accumulator.origin}
    (current : AcceptedCurrentFoldTail dispatch) :
    SliceAll GeneratedCanonicalQM31 current.tail.authenticatedQueries.values.to_slice := by
  exact successful_production_observer_query_fold_values_canonical
    hash wire current.tail.queryFoldView current.tail.authenticatedQueries current.tail.queryFoldRun

theorem accepted_current_fold_tail_before_query_canonical
    {hash : HashFn} {wire : Wire}
    {context : v6_transcript.V6TranscriptContext}
    {hidingContext : HidingContext}
    {inactiveRowGroups : Array Std.U8 64#usize}
    {inactiveGroupMasks : Slice Std.U16} {checkPow : Bool}
    {statement : Statement}
    {transcript : AspisV7ProductionSnapshotObserverR28SourceBridge.Transcript}
    {snapshot : AspisV7ProductionSnapshotObserverR28SourceBridge.Snapshot}
    {inner : AcceptedInnerDispatch terminalInst queryFoldInst prechallengeInst
      hash wire context hidingContext inactiveRowGroups inactiveGroupMasks
      checkPow statement (hash, wire) () true transcript (some snapshot)}
    {chain : AcceptedInnerPrechallengeChain inner}
    {prepared : AcceptedPreparedAccumulator chain.outer}
    {accumulator : AcceptedCircleAccumulator prepared}
    {dispatch : AcceptedInitialPrechallengeDispatch accumulator.origin}
    (current : AcceptedCurrentFoldTail dispatch) :
    GeneratedCanonicalQM31 dispatch.runningClaim := by
  have initial := accepted_production_initial_running_claim_canonical chain
  have afterZero :=
    V7CallerCurrentReleaseR30CircleArithmeticCanonical.AcceptedCircleStep.running_after_canonical
      accumulator.step0 initial
      (V7CallerCurrentReleaseR30CircleArithmeticCanonical.AcceptedCircleStep.fixed_field_canonical accumulator.step0)
  have stateOne : GeneratedCanonicalQM31 accumulator.state1.2.2.2.1 := by
    rw [accumulator.step0.nextExact]
    exact afterZero
  have afterOne :=
    V7CallerCurrentReleaseR30CircleArithmeticCanonical.AcceptedCircleStep.running_after_canonical
      accumulator.step1 stateOne
      (V7CallerCurrentReleaseR30CircleArithmeticCanonical.AcceptedCircleStep.fixed_field_canonical accumulator.step1)
  have incoming : GeneratedCanonicalQM31 accumulator.origin.state.2.2.2.1 := by
    rw [accumulator.originStateExact, accumulator.step1.nextExact]
    exact afterOne
  have allRows := fixed_reader_relation_fields_canonical
    _ dispatch.fieldsAfterRelation dispatch.relationFields dispatch.relationFieldsRun
  have rowCanonical := row_canonical_is_relation_canonical dispatch.firstEncoded
    (decoded_index_row_canonical dispatch.relationFields dispatch.firstEncoded 0#usize
      (by norm_num) allRows dispatch.firstEncodedRun)
  have polynomialCanonical := (decode_compact_relation_polynomial_exact
    dispatch.firstEncoded _ dispatch.firstPolynomial rowCanonical incoming dispatch.firstPolynomialRun).1
  exact (generated_evaluate_success_exact dispatch.firstPolynomial dispatch.initialFold.alpha
    dispatch.runningClaim polynomialCanonical dispatch.initialFold.alpha_canonical
    dispatch.firstEvaluateRun).1

theorem accepted_current_fold_tail_running_canonical
    {hash : HashFn} {wire : Wire}
    {context : v6_transcript.V6TranscriptContext}
    {hidingContext : HidingContext}
    {inactiveRowGroups : Array Std.U8 64#usize}
    {inactiveGroupMasks : Slice Std.U16} {checkPow : Bool}
    {statement : Statement}
    {transcript : AspisV7ProductionSnapshotObserverR28SourceBridge.Transcript}
    {snapshot : AspisV7ProductionSnapshotObserverR28SourceBridge.Snapshot}
    {inner : AcceptedInnerDispatch terminalInst queryFoldInst prechallengeInst
      hash wire context hidingContext inactiveRowGroups inactiveGroupMasks
      checkPow statement (hash, wire) () true transcript (some snapshot)}
    {chain : AcceptedInnerPrechallengeChain inner}
    {prepared : AcceptedPreparedAccumulator chain.outer}
    {accumulator : AcceptedCircleAccumulator prepared}
    {dispatch : AcceptedInitialPrechallengeDispatch accumulator.origin}
    (current : AcceptedCurrentFoldTail dispatch) :
    GeneratedCanonicalQM31 current.tail.runningClaimAfter := by
  have rhoCanonical := accepted_current_fold_tail_query_batch_challenge_canonical current
  have valuesCanonical := accepted_current_fold_tail_values_canonical current
  have beforeCanonical := accepted_current_fold_tail_before_query_canonical current
  let insertion := current.tail.insertion
  have scalesCanonical := (successful_scale_loop_has_exact_shifted_powers
    current.tail.queryBatchChallenge (generatedQm31ToExact current.tail.queryBatchChallenge)
    insertion.preparedRho insertion.seed insertion.scales rhoCanonical rfl
    insertion.seedSuccess insertion.preparedRhoSuccess insertion.scalesLoopSuccess).1
  have valuesAll : ∀ index, index < 16 →
      GeneratedCanonicalQM31 current.tail.authenticatedQueries.values.val[index]! := by
    intro index bound
    exact valuesCanonical index (by simpa [Array.to_slice, Array.length_eq] using bound)
  obtain ⟨increment, incrementRun, incrementCanonical, _⟩ :=
    generated_qm31_dot_sixteen_corresponds insertion.scales.to_slice
      current.tail.authenticatedQueries.values.to_slice
      (by simp [Array.to_slice]) (by simp [Array.to_slice]) scalesCanonical (by
        intro index bound
        have inBounds : index < current.tail.authenticatedQueries.values.val.length := by
          simpa [Array.length_eq] using bound
        have canonical := valuesAll index bound
        rw [← List.Inhabited_getElem_eq_getElem! _ index inBounds] at canonical
        simp only [Array.to_slice, List.getElem!_eq_getElem?_getD,
          List.getElem?_eq_getElem inBounds, Option.getD_some]
        exact canonical)
  have incrementExact : current.tail.claimIncrement = increment :=
    Result.ok.inj (insertion.claimDotSuccess.symm.trans incrementRun)
  have actualIncrementCanonical : GeneratedCanonicalQM31 current.tail.claimIncrement := by
    rw [incrementExact]
    exact incrementCanonical
  obtain ⟨expected, expectedRun, expectedCanonical, _⟩ :=
    generated_qm31_add_corresponds dispatch.runningClaim current.tail.claimIncrement
      beforeCanonical actualIncrementCanonical
  have resultExact : current.tail.runningClaimAfter = expected :=
    Result.ok.inj (insertion.runningClaimSuccess.symm.trans expectedRun)
  rw [resultExact]
  exact expectedCanonical

#print axioms accepted_current_fold_tail_values_canonical
#print axioms accepted_current_fold_tail_before_query_canonical
#print axioms accepted_current_fold_tail_running_canonical
end AspisV7ProductionSnapshotObserverR30RunningCanonical
