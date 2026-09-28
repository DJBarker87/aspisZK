import V7CallerCurrentReleaseR26QueryBatchAppend
import V7CallerCurrentReleaseR26QueryScaleExactLoop
import V7CallerCurrentReleaseR26QueryWeightSemantics

/-!
# Exact current R26 inserted query weights

This file joins the three source-authentic facts carried by one accepted
query insertion: the shifted rho-power loop, the literal appended line-batch
component, and the generated component evaluator.  The authenticated line
coordinates remain an explicit source-binding premise.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26QueryWeightInsertionSemantics

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26LineBatchLoop
open V7CallerCurrentReleaseR26QueryBatchAppend
open V7CallerCurrentReleaseR26QueryScaleExactStep
open V7CallerCurrentReleaseR26QueryScaleExactLoop
open V7CallerCurrentReleaseR26QueryWeightSemantics

abbrev RawQM31 := field.QM31
abbrev RawWeights := sumcheck.WeightAccumulator
abbrev ExactM31 := V7CallerCurrentReleaseR26FieldBridge.ExactM31
abbrev ExactQM31 := V7CallerCurrentReleaseR26FieldBridge.ExactQM31

/-- An accepted production insertion appends a component whose public
pointwise evaluator is exactly the shifted sixteen-query natural-line
covector. -/
theorem accepted_insertion_appends_exact_query_weight
    (weights : RawWeights) (runningClaim : RawQM31)
    (queries : Array Std.U32 16#usize)
    (authenticated : v6_query_batch.V6AuthenticatedQueryBatch)
    (rho claimIncrement : RawQM31)
    (weightsAfter : RawWeights) (runningClaimAfter : RawQM31)
    (rhoExact : ExactQM31) (lineX : Nat → ExactM31)
    (rhoCanonical : GeneratedCanonicalQM31 rho)
    (rhoExactEq : generatedQm31ToExact rho = rhoExact)
    (logLenExact : weights.log_len.val = 18)
    (lineXCanonical : ∀ ordinal, ordinal < 16 →
      GeneratedCanonicalM31 authenticated.line_x.val[ordinal]!)
    (lineXExact : ∀ ordinal, ordinal < 16 →
      generatedM31ToExact authenticated.line_x.val[ordinal]! = lineX ordinal)
    (capacity : weights.components.val.length < Std.Usize.max)
    (trace :
      V7CallerCurrentReleaseR26QueryBatchInsertion.AcceptedQueryBatchInsertionTrace
        weights runningClaim queries authenticated rho claimIncrement
        weightsAfter runningClaimAfter) :
    ∃ scalesVec : alloc.vec.Vec RawQM31,
      ∃ lineVec : alloc.vec.Vec field.M31,
        weightsAfter.log_len = weights.log_len ∧
        weightsAfter.components.val = weights.components.val ++
          [sumcheck.WeightComponent.LineM31Batch scalesVec lineVec 0#u8] ∧
        ∀ index : Std.U32, index.val < 256 →
          sumcheck.WeightAccumulator.impl.weight_component_at_indexed
              weightsAfter.log_len
              (sumcheck.WeightComponent.LineM31Batch
                scalesVec lineVec 0#u8) index
            ⦃ out => GeneratedCanonicalQM31 out ∧
              generatedQm31ToExact out =
                exactShiftedLineBatchWeight rhoExact lineX index.val ⦄ := by
  have scalePrefix : ShiftedScalePrefix rhoExact trace.scales 16#usize :=
    successful_scale_loop_has_exact_shifted_powers rho rhoExact
      trace.preparedRho trace.seed trace.scales rhoCanonical rhoExactEq
      trace.seedSuccess trace.preparedRhoSuccess trace.scalesLoopSuccess
  obtain ⟨scalesVec, lineVec, scalesVal, lineVal, sameLogLen, appendExact⟩ :=
    accepted_insertion_has_exact_append weights runningClaim queries
      authenticated rho claimIncrement weightsAfter runningClaimAfter capacity
      trace
  refine ⟨scalesVec, lineVec, sameLogLen, appendExact, ?_⟩
  intro index coefficientBound
  have scaleSliceEq : alloc.vec.Vec.deref scalesVec =
      Array.to_slice trace.scales := by
    apply Subtype.ext
    exact scalesVal
  have lineSliceEq : alloc.vec.Vec.deref lineVec =
      Array.to_slice authenticated.line_x := by
    apply Subtype.ext
    exact lineVal
  have evaluator := generated_line_batch_zero_deferred_corresponds
    weightsAfter.log_len (alloc.vec.Vec.deref scalesVec)
      (alloc.vec.Vec.deref lineVec) index (by
        rw [sameLogLen, logLenExact]
        omega) (by
        rw [scaleSliceEq, lineSliceEq]
        simp [Array.to_slice]) (by
        rw [scaleSliceEq]
        intro ordinal ordinalBound
        exact scalePrefix.1 ordinal (by simpa [Array.to_slice] using ordinalBound))
      (by
        rw [lineSliceEq]
        intro ordinal ordinalBound
        exact lineXCanonical ordinal (by simpa [Array.to_slice] using ordinalBound))
  obtain ⟨out, outRun, outCanonical, outExact⟩ :=
    Aeneas.Std.WP.spec_imp_exists evaluator
  change
    sumcheck.WeightAccumulator.impl.weight_at_line_batch_indexed
        weightsAfter.log_len (alloc.vec.Vec.deref scalesVec)
          (alloc.vec.Vec.deref lineVec) 0#u8 index
      ⦃ out => GeneratedCanonicalQM31 out ∧
        generatedQm31ToExact out =
          exactShiftedLineBatchWeight rhoExact lineX index.val ⦄
  rw [outRun]
  simp only [Aeneas.Std.WP.spec_ok]
  refine ⟨outCanonical, outExact.trans ?_⟩
  apply lineBatchPrefix_eq_exactShiftedLineBatchWeight
  · rw [sameLogLen]
    exact logLenExact
  · rw [scaleSliceEq]
    simp [Array.to_slice]
  · intro ordinal ordinalBound
    rw [scaleSliceEq]
    exact scalePrefix.2.2.2 ordinal (by simpa using ordinalBound)
  · intro ordinal ordinalBound
    rw [lineSliceEq]
    exact lineXExact ordinal ordinalBound
  · exact coefficientBound

#print axioms accepted_insertion_appends_exact_query_weight

end V7CallerCurrentReleaseR26QueryWeightInsertionSemantics
