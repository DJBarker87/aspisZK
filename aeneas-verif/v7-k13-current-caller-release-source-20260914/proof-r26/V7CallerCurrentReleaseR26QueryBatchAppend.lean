import V7CallerCurrentReleaseR26QueryBatchInsertion
import V7CallerCurrentReleaseR26FieldBridge

/-!
# Exact current R26 query-batch accumulator append

A successful shifted query insertion copies the two fixed sixteen-entry
arrays into vectors and appends exactly one `LineM31Batch` component.  This
small source-shape theorem is the boundary used by the later pointwise
`weight_at` refinement; it does not unfold the accumulator evaluator.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26QueryBatchAppend

open V7CallerCurrentReleaseR26FieldBridge

abbrev RawQM31 := field.QM31
abbrev RawWeights := sumcheck.WeightAccumulator
abbrev RawComponent := sumcheck.WeightComponent

/-- Successful insertion preserves the accumulator domain and appends the
literal copied scale/line component, with no other component change. -/
theorem successful_line_batch_append_exact
    (weights weightsAfter : RawWeights)
    (scales : Array RawQM31 16#usize)
    (lineX : Array field.M31 16#usize)
    (capacity : weights.components.val.length < Std.Usize.max)
    (run :
      sumcheck.WeightAccumulator.impl.add_line_m31_batch weights
          (Array.to_slice scales) (Array.to_slice lineX) =
        ok (core.result.Result.Ok (), weightsAfter)) :
    ∃ scalesVec : alloc.vec.Vec RawQM31,
      ∃ lineVec : alloc.vec.Vec field.M31,
        scalesVec.val = scales.val ∧
        lineVec.val = lineX.val ∧
        weightsAfter.log_len = weights.log_len ∧
        weightsAfter.components.val = weights.components.val ++
          [sumcheck.WeightComponent.LineM31Batch scalesVec lineVec 0#u8] := by
  obtain ⟨scalesVec, scalesRun, scalesExact⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (alloc.slice.Slice.to_vec_spec field.QM31.Insts.CoreCloneClone
        (Array.to_slice scales) (by
          intro value _
          simp [field.QM31.Insts.CoreCloneClone.clone]))
  obtain ⟨lineVec, lineRun, lineExact⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (alloc.slice.Slice.to_vec_spec field.M31.Insts.CoreCloneClone
        (Array.to_slice lineX) (by
          intro value _
          simp [field.M31.Insts.CoreCloneClone.clone]))
  let component : RawComponent :=
    .LineM31Batch scalesVec lineVec 0#u8
  obtain ⟨componentsAfter, pushRun, componentsExact⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (alloc.vec.Vec.push_spec weights.components component capacity)
  have nonempty :
      core.slice.Slice.is_empty (Array.to_slice scales) = ok false := by
    simp [core.slice.Slice.is_empty, Array.to_slice]
  have sameLength :
      (Slice.len (Array.to_slice scales) !=
        Slice.len (Array.to_slice lineX)) = false := by
    simp [Slice.len, Array.to_slice]
  unfold sumcheck.WeightAccumulator.impl.add_line_m31_batch at run
  by_cases emptyLog : weights.log_len = 0#u32
  · simp [emptyLog] at run
  · rw [if_neg emptyLog] at run
    rw [nonempty] at run
    simp only [bind_tc_ok, Bool.false_eq_true, ↓reduceIte] at run
    rw [sameLength] at run
    simp only [Bool.false_eq_true, ↓reduceIte] at run
    rw [scalesRun] at run
    simp only [bind_tc_ok]
      at run
    rw [lineRun] at run
    simp only [bind_tc_ok]
      at run
    rw [pushRun] at run
    simp only [bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at run
    rcases run with ⟨_, rfl⟩
    refine ⟨scalesVec, lineVec, ?_, ?_, rfl, ?_⟩
    · exact congrArg Subtype.val scalesExact.symm
    · exact congrArg Subtype.val lineExact.symm
    · simpa [component] using componentsExact

/-- The exact insertion trace therefore carries the literal append shape
needed by the pointwise query-weight proof. -/
theorem accepted_insertion_has_exact_append
    (weights : RawWeights) (runningClaim : RawQM31)
    (queries : Array Std.U32 16#usize)
    (authenticated : v6_query_batch.V6AuthenticatedQueryBatch)
    (rho claimIncrement : RawQM31)
    (weightsAfter : RawWeights) (runningClaimAfter : RawQM31)
    (capacity : weights.components.val.length < Std.Usize.max)
    (trace :
      V7CallerCurrentReleaseR26QueryBatchInsertion.AcceptedQueryBatchInsertionTrace
        weights runningClaim queries authenticated rho claimIncrement
        weightsAfter runningClaimAfter) :
    ∃ scalesVec : alloc.vec.Vec RawQM31,
      ∃ lineVec : alloc.vec.Vec field.M31,
        scalesVec.val = trace.scales.val ∧
        lineVec.val = authenticated.line_x.val ∧
        weightsAfter.log_len = weights.log_len ∧
        weightsAfter.components.val = weights.components.val ++
          [sumcheck.WeightComponent.LineM31Batch scalesVec lineVec 0#u8] :=
  successful_line_batch_append_exact weights weightsAfter trace.scales
    authenticated.line_x capacity trace.weightsInsertSuccess

/-- The scalar update following the authenticated dot product is the exact
field addition of the incoming claim and that dot product. -/
theorem accepted_insertion_running_claim_exact
    (weights : RawWeights) (runningClaim : RawQM31)
    (queries : Array Std.U32 16#usize)
    (authenticated : v6_query_batch.V6AuthenticatedQueryBatch)
    (rho claimIncrement : RawQM31)
    (weightsAfter : RawWeights) (runningClaimAfter : RawQM31)
    (runningCanonical : GeneratedCanonicalQM31 runningClaim)
    (incrementCanonical : GeneratedCanonicalQM31 claimIncrement)
    (trace :
      V7CallerCurrentReleaseR26QueryBatchInsertion.AcceptedQueryBatchInsertionTrace
        weights runningClaim queries authenticated rho claimIncrement
        weightsAfter runningClaimAfter) :
    GeneratedCanonicalQM31 runningClaimAfter ∧
      generatedQm31ToExact runningClaimAfter =
        generatedQm31ToExact runningClaim +
          generatedQm31ToExact claimIncrement := by
  obtain ⟨out, outRun, outCanonical, outExact⟩ :=
    generated_qm31_add_corresponds runningClaim claimIncrement
      runningCanonical incrementCanonical
  have outputEq : runningClaimAfter = out :=
    Result.ok.inj (trace.runningClaimSuccess.symm.trans outRun)
  subst out
  exact ⟨outCanonical, outExact⟩

end V7CallerCurrentReleaseR26QueryBatchAppend
