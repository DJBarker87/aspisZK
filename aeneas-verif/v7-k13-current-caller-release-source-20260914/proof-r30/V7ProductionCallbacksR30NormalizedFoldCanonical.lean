import V7ProductionCallbacksR30PackedGammaCanonical
import V7ProductionCallbacksR30ArrayCanonical

/-! Canonicality of the production normalized arity-four fold polynomial. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
open Aeneas Aeneas.Std Result ControlFlow Error

namespace V7ProductionCallbacksR30NormalizedFoldCanonical
open V7ProductionCallbacksR30MutableCanonical
open V7ProductionCallbacksR30ArrayCanonical
open V7ProductionCallbacksR30KaratsubaCanonical
open V7ProductionCallbacksR30Qm31Canonical
open V7CallerCurrentReleaseR26FieldBridge

local instance : Inhabited CallbackQM31 :=
  ⟨V7ProductionCallbacksR29.aspis_core.field.QM31.ZERO⟩

private theorem bind_eq_ok_iff {Input Output : Type}
    (input : Result Input) (next : Input → Result Output) (output : Output) :
    (do let value ← input; next value) = ok output ↔
      ∃ value, input = ok value ∧ next value = ok output := by
  cases input <;> simp [Bind.bind, Aeneas.Std.bind]

/-- This is a successful-output representation theorem. The dot helper
reduces its channels; no overflow-freedom or polynomial identity is inferred. -/
theorem successful_normalized_candidate_canonical
    (values : Array CallbackQM31 4#usize)
    (powers : Array CallbackPreparedQM31 3#usize)
    (inverses : Array Std.U32 3#usize) (output : CallbackQM31)
    (canonical : SliceAll GeneratedCanonicalQM31 values.to_slice)
    (run : V7ProductionCallbacksR29.aspis_core.circle_fri.normalized_arity4_prepared_polynomial_candidate
      values powers inverses = ok output) : GeneratedCanonicalQM31 output := by
  unfold V7ProductionCallbacksR29.aspis_core.circle_fri.normalized_arity4_prepared_polynomial_candidate at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨q0, q0Run, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨q1, q1Run, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨leftSum, leftSumRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨q2, q2Run, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨q3, q3Run, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨rightSum, rightSumRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨leftDiff, leftDiffRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨inv0, inv0Run, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨leftScaled, leftScaledRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨rightDiff, rightDiffRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨inv1, inv1Run, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨rightScaled, rightScaledRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨sum, sumRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨halfSum, halfSumRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨constantTerm, constantTermRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨scaledSum, scaledSumRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨linear, linearRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨sumDiff, sumDiffRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨halfDiff, halfDiffRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨inv2, inv2Run, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨quadratic, quadraticRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨scaledDiff, scaledDiffRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨cubic, cubicRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨dot, dotRun, run⟩ := run

  have q0Can := array_index_all GeneratedCanonicalQM31 values 0#usize q0 canonical q0Run
  have q1Can := array_index_all GeneratedCanonicalQM31 values 1#usize q1 canonical q1Run
  have q2Can := array_index_all GeneratedCanonicalQM31 values 2#usize q2 canonical q2Run
  have q3Can := array_index_all GeneratedCanonicalQM31 values 3#usize q3 canonical q3Run
  have leftCan := successful_result_property (callback_qm31_add_canonical q0 q1 q0Can q1Can) leftSumRun
  have rightCan := successful_result_property (callback_qm31_add_canonical q2 q3 q2Can q3Can) rightSumRun
  have sumCan := successful_result_property (callback_qm31_add_canonical leftSum rightSum leftCan rightCan) sumRun
  have halfCan := successful_result_property (callback_qm31_half_canonical sum sumCan) halfSumRun
  have constantCan := successful_result_property (callback_qm31_half_canonical halfSum halfCan) constantTermRun
  have dotCan := successful_prepared_sum_products3_canonical powers _ dot dotRun
  exact successful_result_property (callback_qm31_add_canonical constantTerm dot constantCan dotCan) run

theorem successful_normalized_polynomial_refs_canonical
    (values : Array CallbackQM31 4#usize)
    (powers : Array CallbackPreparedQM31 3#usize)
    (inv2x inv2y : Std.U32) (output : CallbackQM31)
    (canonical : SliceAll GeneratedCanonicalQM31 values.to_slice)
    (run : V7ProductionCallbacksR29.aspis_core.circle_fri.normalized_circle_to_line_arity4_prepared_polynomial_refs
      values powers inv2x inv2y = ok output) : GeneratedCanonicalQM31 output := by
  unfold V7ProductionCallbacksR29.aspis_core.circle_fri.normalized_circle_to_line_arity4_prepared_polynomial_refs at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨negativeInv2y, negativeRun, run⟩ := run
  exact successful_normalized_candidate_canonical values powers _ output canonical run

#print axioms successful_normalized_candidate_canonical
#print axioms successful_normalized_polynomial_refs_canonical
end V7ProductionCallbacksR30NormalizedFoldCanonical
