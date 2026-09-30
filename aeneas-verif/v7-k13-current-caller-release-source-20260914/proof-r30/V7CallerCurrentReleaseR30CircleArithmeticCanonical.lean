import V7CallerCurrentReleaseR30CircleAccumulator
import V7CallerCurrentReleaseR30ChallengeCanonical
import V7CallerCurrentReleaseR30FixedFieldCanonical

/-!
# Canonical arithmetic retained by the production circle accumulator

These lemmas discharge the direct arithmetic facts needed after the exact
two-step circle trace: sampled scales, fixed-field values, products, running
claims, and the source-enforced tensor-factor length.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR30CircleArithmeticCanonical

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26AcceptedCircleOrigin
open V7CallerCurrentReleaseR30ChallengeCanonical
open V7CallerCurrentReleaseR30FixedFieldCanonical
open V7CallerCurrentReleaseR30CircleAccumulator

abbrev RawQM31 := field.QM31
abbrev RawWeights := sumcheck.WeightAccumulator

/-- Successful common tensor insertion enforces exactly `log_len` factors. -/
theorem successful_tensor_factors_length
    (weights output : RawWeights) (scale : RawQM31)
    (factors : alloc.vec.Vec RawQM31)
    (success :
      sumcheck.WeightAccumulator.impl.add_tensor_factors weights scale factors =
        ok (.Ok (), output)) :
    factors.val.length = (UScalar.cast .Usize weights.log_len).val := by
  unfold sumcheck.WeightAccumulator.impl.add_tensor_factors at success
  simp only [Aeneas.Std.lift, bind_tc_ok] at success
  by_cases mismatch :
      alloc.vec.Vec.len factors != UScalar.cast .Usize weights.log_len
  · rw [if_pos mismatch] at success
    simp at success
  · have exactLength :
        alloc.vec.Vec.len factors = UScalar.cast .Usize weights.log_len := by
      simpa only [bne_iff_ne, ne_eq, not_not] using mismatch
    exact congrArg UScalar.val exactLength

theorem AcceptedCircleStep.scale_canonical
    {Fields : Type} {fieldsInst : v6_onefold.V6FixedFieldStream Fields}
    {state next : CircleState Fields}
    {iterNext : core.ops.range.Range Std.I32}
    (step : AcceptedCircleStep fieldsInst state next iterNext) :
    GeneratedCanonicalQM31 step.scale := by
  exact successful_challenge_qm31_canonical step.transcriptAfterAbsorb
    step.transcriptAfterScale step.scale step.scaleRun

theorem AcceptedCircleStep.fixed_field_canonical
    {state next : CircleState v6_onefold.V6FixedFieldReader}
    {iterNext : core.ops.range.Range Std.I32}
    (step : AcceptedCircleStep
      v6_onefold.V6FixedFieldReader.Insts.Aspis_coreV6_onefoldV6FixedFieldStream
      state next iterNext) :
    GeneratedCanonicalQM31 step.fieldValue := by
  exact fixed_reader_next_qm31_canonical state.2.2.1 step.fieldsAfter
    step.fieldValue step.fieldRun

theorem AcceptedCircleStep.product_canonical
    {Fields : Type} {fieldsInst : v6_onefold.V6FixedFieldStream Fields}
    {state next : CircleState Fields}
    {iterNext : core.ops.range.Range Std.I32}
    (step : AcceptedCircleStep fieldsInst state next iterNext)
    (fieldCanonical : GeneratedCanonicalQM31 step.fieldValue) :
    GeneratedCanonicalQM31 step.product := by
  obtain ⟨expected, expectedRun, expectedCanonical, _⟩ :=
    generated_qm31_mul_corresponds step.scale step.fieldValue
      (V7CallerCurrentReleaseR30CircleArithmeticCanonical.AcceptedCircleStep.scale_canonical
        step) fieldCanonical
  have exact : step.product = expected :=
    Result.ok.inj (step.productRun.symm.trans expectedRun)
  rw [exact]
  exact expectedCanonical

theorem AcceptedCircleStep.running_after_canonical
    {Fields : Type} {fieldsInst : v6_onefold.V6FixedFieldStream Fields}
    {state next : CircleState Fields}
    {iterNext : core.ops.range.Range Std.I32}
    (step : AcceptedCircleStep fieldsInst state next iterNext)
    (runningCanonical : GeneratedCanonicalQM31 state.2.2.2.1)
    (fieldCanonical : GeneratedCanonicalQM31 step.fieldValue) :
    GeneratedCanonicalQM31 step.runningAfter := by
  have productCanonical :=
    V7CallerCurrentReleaseR30CircleArithmeticCanonical.AcceptedCircleStep.product_canonical
      step fieldCanonical
  obtain ⟨expected, expectedRun, expectedCanonical, _⟩ :=
    generated_qm31_add_corresponds state.2.2.2.1 step.product
      runningCanonical productCanonical
  have exact : step.runningAfter = expected :=
    Result.ok.inj (step.runningRun.symm.trans expectedRun)
  rw [exact]
  exact expectedCanonical

theorem AcceptedCircleStep.factors_length
    {Fields : Type} {fieldsInst : v6_onefold.V6FixedFieldStream Fields}
    {state next : CircleState Fields}
    {iterNext : core.ops.range.Range Std.I32}
    (step : AcceptedCircleStep fieldsInst state next iterNext) :
    step.factors.val.length =
      (UScalar.cast .Usize state.2.2.2.2.log_len).val := by
  exact successful_tensor_factors_length state.2.2.2.2 step.weightsAfter
    step.scale step.factors step.tensorRun

#print axioms successful_tensor_factors_length
#print axioms AcceptedCircleStep.scale_canonical
#print axioms AcceptedCircleStep.fixed_field_canonical
#print axioms AcceptedCircleStep.product_canonical
#print axioms AcceptedCircleStep.running_after_canonical
#print axioms AcceptedCircleStep.factors_length

end V7CallerCurrentReleaseR30CircleArithmeticCanonical
