import RPu_FJa_InclusiveFoldStep
import RPu_FJa_LocalWeightFold
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_InternalLowShape
open Aeneas Aeneas.Std Result FIq_Native
open FJa_PoseidonOrigins (Selectors internalFold)
/-- Seven-visit control-flow shape only; field operations remain symbolic
callbacks. No packed recurrence or field numeral is evaluated. -/
theorem value (s : Selectors) : internalFold s=
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.fold
      (N:=7#usize) FJa_LocalWeightFold.Callback
      [2#usize,3#usize,4#usize,5#usize,6#usize,7#usize,8#usize] field.QM31.ZERO s := by
  unfold internalFold
  simp only [Aeneas.Std.core.ops.range.RangeInclusive.new,bind_tc_ok]
  unfold core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.fold
  have ceq : state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_1.Insts.CoreOpsFunctionFnMutPairQM31UsizeQM31=FJa_LocalWeightFold.Callback := rfl
  rw [ceq]
  simp only [
    FJa_InclusiveFoldStep.step _ _ _ _ FJa_InclusiveSteps.step2,
    FJa_InclusiveFoldStep.step _ _ _ _ FJa_InclusiveSteps.step3,
    FJa_InclusiveFoldStep.step _ _ _ _ FJa_InclusiveSteps.step4,
    FJa_InclusiveFoldStep.step _ _ _ _ FJa_InclusiveSteps.step5,
    FJa_InclusiveFoldStep.step _ _ _ _ FJa_InclusiveSteps.step6,
    FJa_InclusiveFoldStep.step _ _ _ _ FJa_InclusiveSteps.step7,
    FJa_InclusiveFoldStep.step _ _ _ _ (FJa_InclusiveNext.last 8#usize),
    FJa_InclusiveFoldStep.stop _ _ (FJa_InclusiveNext.stop 8#usize 8#usize),
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.fold]

#print axioms value
end AspisR1.FJa_InternalLowShape
end
