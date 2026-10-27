import FJa_InclusiveSteps
import FJa_LocalWeightFold
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
  have n2 := FJa_InclusiveSteps.step2
  have n3 := FJa_InclusiveSteps.step3
  have n4 := FJa_InclusiveSteps.step4
  have n5 := FJa_InclusiveSteps.step5
  have n6 := FJa_InclusiveSteps.step6
  have n7 := FJa_InclusiveSteps.step7
  have n8 := FJa_InclusiveNext.last 8#usize
  have stop := FJa_InclusiveNext.stop 8#usize 8#usize
  unfold FJa_InclusiveNext.next at n2 n3 n4 n5 n6 n7 n8 stop
  simp only [core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.fold,
    rangeFold.eq_def,n2,n3,n4,n5,n6,n7,n8,stop,bind_tc_ok,
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.fold,
    FJa_LocalWeightFold.Callback,
    state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_1.Insts.CoreOpsFunctionFnMutPairQM31UsizeQM31,
    state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure.Insts.CoreOpsFunctionFnMutPairQM31UsizeQM31,
    FJa_LocalWeightStep.internal,
    state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure.Insts.CoreOpsFunctionFnMutPairQM31UsizeQM31.call_mut,
    bind_assoc_eq]

#print axioms value
end AspisR1.FJa_InternalLowShape
end
