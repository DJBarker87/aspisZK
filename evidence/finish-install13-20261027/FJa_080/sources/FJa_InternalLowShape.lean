import FJa_InclusiveShape
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
  simp [core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.fold,
    rangeFold.eq_def,Aeneas.Std.core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next,
    Aeneas.Std.core.ops.range.RangeInclusive.is_empty,
    core.iter.range.StepUsize,core.iter.range.UScalarStep,core.iter.range.UScalarStep.forward_checked,
    core.cmp.PartialOrdUsize,liftFun2,core.cmp.impls.PartialOrdUsize.lt,
    core.cmp.impls.PartialOrdUsize.le,
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.fold,
    FJa_LocalWeightFold.Callback,
    state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_1.Insts.CoreOpsFunctionFnMutPairQM31UsizeQM31,
    state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure.Insts.CoreOpsFunctionFnMutPairQM31UsizeQM31,
    FJa_LocalWeightStep.internal]
#print axioms value
end AspisR1.FJa_InternalLowShape
end
