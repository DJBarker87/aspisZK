import AspisR1S9HelperP6.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9GenericHelperScalarSuccessV1
abbrev HW := AspisR1S9HelperP6.field.WideExact
abbrev HQ := AspisR1S9HelperP6.field.QM31
abbrev R := core.ops.range.Range Usize

theorem generic_scalar_success_of_calls (ops : AspisR1S9HelperP6.FieldOps)
    (f : Array HQ 4#usize) (p : Array HW 4#usize) (acc out : HW)
    (hfold : @AspisR1S9HelperP6.FieldOps.iterFold ops _ _ _ _
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      (@AspisR1S9HelperP6.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact ops)
      ({start:=0#usize,«end»:=4#usize} : R)
      AspisR1S9HelperP6.field.WideExact.ZERO (p,f) = .ok acc)
    (hmul : @AspisR1S9HelperP6.FieldOps.wideMulM31 ops acc
      AspisR1S9HelperP6.weights.QUARTER = .ok out) :
    @AspisR1S9HelperP6.weights.Weights.scalar_factor ops f p = .ok out := by
  change (do
    let value ← @AspisR1S9HelperP6.FieldOps.iterFold ops _ _ _ _
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      (@AspisR1S9HelperP6.weights.Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact ops)
      ({start:=0#usize,«end»:=4#usize} : R)
      AspisR1S9HelperP6.field.WideExact.ZERO (p,f)
    @AspisR1S9HelperP6.FieldOps.wideMulM31 ops value AspisR1S9HelperP6.weights.QUARTER) = .ok out
  rw [hfold]
  exact hmul
#print axioms generic_scalar_success_of_calls
end AspisR1S9GenericHelperScalarSuccessV1
