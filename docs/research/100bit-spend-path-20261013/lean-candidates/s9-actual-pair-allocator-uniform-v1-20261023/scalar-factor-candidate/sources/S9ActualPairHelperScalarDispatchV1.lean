import S9ActualPairScalarFoldV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ActualPairScalarCallbackV1 AspisR1S9ActualPairScalarFoldV1
namespace AspisR1S9ActualPairHelperScalarDispatchV1
local instance helperOps : AspisR1S9HelperP6.FieldOps :=
  AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
abbrev HW := AspisR1S9HelperP6.field.WideExact
abbrev HQ := AspisR1S9HelperP6.field.QM31

theorem helper_fold_eq_range_run (range : R) (initial : HW) (closure : HC) :
    @AspisR1S9HelperP6.FieldOps.iterFold AspisR1S9ConcreteFieldOpsV1.concreteFieldOps _ _ _ _
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      helperCallback range initial closure =
      (do
        let (value,_) ← AspisR1S3S9RangeFoldP6.rangeFoldRun
          (range.end.val-range.start.val) range
          (AspisR1S9TransparentFoldRangeLawV1.foldStep helperCallback) (initial,closure)
        ok value) := by
  change AspisR1S9FactoredCut.core.iter.traits.iterator.Iterator.fold.default
    (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
    helperCallback range initial closure = _
  exact AspisR1S9TransparentFoldRangeLawV1.extracted_fold_eq_rangeFoldRun helperCallback range initial closure

theorem helper_scalar_factor_dispatch (f : Array HQ 4#usize) (p : Array HW 4#usize) :
    @AspisR1S9HelperP6.weights.Weights.scalar_factor
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps f p =
      (do
        let value ← @AspisR1S9HelperP6.FieldOps.iterFold
          AspisR1S9ConcreteFieldOpsV1.concreteFieldOps _ _ _ _
          (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
          helperCallback ({start:=0#usize,«end»:=4#usize} : R)
          AspisR1S9HelperP6.field.WideExact.ZERO (p,f)
        @AspisR1S9HelperP6.FieldOps.wideMulM31
          AspisR1S9ConcreteFieldOpsV1.concreteFieldOps value AspisR1S9HelperP6.weights.QUARTER) := rfl

#print axioms helper_fold_eq_range_run
#print axioms helper_scalar_factor_dispatch
end AspisR1S9ActualPairHelperScalarDispatchV1
