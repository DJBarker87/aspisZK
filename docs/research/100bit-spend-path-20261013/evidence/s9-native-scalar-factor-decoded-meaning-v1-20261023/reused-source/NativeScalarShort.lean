import S9ActualPairSourceScalarTraceV1
import S9ActualPairScalarFoldJoinV1
import S9ActualPairScalarQuarterFactsV1
import S9GenericHelperScalarSuccessV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
open AspisR1S9ActualPairScalarCallbackV1 AspisR1S9ActualPairScalarFoldV1
namespace AspisR1S9ActualPairScalarFactorShortV1
local instance helperOps : AspisR1S9HelperP6.FieldOps := AspisR1S9ConcreteFieldOpsV1.concreteFieldOps

theorem actual_scalar_factor_success_maps (f : Array Q 4#usize) (p : Array W 4#usize)
    (out : W) (hp : GoodArray p)
    (h : weights.Weights.scalar_factor f p = .ok out) :
    Canonical out ∧
      @AspisR1S9HelperP6.weights.Weights.scalar_factor AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (mapArray toHelperQ f) (mapArray toHelperW p) = .ok (toHelperW out) := by
  obtain ⟨acc,hfold,hmul⟩ :=
    AspisR1S9ActualPairSourceScalarTraceV1.source_scalar_success_trace f p out h
  obtain ⟨hacc,hmodelFold⟩ := AspisR1S9ActualPairScalarFoldJoinV1.actual_fold_success_to_helper
    ({start:=0#usize,«end»:=4#usize} : R)
    aspis_core.field.wide_exact.WideExact.ZERO acc (p,f) hp
    AspisR1S9ActualPairWideOutputCanonicalV1.zero_canonical hfold
  have hcan := AspisR1S9ActualPairWideOutputCanonicalV1.mul_m31_success_canonical
    acc out weights.QUARTER hacc hmul
  have hmodelMul := AspisR1S9ActualPairScalarQuarterFactsV1.source_quarter_success_maps acc out hmul
  rw [AspisR1S9ActualPairScalarQuarterFactsV1.mapped_zero_eq_helper] at hmodelFold
  exact ⟨hcan,AspisR1S9GenericHelperScalarSuccessV1.generic_scalar_success_of_calls
    AspisR1S9ConcreteFieldOpsV1.concreteFieldOps (mapArray toHelperQ f) (mapArray toHelperW p)
    (toHelperW acc) (toHelperW out) hmodelFold hmodelMul⟩

#print axioms actual_scalar_factor_success_maps
end AspisR1S9ActualPairScalarFactorShortV1
