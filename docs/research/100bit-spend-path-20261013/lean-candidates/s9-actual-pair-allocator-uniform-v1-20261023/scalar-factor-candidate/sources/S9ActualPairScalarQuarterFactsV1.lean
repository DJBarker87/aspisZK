import S9ActualPairHelperScalarDispatchV1
import S9ActualPairMulM31HelperTransportV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
open AspisR1S9ActualPairScalarCallbackV1 AspisR1S9ActualPairScalarFoldV1
namespace AspisR1S9ActualPairScalarQuarterFactsV1
local instance helperOps : AspisR1S9HelperP6.FieldOps := AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
abbrev HW := AspisR1S9HelperP6.field.WideExact
abbrev HQ := AspisR1S9HelperP6.field.QM31

theorem mapped_zero_eq_helper : toHelperW aspis_core.field.wide_exact.WideExact.ZERO =
    AspisR1S9HelperP6.field.WideExact.ZERO := by
  unfold aspis_core.field.wide_exact.WideExact.ZERO aspis_core.field.QM31.ZERO
    AspisR1S9HelperP6.field.WideExact.ZERO AspisR1S9HelperP6.field.QM31.ZERO
  rfl

theorem source_quarter_success_maps (acc out : W)
    (h : aspis_core.field.wide_exact.WideExact.mul_m31 acc weights.QUARTER = .ok out) :
    @AspisR1S9HelperP6.FieldOps.wideMulM31 AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      (toHelperW acc) AspisR1S9HelperP6.weights.QUARTER = .ok (toHelperW out) := by
  have hm := AspisR1S9ActualPairMulM31HelperTransportV1.actual_pair_wide_mul_m31_to_installed_helper
    acc weights.QUARTER
  rw [h] at hm
  have hquarter : weights.QUARTER = AspisR1S9HelperP6.weights.QUARTER := by
    unfold weights.QUARTER AspisR1S9HelperP6.weights.QUARTER
    rfl
  rw [←hquarter]
  exact hm.symm

#print axioms mapped_zero_eq_helper
#print axioms source_quarter_success_maps
end AspisR1S9ActualPairScalarQuarterFactsV1
