import R1Z.PV_B2_Total_QM31_mul
import R1Z.PV_B2_W_22_host_weights_Weights_new
import R1Z.PV_B2_ArrayTotal
set_option autoImplicit false
noncomputable section
namespace PV_B2_WeightsTotal
open Aeneas Aeneas.Std Result PV_B2_ArrayTotal
abbrev K := ProverRwFull.aspis_core.field.QM31

theorem double (x : K) : Total (PV_B2_WeightsNative.host_weights.double x) := by
  simp only [PV_B2_WeightsNative.host_weights.double,
    PV_B2_FieldTotal.QM31_mul,PV_B2_FieldTotal.QM31_add,PV_B2_FieldTotal.QM31_sub,
    bind_tc_ok]
  exact ⟨_,rfl⟩

/-- Every raw ten-element alpha array yields the copied three statement points.
This is source totality; it does not assert field validity of malformed limbs. -/
theorem points (alpha : Array K 10#usize) :
    Total (PV_B2_WeightsNative.host_weights.state_only_statement_points alpha) := by
  simp only [PV_B2_WeightsNative.host_weights.state_only_statement_points,
    PV_B2_FieldTotal.QM31_mul,PV_B2_FieldTotal.QM31_add,PV_B2_FieldTotal.QM31_sub,
    bind_tc_ok]
  repeat' first
    | exact ⟨_,rfl⟩
    | exact read _ _ (by decide)
    | exact write _ _ _ (by decide)
    | apply PV_B2_ArrayTotal.bind
    | (intro x; cases x)
#print axioms double
#print axioms points
end PV_B2_WeightsTotal
