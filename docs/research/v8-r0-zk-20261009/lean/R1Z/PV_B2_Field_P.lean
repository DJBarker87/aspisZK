import R1Z.PV_B2_W_00_P
import R1Z.ProverRwP7CurrentFieldSource
open Aeneas Aeneas.Std Result
namespace PV_B2_Field
/-- Exact complete-Result arithmetic comparison on arbitrary raw limbs. -/
theorem P : PV_B2_WeightsNative.aspis_core.field.P = R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.P := by
  unfold PV_B2_WeightsNative.aspis_core.field.P R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.P
  rfl
#print axioms P
end PV_B2_Field
