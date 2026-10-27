import R1Z.PV_B2_W_01_ct_subtract_p
import R1Z.PV_B2_Field_P
open Aeneas Aeneas.Std Result
namespace PV_B2_Field
/-- Exact complete-Result arithmetic comparison on arbitrary raw limbs. -/
theorem ct_subtract_p : PV_B2_WeightsNative.aspis_core.field.ct.subtract_p = R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.ct.subtract_p := by
  unfold PV_B2_WeightsNative.aspis_core.field.ct.subtract_p R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.ct.subtract_p
  simp only [PV_B2_Field.P]
#print axioms ct_subtract_p
end PV_B2_Field
