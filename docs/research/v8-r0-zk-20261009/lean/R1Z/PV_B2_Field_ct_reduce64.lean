import R1Z.PV_B2_W_02_ct_reduce64
import R1Z.PV_B2_Field_ct_subtract_p
open Aeneas Aeneas.Std Result
namespace PV_B2_Field
/-- Exact complete-Result arithmetic comparison on arbitrary raw limbs. -/
theorem ct_reduce64 : PV_B2_WeightsNative.aspis_core.field.ct.reduce64 = R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.ct.reduce64 := by
  unfold PV_B2_WeightsNative.aspis_core.field.ct.reduce64 R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.ct.reduce64
  simp only [PV_B2_Field.P, PV_B2_Field.ct_subtract_p]
#print axioms ct_reduce64
end PV_B2_Field
