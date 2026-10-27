import R1Z.PV_B2_W_04_ct_sub
import R1Z.PV_B2_Field_ct_add
open Aeneas Aeneas.Std Result
namespace PV_B2_Field
/-- Exact complete-Result arithmetic comparison on arbitrary raw limbs. -/
theorem ct_sub : PV_B2_WeightsNative.aspis_core.field.ct.sub = R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.ct.sub := by
  unfold PV_B2_WeightsNative.aspis_core.field.ct.sub R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.ct.sub
  simp only [PV_B2_Field.P, PV_B2_Field.ct_subtract_p, PV_B2_Field.ct_reduce64, PV_B2_Field.ct_add]
#print axioms ct_sub
end PV_B2_Field
