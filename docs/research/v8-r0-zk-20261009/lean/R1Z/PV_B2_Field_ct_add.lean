import R1Z.PV_B2_W_03_ct_add
import R1Z.PV_B2_Field_ct_reduce64
open Aeneas Aeneas.Std Result
namespace PV_B2_Field
/-- Exact complete-Result arithmetic comparison on arbitrary raw limbs. -/
theorem ct_add : PV_B2_WeightsNative.aspis_core.field.ct.add = R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.ct.add := by
  unfold PV_B2_WeightsNative.aspis_core.field.ct.add R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.ct.add
  simp only [PV_B2_Field.P, PV_B2_Field.ct_subtract_p, PV_B2_Field.ct_reduce64]
#print axioms ct_add
end PV_B2_Field
