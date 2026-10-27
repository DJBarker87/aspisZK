import R1Z.PV_B2_W_05_reduce_u64
import R1Z.PV_B2_Field_ct_sub
open Aeneas Aeneas.Std Result
namespace PV_B2_Field
/-- Exact complete-Result arithmetic comparison on arbitrary raw limbs. -/
theorem reduce_u64 : PV_B2_WeightsNative.aspis_core.field.reduce_u64 = R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.reduce_u64 := by
  unfold PV_B2_WeightsNative.aspis_core.field.reduce_u64 R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.reduce_u64
  simp only [PV_B2_Field.P, PV_B2_Field.ct_subtract_p, PV_B2_Field.ct_reduce64, PV_B2_Field.ct_add, PV_B2_Field.ct_sub]
#print axioms reduce_u64
end PV_B2_Field
