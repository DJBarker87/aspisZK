import R1Z.PV_B2_W_08_M31_add
import R1Z.PV_B2_Field_M31_reduce_u64
open Aeneas Aeneas.Std Result
namespace PV_B2_Field
/-- Exact complete-Result arithmetic comparison on arbitrary raw limbs. -/
theorem M31_add : PV_B2_WeightsNative.aspis_core.field.M31.add = R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.M31.add := by
  unfold PV_B2_WeightsNative.aspis_core.field.M31.add R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.M31.add
  simp only [PV_B2_Field.P, PV_B2_Field.ct_subtract_p, PV_B2_Field.ct_reduce64, PV_B2_Field.ct_add, PV_B2_Field.ct_sub, PV_B2_Field.reduce_u64, PV_B2_Field.M31_mul, PV_B2_Field.M31_reduce_u64]
#print axioms M31_add
end PV_B2_Field
