import R1Z.PV_B2_W_11_M31_sub
import R1Z.PV_B2_Field_CM31_add
open Aeneas Aeneas.Std Result
namespace PV_B2_Field
/-- Exact complete-Result arithmetic comparison on arbitrary raw limbs. -/
theorem M31_sub : PV_B2_WeightsNative.aspis_core.field.M31.sub = R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.M31.sub := by
  unfold PV_B2_WeightsNative.aspis_core.field.M31.sub R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.M31.sub
  simp only [PV_B2_Field.P, PV_B2_Field.ct_subtract_p, PV_B2_Field.ct_reduce64, PV_B2_Field.ct_add, PV_B2_Field.ct_sub, PV_B2_Field.reduce_u64, PV_B2_Field.M31_mul, PV_B2_Field.M31_reduce_u64, PV_B2_Field.M31_add, PV_B2_Field.M31_double, PV_B2_Field.CM31_add]
#print axioms M31_sub
end PV_B2_Field
