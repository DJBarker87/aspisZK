import R1Z.PV_B2_W_06_M31_mul
import R1Z.PV_B2_Field_reduce_u64
open Aeneas Aeneas.Std Result
namespace PV_B2_Field
/-- Exact complete-Result arithmetic comparison on arbitrary raw limbs. -/
theorem M31_mul : PV_B2_WeightsNative.aspis_core.field.M31.mul = R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.M31.mul := by
  unfold PV_B2_WeightsNative.aspis_core.field.M31.mul R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.M31.mul
  simp only [PV_B2_Field.P, PV_B2_Field.ct_subtract_p, PV_B2_Field.ct_reduce64, PV_B2_Field.ct_add, PV_B2_Field.ct_sub, PV_B2_Field.reduce_u64]
#print axioms M31_mul
end PV_B2_Field
