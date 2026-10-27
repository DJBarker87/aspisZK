import R1Z.PV_B2_W_17_QM31_add
import R1Z.PV_B2_Field_QM31_ONE
open Aeneas Aeneas.Std Result
namespace PV_B2_Field
/-- Exact complete-Result arithmetic comparison on arbitrary raw limbs. -/
theorem QM31_add : PV_B2_WeightsNative.aspis_core.field.QM31.add = R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.QM31.add := by
  unfold PV_B2_WeightsNative.aspis_core.field.QM31.add R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.QM31.add
  simp only [PV_B2_Field.P, PV_B2_Field.ct_subtract_p, PV_B2_Field.ct_reduce64, PV_B2_Field.ct_add, PV_B2_Field.ct_sub, PV_B2_Field.reduce_u64, PV_B2_Field.M31_mul, PV_B2_Field.M31_reduce_u64, PV_B2_Field.M31_add, PV_B2_Field.M31_double, PV_B2_Field.CM31_add, PV_B2_Field.M31_sub, PV_B2_Field.CM31_sub, PV_B2_Field.CM31_mul, PV_B2_Field.mul_by_r, PV_B2_Field.QM31_ZERO, PV_B2_Field.QM31_ONE]
#print axioms QM31_add
end PV_B2_Field
