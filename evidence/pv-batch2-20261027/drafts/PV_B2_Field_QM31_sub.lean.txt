import R1Z.PV_B2_W_18_QM31_sub
import R1Z.PV_B2_Field_QM31_add
open Aeneas Aeneas.Std Result
namespace PV_B2_Field
/-- Exact complete-Result arithmetic comparison on arbitrary raw limbs. -/
theorem QM31_sub : PV_B2_WeightsNative.aspis_core.field.QM31.sub = (fun (a b : ProverRwFull.aspis_core.field.QM31) => do
  let c0 ← R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.CM31.sub a.c0 b.c0
  let c1 ← R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.CM31.sub a.c1 b.c1
  Aeneas.Std.Result.ok ({c0,c1} : ProverRwFull.aspis_core.field.QM31)) := by
  unfold PV_B2_WeightsNative.aspis_core.field.QM31.sub
  simp only [PV_B2_Field.P, PV_B2_Field.ct_subtract_p, PV_B2_Field.ct_reduce64, PV_B2_Field.ct_add, PV_B2_Field.ct_sub, PV_B2_Field.reduce_u64, PV_B2_Field.M31_mul, PV_B2_Field.M31_reduce_u64, PV_B2_Field.M31_add, PV_B2_Field.M31_double, PV_B2_Field.CM31_add, PV_B2_Field.M31_sub, PV_B2_Field.CM31_sub, PV_B2_Field.CM31_mul, PV_B2_Field.mul_by_r, PV_B2_Field.QM31_ZERO, PV_B2_Field.QM31_ONE, PV_B2_Field.QM31_add]
#print axioms QM31_sub
end PV_B2_Field
