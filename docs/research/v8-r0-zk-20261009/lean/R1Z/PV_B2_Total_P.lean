import R1Z.PV_B2_W_00_P
import R1Z.PV_B2_WeightsNativeTypes
open Aeneas Aeneas.Std Result
namespace PV_B2_FieldValue
abbrev aspis_core.field.M31 := ProverRwFull.aspis_core.field.M31
abbrev aspis_core.field.CM31 := ProverRwFull.aspis_core.field.CM31
abbrev aspis_core.field.QM31 := ProverRwFull.aspis_core.field.QM31
def aspis_core.field.P : Std.U32 := 2147483647#u32
end PV_B2_FieldValue
namespace PV_B2_FieldTotal
/-- Full Result, arbitrary raw inputs; shared symbolic operations avoid field-term reduction. -/
theorem P : PV_B2_WeightsNative.aspis_core.field.P = PV_B2_FieldValue.aspis_core.field.P := by
  unfold PV_B2_WeightsNative.aspis_core.field.P PV_B2_FieldValue.aspis_core.field.P
  rfl
#print axioms P
end PV_B2_FieldTotal
