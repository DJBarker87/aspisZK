import R1Z.PV_Op223_Extract_00_P
import R1Z.PV_Op223_FieldBridge_QM31_mul_m31
open Aeneas Aeneas.Std Result
namespace R1Z.PV_Op223_Agreement
theorem P : PV_Op223_Applied.aspis_core.field.P = PV_Ext_IndexClosed.aspis_core.field.P := by
  unfold PV_Op223_Applied.aspis_core.field.P PV_Ext_IndexClosed.aspis_core.field.P
  rfl
#print axioms P
end R1Z.PV_Op223_Agreement
