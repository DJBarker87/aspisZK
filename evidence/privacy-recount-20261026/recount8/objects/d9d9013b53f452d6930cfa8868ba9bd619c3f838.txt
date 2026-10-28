import R1Z.PV_Ext_Closed_05_M31_ZERO
import R1Z.PV_Ext_FieldBridge_ct_sub
open Aeneas Aeneas.Std Result
namespace R1Z.PV_Ext_FieldBridge
/-- Exact complete-Result comparison of the freshly extracted candidate leaf
    field dependency with the retained current source, on arbitrary raw limbs. -/
theorem M31_ZERO : PV_Ext_IndexClosed.aspis_core.field.M31.ZERO = (0#u32 : Aeneas.Std.U32) := by
  unfold PV_Ext_IndexClosed.aspis_core.field.M31.ZERO
  rfl
#print axioms M31_ZERO
end R1Z.PV_Ext_FieldBridge
