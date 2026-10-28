import R1Z.PV_Ext_Closed_11_CM31_ZERO
import R1Z.PV_Ext_FieldBridge_M31_double
open Aeneas Aeneas.Std Result
namespace R1Z.PV_Ext_FieldBridge
/-- Exact complete-Result comparison of the freshly extracted candidate leaf
    field dependency with the retained current source, on arbitrary raw limbs. -/
theorem CM31_ZERO : PV_Ext_IndexClosed.aspis_core.field.CM31.ZERO = (⟨0#u32,0#u32⟩ : ProverRwFull.aspis_core.field.CM31) := by
  unfold PV_Ext_IndexClosed.aspis_core.field.CM31.ZERO
  rfl
#print axioms CM31_ZERO
end R1Z.PV_Ext_FieldBridge
