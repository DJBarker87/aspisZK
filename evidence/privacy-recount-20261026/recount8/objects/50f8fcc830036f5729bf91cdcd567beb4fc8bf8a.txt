import R1Z.PV_Ext_Closed_12_CM31_from_m31
import R1Z.PV_Ext_FieldBridge_CM31_ZERO
open Aeneas Aeneas.Std Result
namespace R1Z.PV_Ext_FieldBridge
/-- Exact complete-Result comparison of the freshly extracted candidate leaf
    field dependency with the retained current source, on arbitrary raw limbs. -/
theorem CM31_from_m31 : PV_Ext_IndexClosed.aspis_core.field.CM31.from_m31 = (fun x => Aeneas.Std.Result.ok (⟨x,0#u32⟩ : ProverRwFull.aspis_core.field.CM31)) := by
  funext x
  simp only [PV_Ext_IndexClosed.aspis_core.field.CM31.from_m31, PV_Ext_IndexClosed.aspis_core.field.M31.ZERO]
#print axioms CM31_from_m31
end R1Z.PV_Ext_FieldBridge
