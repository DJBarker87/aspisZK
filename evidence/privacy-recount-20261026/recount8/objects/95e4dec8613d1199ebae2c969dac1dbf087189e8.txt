import R1Z.PV_Ext_Closed_19_QM31_from_cm31
import R1Z.PV_Op223_FieldBridge_mul_by_r
open Aeneas Aeneas.Std Result
namespace R1Z.PV_Op223_FieldBridge
/-- Exact complete-Result comparison of the freshly extracted candidate leaf
    field dependency with the retained current source, on arbitrary raw limbs. -/
theorem QM31_from_cm31 : PV_Ext_IndexClosed.aspis_core.field.QM31.from_cm31 = (fun x => Aeneas.Std.Result.ok (⟨x,⟨0#u32,0#u32⟩⟩ : ProverRwFull.aspis_core.field.QM31)) := by
  funext x
  simp only [PV_Ext_IndexClosed.aspis_core.field.QM31.from_cm31, PV_Ext_IndexClosed.aspis_core.field.CM31.ZERO]
#print axioms QM31_from_cm31
end R1Z.PV_Op223_FieldBridge
