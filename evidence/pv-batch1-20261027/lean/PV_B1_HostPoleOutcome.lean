import PV_B1_Install
import PV_B1_PoleOutcome
set_option autoImplicit false
noncomputable section
namespace PV_B1_HostPoleOutcome
open Aeneas Aeneas.Std Result PV_B1_Transport
open PV_B1_Host PV_B1_Install
variable [ExternalTypes]
theorem length (v : Rows) : (rows v).val.length=v.val.length := by
  simp only [rows,sliceMap,List.length_map]
theorem total (ops : ExternalFuns) (v : Rows) (m : Array U16 64#usize) (c : HQ)
    (h : v.val.length≤1024) : ∃ b, (selected ops).op258 v m c=ok b := by
  exact PV_B1_PoleOutcome.total (rows v) m (PV_B1_Carrier258.toQ c) (by rw [length]; exact h)
theorem failure_iff (ops : ExternalFuns) (v : Rows) (m : Array U16 64#usize) (c : HQ) :
    (selected ops).op258 v m c=fail .arrayOutOfBounds ↔ 1024<v.val.length := by
  change PV_B1_258.all_slots_clear _ _ _=fail _ ↔ _
  rw [PV_B1_PoleOutcome.failure_iff,length]
#print axioms length
#print axioms total
#print axioms failure_iff
end PV_B1_HostPoleOutcome
