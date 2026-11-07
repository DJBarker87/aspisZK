import NMS_EmittedLinks
import AdapterRwCuts
set_option autoImplicit false
noncomputable section
namespace NMS_GetterSuccess
open Aeneas Aeneas.Std AdapterRw
/-- Success comes only from the ORIGINAL Vec payload. This holds for the
entire ProgramError type and arbitrary partial clone replies; no snapshot-only
error restriction, buffer-size bound, or allocation-success premise is used. -/
theorem stored (ops : Ops) (account : r1_pool_adapter.owned.OwnedAccount) (bytes : Slice U8)
 (returned : NMS_Emitted.get ops account = .ok (.Ok bytes)) :
 ∃ original, account.bytes = .Ok original ∧ bytes = original.deref := by
 cases h : account.bytes with
 | Ok original =>
  simp only [NMS_Emitted.get,h] at returned
  cases returned
  exact ⟨original,rfl,rfl⟩
 | Err error =>
  simp only [NMS_Emitted.get,h] at returned
  exact False.elim (AspisR1.AdapterRw.Cuts.error_bind_ne_ok (ops.op35 error) bytes returned)
#print axioms stored
end NMS_GetterSuccess
