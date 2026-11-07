import NMS_GetterSuccess
import NMS_R2N_RSLPoolCarriers
set_option autoImplicit false
noncomputable section
namespace NMS_R2N_RSLGetterLink
open Aeneas Aeneas.Std AdapterRw
/-- The SAME successful fresh getter gives the canonical byte carrier of the
original stored Vec. All other clone outcomes remain unassumed. -/
theorem original (ops : Ops) (account : r1_pool_adapter.owned.OwnedAccount)
 (bytes : Slice U8) (read : NMS_Emitted.get ops account = .ok (.Ok bytes)) :
 (NMS_R2N_RSLPoolCarriers.account account).bytes = .ok (NMS_R2N_RSLScalars.bytes bytes) := by
 obtain ⟨stored,source,same⟩ := NMS_GetterSuccess.stored ops account bytes read
 unfold NMS_R2N_RSLPoolCarriers.account
 simp only [source,NMS_R2N_RSLError.reply]
 rw [same]
 rfl

#print axioms original
end NMS_R2N_RSLGetterLink
