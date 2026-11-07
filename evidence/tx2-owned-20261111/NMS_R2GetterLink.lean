import NMS_R2CloneLaw
import NMS_R2N_GetterMeaning
set_option autoImplicit false
noncomputable section
namespace NMS_R2GetterLink
open Aeneas Aeneas.Std AdapterRw
/-- Full E003 getter observation at the SAME account, with the retained
std/allocator interpretation, against the approved canonical revision2 law.
All error payloads and stopped prefixes survive the carrier map. -/
theorem full (a : r1_pool_adapter.owned.OwnedAccount) :
 NMS_R2N_Interpreted.Simulates (NMS_R2N_RSLError.reply NMS_R2N_RSLScalars.bytes)
  (NMS_R2N_GetterMeaning.meaning a)
  (NMS_R2N_RSLPoolCarriers.account a).data := by
 rw [←NMS_R2CloneLaw.data]
 exact NMS_R2N_GetterMeaning.full a

/-- Exact value erasure to the fresh emitted getter, separate from the
allocation-sensitive observation law. -/
theorem erases (ops : Ops) (a : r1_pool_adapter.owned.OwnedAccount) :
 NMS_R2N_GetterMeaning.get ops.op35 a = NMS_Emitted.get ops a :=
 NMS_R2N_GetterMeaning.erases ops a
#print axioms full
#print axioms erases
end NMS_R2GetterLink
