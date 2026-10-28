import NDO_JHg_World
import JGx_EntryReads
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHj_RegistryReads
open Aeneas Aeneas.Std Result
open JHg_World
attribute [local irreducible] e2 JHb_DataRegistry.value JHb_DataEntry.value

theorem registry (ops : AdapterRw.Ops) :
    AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops (e2.snapshot 4 128 256)=ok (.Ok JHb_DataRegistry.value) := by
  have b : e2.buffers (e2.handles 4).1=JHb_DataRegistry.value := by unfold e2;rfl
  have len : (e2.buffers (e2.handles 4).1).val.length=256 := by
    rw [b];unfold JHb_DataRegistry.value;exact JHb_DataRegistry.length
  rw [JGx_EntryReads.data ops e2 4 128 256 (Or.inr len),b]
#print axioms registry

theorem entry (ops : AdapterRw.Ops) :
    AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops (e2.snapshot 5 192 320)=ok (.Ok JHb_DataEntry.value) := by
  have b : e2.buffers (e2.handles 5).1=JHb_DataEntry.value := by unfold e2;rfl
  have len : (e2.buffers (e2.handles 5).1).val.length=320 := by
    rw [b];unfold JHb_DataEntry.value;exact JHb_DataEntry.length
  rw [JGx_EntryReads.data ops e2 5 192 320 (Or.inr len),b]
#print axioms entry
end AspisR1.JHj_RegistryReads
end
