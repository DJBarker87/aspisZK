import NDO_JHg_World
import JGx_EntryReads
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHi_AccountReads
open Aeneas Aeneas.Std Result S2W_D189Entry S2W_D189Wrappers JHg_World
attribute [local irreducible] e1 e2
attribute [local irreducible] JHg_DataMaster.value JHg_DataForest.value JHb_DataLane.value JHb_DataRegistry.value JHb_DataEntry.value

theorem master (ops : AdapterRw.Ops) :
    AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops (e2.snapshot 1 384 384)=ok (.Ok JHg_DataMaster.value) := by
  have b : e2.buffers (e2.handles 1).1=JHg_DataMaster.value := by unfold e2;rfl
  have len : (e2.buffers (e2.handles 1).1).val.length=384 := by rw [b];unfold JHg_DataMaster.value;exact JHg_DataMaster.length
  rw [JGx_EntryReads.data ops e2 1 384 384 (Or.inl len),b]
#print axioms master

theorem forest (ops : AdapterRw.Ops) :
    AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops (e2.snapshot 2 192 192)=ok (.Ok JHg_DataForest.value) := by
  have b : e2.buffers (e2.handles 2).1=JHg_DataForest.value := by unfold e2;rfl
  have len : (e2.buffers (e2.handles 2).1).val.length=192 := by rw [b];unfold JHg_DataForest.value;exact JHg_DataForest.length
  rw [JGx_EntryReads.data ops e2 2 192 192 (Or.inl len),b]
#print axioms forest

theorem lane (ops : AdapterRw.Ops) :
    AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops (e2.snapshot 3 768 768)=ok (.Ok JHb_DataLane.value) := by
  have b : e2.buffers (e2.handles 3).1=JHb_DataLane.value := by unfold e2;rfl
  have len : (e2.buffers (e2.handles 3).1).val.length=768 := by rw [b];unfold JHb_DataLane.value;exact JHb_DataLane.length
  rw [JGx_EntryReads.data ops e2 3 768 768 (Or.inl len),b]
#print axioms lane
end AspisR1.JHi_AccountReads
end
