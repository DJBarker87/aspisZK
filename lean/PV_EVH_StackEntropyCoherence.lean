import PV_EVH_StackEntropyFill
set_option autoImplicit false
noncomputable section
namespace PV_EVH_StackEntropyCoherence
open Aeneas Aeneas.Std ProverRwFull
open PV_EVH_StackZero (Slot State)
open PV_EVH_StackAdmission
variable [ExternalTypes]

def Fresh (slot : Slot) (w : State) : Prop :=
  ∀ old ∈ w.frame.live, old.key ≠ slot.key

/-- The source initializer does not itself choose or prove the machine frame's
address. This is the invariant its native frame association must establish. -/
def Admission (slot : Slot) (w : State) : Prop :=
  slot.initialized = 64 ∧ Fresh slot w ∧ HeapSeparate slot w ∧ LiveSeparate slot w

theorem post_heap (slot : Slot) (d : PV_EVH_StackEntropyFill.Delivery) (w : State)
    (hc : HeapCoherent w) (hs : HeapSeparate slot w)
    (hh : d.runtime.heap = w.frame.runtime.heap) :
    HeapCoherent (PV_EVH_StackEntropyFill.post slot d w) := by
  intro b hb i hi
  change b ∈ d.runtime.heap at hb
  rw [hh] at hb
  exact (write_outside slot (PV_EVH_StackEntropyFill.encode d.buffer) w
    (b.address+i) (hs b hb i hi)).trans (hc b hb i hi)

theorem post_separate (slot : Slot) (d : PV_EVH_StackEntropyFill.Delivery) (w : State)
    (hs : HeapSeparate slot w) (hh : d.runtime.heap = w.frame.runtime.heap) :
    HeapSeparate slot (PV_EVH_StackEntropyFill.post slot d w) := by
  intro b hb i hi
  change b ∈ d.runtime.heap at hb
  rw [hh] at hb
  exact hs b hb i hi

theorem cleanup_heap (slot : Slot) (d : PV_EVH_StackEntropyFill.Delivery)
    (bytes : PV_RJ4IDB.Bytes) (w : State) (hc : HeapCoherent w)
    (hs : HeapSeparate slot w) (hh : d.runtime.heap = w.frame.runtime.heap) :
    HeapCoherent (PV_EVH_StackZero.drop slot
      (PV_EVH_StackEntropyFill.post slot d (enter slot bytes w))) := by
  have hs' : HeapSeparate slot (enter slot bytes w) := hs
  exact drop_heap slot _
    (post_heap slot d _ (enter_heap slot bytes w hc hs) hs' hh)
    (post_separate slot d _ hs' hh)

/-- Cleanup removes exactly the admitted lifetime, retaining every prior live
owner. Equal-valued buffers cannot redirect or retire another owner's slot. -/
theorem cleanup_live (slot : Slot) (d : PV_EVH_StackEntropyFill.Delivery)
    (bytes : PV_RJ4IDB.Bytes) (w : State) (hfresh : Fresh slot w) :
    (PV_EVH_StackZero.drop slot
      (PV_EVH_StackEntropyFill.post slot d (enter slot bytes w))).frame.live = w.frame.live := by
  let v := PV_EVH_StackEntropyFill.post slot d (enter slot bytes w)
  have hf := (PV_EVH_DeployedZeroWorld.frame slot.address slot.initialized v).1
  change (PV_EVH_DeployedZeroCursor.run _ _ _ v).frame.live.filter
    (fun s => s.key != slot.key) = _
  rw [PV_EVH_DeployedZeroCursor.source,hf]
  change (slot :: w.frame.live).filter (fun s => s.key != slot.key) = _
  simp only [List.filter_cons,bne_self_eq_false,Bool.false_eq_true,if_false]
  apply List.filter_eq_self.mpr
  intro old ho
  simp [hfresh old ho]

#print axioms post_heap
#print axioms post_separate
#print axioms cleanup_heap
#print axioms cleanup_live
end PV_EVH_StackEntropyCoherence
