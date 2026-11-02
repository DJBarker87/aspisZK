import PV_EVH_StackRegions
set_option autoImplicit false
namespace PV_EVH_StackCopy
open PV_EVH_StackZero (Slot State)
open PV_EVH_StackAdmission (Outside HeapSeparate HeapCoherent)

/-- Snapshot semantics of a byte copy into an already initialized exclusive
destination. Actual source/destination provenance, bounds, and primitive
association remain P. This state operation makes no event-silence claim. -/
def copy (src dst : Slot) (offset : Nat) (w : State) : State :=
  {w with memory := fun address =>
    if dst.address ≤ address ∧ address < dst.address+dst.initialized
    then w.memory (src.address+offset+(address-dst.address))
    else w.memory address}

theorem inside (src dst : Slot) (offset : Nat) (w : State)
    (i : Nat) (hi : i < dst.initialized) :
    (copy src dst offset w).memory (dst.address+i) =
      w.memory (src.address+offset+i) := by
  simp only [copy]
  rw [if_pos (by omega),Nat.add_sub_cancel_left]

theorem outside (src dst : Slot) (offset : Nat) (w : State)
    (address : Nat) (h : Outside dst address) :
    (copy src dst offset w).memory address = w.memory address := by
  simp only [copy]
  rw [if_neg (by unfold Outside at h; omega)]

theorem source_preserved (src dst : Slot) (offset : Nat) (w : State)
    (h : PV_EVH_StackRegions.Separate dst src)
    (i : Nat) (hi : i < src.initialized) :
    (copy src dst offset w).memory (src.address+i) = w.memory (src.address+i) :=
  outside src dst offset w _ (PV_EVH_StackRegions.outside dst src h i hi)

theorem heap_coherent (src dst : Slot) (offset : Nat) (w : State)
    (hc : HeapCoherent w) (hs : HeapSeparate dst w) :
    HeapCoherent (copy src dst offset w) := by
  intro b hb i hi
  exact (outside src dst offset w (b.address+i) (hs b hb i hi)).trans (hc b hb i hi)

theorem live_preserved (src dst old : Slot) (offset : Nat) (w : State)
    (hs : PV_EVH_StackAdmission.LiveSeparate dst w)
    (ho : old ∈ w.frame.live) (i : Nat) (hi : i < old.initialized) :
    (copy src dst offset w).memory (old.address+i) = w.memory (old.address+i) :=
  outside src dst offset w _ (hs old ho i hi)

/-- Copying bytes neither transfers ownership nor destroys any lifetime. -/
theorem frame_history (src dst : Slot) (offset : Nat) (w : State) :
    (copy src dst offset w).frame = w.frame ∧
    (copy src dst offset w).history = w.history ∧
    (copy src dst offset w).drops = w.drops := ⟨rfl,rfl,rfl⟩

#print axioms inside
#print axioms outside
#print axioms source_preserved
#print axioms heap_coherent
#print axioms live_preserved
#print axioms frame_history
end PV_EVH_StackCopy
