import PV_EVH_StackMove
set_option autoImplicit false
namespace PV_EVH_StackSizedDrop
open Aeneas Aeneas.Std
open PV_EVH_StackZero (State Slot)
open PV_EVH_StackCleanup (Q sameKey)
open PV_EVH_HeapOwnership (Key)

/-- Checked array destructor, including the two actual inner32 lifetimes.
Failure to find the original key/extent is a runtime fault, never a redirected
cleanup of a different equal-valued slot. The deployed byte law is unchanged. -/
def drop (size : Nat) (key : Key) : Q Unit := fun w =>
  match w.frame.live.find? (sameKey key) with
  | none => ⟨.fault (.invalidMemory key.identity),w,[]⟩
  | some slot =>
    if slot.initialized = size then
      ⟨.returned (.ok ()),PV_EVH_StackZero.drop slot w,PV_EVH_StackZero.emitted slot⟩
    else ⟨.fault (.invalidMemory key.identity),w,[]⟩

theorem drop64 : drop 64 = PV_EVH_StackCleanup.drop64 := rfl

theorem returned (size : Nat) (key : Key) (slot : Slot) (w : State)
    (hl : w.frame.live.find? (sameKey key) = some slot) (hn : slot.initialized = size) :
    drop size key w =
      ⟨.returned (.ok ()),PV_EVH_StackZero.drop slot w,PV_EVH_StackZero.emitted slot⟩ := by
  simp only [drop,hl,hn,if_true]

theorem live_after (slot : Slot) (w : State) :
    (PV_EVH_StackZero.drop slot w).frame.live =
      w.frame.live.filter (fun s => s.key != slot.key) := by
  have hf := (PV_EVH_DeployedZeroWorld.frame slot.address slot.initialized w).1
  change (PV_EVH_DeployedZeroCursor.run _ _ _ w).frame.live.filter _ = _
  rw [PV_EVH_DeployedZeroCursor.source,hf]

theorem keeps_lookup (removed old : Slot) (w : State)
    (hl : w.frame.live.find? (sameKey old.key) = some old)
    (hne : old.key ≠ removed.key) :
    (PV_EVH_StackZero.drop removed w).frame.live.find? (sameKey old.key) = some old := by
  rw [live_after]
  exact PV_EVH_StackMove.find_filter_keep _ _ _ _ hl (by simp [hne])

theorem missing (size : Nat) (key : Key) (w : State)
    (hl : w.frame.live.find? (sameKey key) = none) :
    drop size key w = ⟨.fault (.invalidMemory key.identity),w,[]⟩ := by
  simp only [drop,hl]

#print axioms drop64
#print axioms returned
#print axioms live_after
#print axioms keeps_lookup
#print axioms missing
end PV_EVH_StackSizedDrop
