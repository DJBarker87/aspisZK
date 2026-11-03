import PV_EVH_StackMove
set_option autoImplicit false
namespace PV_EVH_StackTransfer
open PV_EVH_StackZero (Slot State)
open PV_EVH_StackCleanup (sameKey)

/-- Ghost lifetime transfer after the actual return stores. This neither
invents extra physical copies nor inserts a moved-from destructor. Reached
native ownership interpretation stays FRAME-CALL/MOVE-COMPILER under V370. -/
def transfer (src dst : Slot) (w : State) : State :=
  {w with frame := {w.frame with
    live := dst :: w.frame.live.filter (fun s => s.key != src.key)
    retired := src :: w.frame.retired}}

theorem frame (src dst : Slot) (w : State) :
    (transfer src dst w).frame = (PV_EVH_StackMove.relocate src dst w).frame := rfl

theorem memory (src dst : Slot) (w : State) :
    (transfer src dst w).memory = w.memory := rfl

theorem original_lookup (src dst original : Slot) (w : State)
    (hl : w.frame.live.find? (sameKey original.key) = some original)
    (hs : original.key ≠ src.key) (hd : sameKey original.key dst = false) :
    (transfer src dst w).frame.live.find? (sameKey original.key) = some original := by
  rw [frame]
  exact PV_EVH_StackMove.original_lookup src dst original w hl hs hd

theorem no_destructor (src dst : Slot) (w : State) :
    (transfer src dst w).history = w.history ∧
    (transfer src dst w).writes = w.writes ∧
    (transfer src dst w).barriers = w.barriers ∧
    (transfer src dst w).drops = w.drops ∧
    (transfer src dst w).frame.runtime = w.frame.runtime := ⟨rfl,rfl,rfl,rfl,rfl⟩

#print axioms frame
#print axioms memory
#print axioms original_lookup
#print axioms no_destructor
end PV_EVH_StackTransfer
