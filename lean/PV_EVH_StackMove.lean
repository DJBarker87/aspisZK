import PV_EVH_StackCopy
import PV_EVH_StackCleanup
set_option autoImplicit false
namespace PV_EVH_StackMove
open PV_EVH_StackZero (Slot State)
open PV_EVH_StackCleanup (sameKey)

/-- Byte-relocation representation of a move, with ghost lifetime transfer.
No destructor or zeroization is inserted. Source/destination addresses come
from provenance; overlap is allowed by snapshot semantics. Relating this
representation to the reached Rust return-place move remains P under V370/L3.
This is a state law and does not assert the native move has no observations. -/
def relocate (src dst : Slot) (w : State) : State :=
  let v := PV_EVH_StackCopy.copy src dst 0 w
  {v with frame := {v.frame with
    live := dst :: v.frame.live.filter (fun s => s.key != src.key)
    retired := src :: v.frame.retired}}

theorem destination (src dst : Slot) (w : State)
    (i : Nat) (hi : i < dst.initialized) :
    (relocate src dst w).memory (dst.address+i) = w.memory (src.address+i) := by
  exact (PV_EVH_StackCopy.inside src dst 0 w i hi).trans (by rw [Nat.add_zero])

theorem no_destructor (src dst : Slot) (w : State) :
    (relocate src dst w).drops = w.drops ∧
    (relocate src dst w).writes = w.writes ∧
    (relocate src dst w).barriers = w.barriers ∧
    (relocate src dst w).history = w.history := ⟨rfl,rfl,rfl,rfl⟩

/-- A source residue is preserved only outside the destination footprint.
There is deliberately no moved-from-cleared postcondition. -/
theorem residue_outside (src dst : Slot) (w : State) (address : Nat)
    (h : PV_EVH_StackAdmission.Outside dst address) :
    (relocate src dst w).memory address = w.memory address :=
  PV_EVH_StackCopy.outside src dst 0 w address h

theorem runtime (src dst : Slot) (w : State) :
    (relocate src dst w).frame.runtime = w.frame.runtime := rfl

theorem find_filter_keep {A : Type} (p q : A → Bool) (xs : List A) (x : A)
    (hf : xs.find? p = some x) (hq : q x = true) :
    (xs.filter q).find? p = some x := by
  induction xs with
  | nil => cases hf
  | cons a rest ih =>
    by_cases hp : p a = true
    · have he : a = x := by simpa [List.find?_cons,hp] using hf
      subst a
      simp only [List.filter_cons,hq,if_true,List.find?_cons,hp]
    · have hp' : p a = false := Bool.eq_false_iff.mpr hp
      have hr : rest.find? p = some x := by simpa [List.find?_cons,hp'] using hf
      by_cases hqa : q a = true
      · simpa [List.filter_cons,hqa,List.find?_cons,hp'] using ih hr
      · have hqa' : q a = false := Bool.eq_false_iff.mpr hqa
        simpa [List.filter_cons,hqa'] using ih hr

/-- The original cleanup slot survives a different source lifetime transfer,
and a different returned key cannot shadow it. This discharges the post-move
lookup premise from explicit key provenance for this relocation representation. -/
theorem original_lookup (src dst original : Slot) (w : State)
    (hl : w.frame.live.find? (sameKey original.key) = some original)
    (hs : original.key ≠ src.key)
    (hd : sameKey original.key dst = false) :
    (relocate src dst w).frame.live.find? (sameKey original.key) = some original := by
  change (dst :: w.frame.live.filter (fun s => s.key != src.key)).find?
    (sameKey original.key) = some original
  simp only [List.find?_cons,hd,Bool.false_eq_true,if_false]
  exact find_filter_keep (sameKey original.key) (fun s => s.key != src.key)
    w.frame.live original hl (by simpa using hs)

#print axioms destination
#print axioms no_destructor
#print axioms residue_outside
#print axioms runtime
#print axioms find_filter_keep
#print axioms original_lookup
end PV_EVH_StackMove
