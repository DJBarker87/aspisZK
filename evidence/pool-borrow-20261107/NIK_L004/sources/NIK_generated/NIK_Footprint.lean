import NIK_Counter
set_option autoImplicit false
namespace NIK_Footprint
open AspisR1.S2Trust

/-- `touched` names physical cells, never just account indices or keys. -/
def CounterFrame {F : Type} (s u : Heap F) (touched : Nat → Prop) : Prop :=
  u.accounts = s.accounts ∧ ∀ c, ¬ touched c → u.counter c = s.counter c

theorem outside_room {F : Type} (s u : Heap F) (touched : Nat → Prop)
    (frame : CounterFrame s u touched) (a : Nat)
    (outside : ¬ touched (s.accounts a).1)
    (room : NIE_BorrowRelease.SharedRoom s a) :
    NIE_BorrowRelease.SharedRoom u a := by
  unfold NIE_BorrowRelease.SharedRoom at *
  rw [frame.1,frame.2 _ outside]
  exact room
#print axioms outside_room

/-- Aliased handles must be excluded together by the physical-cell footprint. -/
theorem alias_footprint {F : Type} (s : Heap F) (touched : Nat → Prop)
    (a b : Nat) (same : (s.accounts a).1 = (s.accounts b).1) :
    touched (s.accounts a).1 ↔ touched (s.accounts b).1 := by
  rw [same]
#print axioms alias_footprint

theorem frame_compose {F : Type} (s u v : Heap F) (p q : Nat → Prop)
    (first : CounterFrame s u p) (second : CounterFrame u v q) :
    CounterFrame s v (fun c => p c ∨ q c) := by
  refine ⟨second.1.trans first.1,?_⟩
  intro c outside
  exact (second.2 c (fun h => outside (Or.inr h))).trans
    (first.2 c (fun h => outside (Or.inl h)))
#print axioms frame_compose

/-- A negative counter rules out an infallible accessor on the SAME cell. -/
theorem negative_blocks {F : Type} (s : Heap F) (a : Nat)
    (negative : s.counter (s.accounts a).1 < 0) :
    ¬ NIE_BorrowRelease.SharedRoom s a := by
  intro room
  have nonnegative := room.1
  omega
#print axioms negative_blocks
end NIK_Footprint
