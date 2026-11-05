import NIO_Cpi
import NIK_Invariant
set_option autoImplicit false
namespace NIO_Invariant
open AspisR1.S2Trust

/-- Reuse the retained conditional scope theorem; native ScopeRun remains OPEN. -/
theorem certified_scope_preserves_room {F : Type} {s u : Heap F}
    (nativeScope : NIK_Invariant.ScopeRun s u) (a : Nat)
    (entry : NIE_BorrowRelease.SharedRoom s a) :
    NIE_BorrowRelease.SharedRoom u a :=
  NIK_Invariant.scope_model_invariant nativeScope a entry
#print axioms certified_scope_preserves_room

/-- A child can run while a different physical cell is exclusively guarded. -/
theorem cpi_preserves_held_counter {F : Type} (s u : Heap F)
    (touched : Nat → Prop) (frame : NIK_Footprint.CounterFrame s u touched)
    (c : Nat) (held : s.counter c = -1) (disjoint : ¬ touched c) :
    u.counter c = -1 := by
  rw [frame.2 c disjoint]
  exact held
#print axioms cpi_preserves_held_counter
end NIO_Invariant
