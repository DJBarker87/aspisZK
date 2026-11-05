import NIO_Windows
import NIO_AbortScopes
import NIO_LoopModel
import NIK_Invariant
set_option autoImplicit false
namespace NIO_Invariant
open AspisR1.S2Trust

/-- Reuse the retained conditional scope theorem; native ScopeRun remains OPEN. -/
theorem certified_scope_preserves_room {F : Type} {s u : Heap F}
    (modelRun : NIK_Invariant.ScopeRun s u) (a : Nat)
    (entry : NIE_BorrowRelease.SharedRoom s a) :
    NIE_BorrowRelease.SharedRoom u a :=
  NIK_Invariant.scope_model_invariant modelRun a entry
#print axioms certified_scope_preserves_room

/-- A child can run while a different physical cell is exclusively guarded. -/
theorem cpi_preserves_held_counter {F : Type} (s u : Heap F)
    (touched : Nat → Prop) (frame : NIK_Footprint.CounterFrame s u touched)
    (c : Nat) (held : s.counter c = -1) (disjoint : ¬ touched c) :
    u.counter c = -1 := by
  rw [frame.2 c disjoint]
  exact held
#print axioms cpi_preserves_held_counter

/-- The explicit-counter reference uses the adopted library's exact update. -/
theorem put_is_library_put (s : Nat → Int) (c : Nat) (v : Int) :
    NIO_Nested.put s c v = AspisR1.S2Trust.put s c v := rfl
#print axioms put_is_library_put

theorem exclusive_acquire_counter {F : Type} (s : Heap F) (c t o : Nat) :
    (acquire s c t o .exclusive).counter = NIO_Nested.put s.counter c (-1) := rfl
#print axioms exclusive_acquire_counter

theorem exclusive_release_counter {F : Type} (s : Heap F) (c t o : Nat) :
    (release s ⟨t,c,o,.exclusive,(s.payload c).descriptor⟩).counter =
      NIO_Nested.put s.counter c 0 := rfl
#print axioms exclusive_release_counter

end NIO_Invariant
