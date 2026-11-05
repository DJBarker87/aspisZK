import NIE_AccessorPrecondition
set_option autoImplicit false
namespace NIK_Counter
open AspisR1.S2Trust

theorem room_of_frame {F : Type} (s u : Heap F)
    (cells : u.accounts = s.accounts) (counters : u.counter = s.counter)
    (a : Nat) (h : NIE_BorrowRelease.SharedRoom s a) :
    NIE_BorrowRelease.SharedRoom u a := by
  unfold NIE_BorrowRelease.SharedRoom at *
  rw [cells,counters]
  exact h
#print axioms room_of_frame

theorem exclusive_scope_room {F : Type} (s : Heap F) (c t o a : Nat)
    (free : s.counter c = 0) (room : NIE_BorrowRelease.SharedRoom s a) :
    NIE_BorrowRelease.SharedRoom
      (release (acquire s c t o .exclusive)
        ⟨t,c,o,.exclusive,(s.payload c).descriptor⟩) a := by
  unfold NIE_BorrowRelease.SharedRoom at *
  change 0 ≤ _ ∧ _ < _
  rw [NIE_AccessorPrecondition.exclusive_counter_roundtrip s c t o free]
  exact room
#print axioms exclusive_scope_room
end NIK_Counter
