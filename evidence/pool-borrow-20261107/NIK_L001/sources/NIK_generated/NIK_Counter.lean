import NIE_BorrowRelease
set_option autoImplicit false
namespace NIK_Counter
open AspisR1.S2Trust

/-- A model law, conditional on exclusive acquisition's actual domain. -/
theorem exclusive_roundtrip {F : Type} (s : Heap F) (c t o : Nat)
    (free : s.counter c = 0) :
    (release (acquire s c t o .exclusive)
      ⟨t,c,o,.exclusive,(s.payload c).descriptor⟩).counter = s.counter := by
  funext d
  by_cases h : d = c
  · subst d
    simp only [release, acquire, put, if_pos]
    omega
  · simp [release, acquire, put, h]
#print axioms exclusive_roundtrip

theorem exclusive_frame {F : Type} (s : Heap F) (c t o : Nat) :
    (release (acquire s c t o .exclusive)
      ⟨t,c,o,.exclusive,(s.payload c).descriptor⟩).accounts = s.accounts ∧
    (release (acquire s c t o .exclusive)
      ⟨t,c,o,.exclusive,(s.payload c).descriptor⟩).payload = s.payload ∧
    (release (acquire s c t o .exclusive)
      ⟨t,c,o,.exclusive,(s.payload c).descriptor⟩).ambient = s.ambient := by
  exact ⟨rfl,rfl,rfl⟩
#print axioms exclusive_frame

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
  apply room_of_frame s _ (exclusive_frame s c t o).1
    (exclusive_roundtrip s c t o free) a room
#print axioms exclusive_scope_room
end NIK_Counter
