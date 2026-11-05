import S2TrustedSdkBorrow
set_option autoImplicit false
namespace NIE_BorrowRelease
open AspisR1.S2Trust

/-- Both bounds are needed by an infallible shared acquisition. This is a
library predicate, not an asserted production caller invariant. -/
def SharedRoom {F : Type} (s : Heap F) (a : Nat) : Prop :=
  0 ≤ s.counter (s.accounts a).1 ∧ s.counter (s.accounts a).1 < maxCounter

/-- Acquisition followed by the matching unsplit shared Drop restores every
counter, including when other account handles alias this cell. -/
theorem shared_counter_roundtrip {F : Type} (s : Heap F) (c t o : Nat) :
    (release (acquire s c t o .shared)
      ⟨t,c,o,.shared,(s.payload c).descriptor⟩).counter = s.counter := by
  funext d
  by_cases h : d = c
  · subst d
    simp only [release, acquire, put, if_pos, Kind.shared.injEq]
    omega
  · simp [release, acquire, put, h]
#print axioms shared_counter_roundtrip

/-- A shared scope does not change the account-to-cell map or payload. -/
theorem shared_frame {F : Type} (s : Heap F) (c t o : Nat) :
    (release (acquire s c t o .shared)
      ⟨t,c,o,.shared,(s.payload c).descriptor⟩).accounts = s.accounts ∧
    (release (acquire s c t o .shared)
      ⟨t,c,o,.shared,(s.payload c).descriptor⟩).payload = s.payload ∧
    (release (acquire s c t o .shared)
      ⟨t,c,o,.shared,(s.payload c).descriptor⟩).ambient = s.ambient := by
  exact ⟨rfl,rfl,rfl⟩
#print axioms shared_frame

theorem shared_room_roundtrip {F : Type} (s : Heap F) (c t o a : Nat)
    (h : SharedRoom s a) :
    SharedRoom (release (acquire s c t o .shared)
      ⟨t,c,o,.shared,(s.payload c).descriptor⟩) a := by
  unfold SharedRoom at *
  rw [shared_counter_roundtrip]
  exact h
#print axioms shared_room_roundtrip

/-- Aliasing cannot be discharged from key inequality. This theorem requires
identity of the two actual cell projections, as provided by interpretation. -/
theorem alias_room {F : Type} (s : Heap F) (a b : Nat)
    (same : (s.accounts a).1 = (s.accounts b).1) :
    SharedRoom s a ↔ SharedRoom s b := by
  simp only [SharedRoom,same]
#print axioms alias_room

/-- Nonnegativity alone does not supply the complete accessor domain. No
concrete input or production reachability is asserted. -/
theorem saturation_not_shared_room {F : Type} (s : Heap F) (a : Nat)
    (h : s.counter (s.accounts a).1 = maxCounter) : ¬ SharedRoom s a := by
  simp [SharedRoom,h]
#print axioms saturation_not_shared_room
end NIE_BorrowRelease
