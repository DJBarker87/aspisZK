import NIE_BorrowRelease
set_option autoImplicit false
namespace NIE_AccessorPrecondition
open AspisR1.S2Trust NIE_BorrowRelease

/-- A valid state with room for a shared borrow has no tracked exclusive guard
on THAT cell. External-borrow admission and production relatedness stay separate. -/
theorem no_tracked_exclusive {F : Type} (s : Heap F) (a : Nat)
    (valid : Valid s) (room : SharedRoom s a) :
    count s (s.accounts a).1 .exclusive = 0 := by
  let c := (s.accounts a).1
  have nonneg : 0 ≤ count s c .exclusive := by unfold count; omega
  by_contra h
  have pos : 0 < count s c .exclusive := by omega
  obtain ⟨external, shared, exclusive⟩ := (valid.2.1 c).2.2.2.1 pos
  have balance := (valid.2.1 c).2.2.1
  have lower := room.1
  change 0 ≤ s.counter c at lower
  omega
#print axioms no_tracked_exclusive

theorem no_external_exclusive {F : Type} (s : Heap F) (a : Nat)
    (valid : Valid s) (room : SharedRoom s a) : 0 ≤ s.external (s.accounts a).1 := by
  let c := (s.accounts a).1
  by_contra h
  have neg : s.external c < 0 := by omega
  obtain ⟨shared, exclusive⟩ := (valid.2.1 c).2.2.2.2 neg
  have balance := (valid.2.1 c).2.2.1
  have lower := room.1
  change 0 ≤ s.counter c at lower
  omega
#print axioms no_external_exclusive

/-- Complete model-side acquisition domain from the actual token ledger. The
upper bound is explicit rather than lost behind 'no exclusive borrow'. -/
theorem room_from_ledger {F : Type} (s : Heap F) (a : Nat)
    (valid : Valid s)
    (external : 0 ≤ s.external (s.accounts a).1)
    (exclusive : count s (s.accounts a).1 .exclusive = 0)
    (capacity : s.external (s.accounts a).1 + count s (s.accounts a).1 .shared < maxCounter) :
    SharedRoom s a := by
  have balance := (valid.2.1 (s.accounts a).1).2.2.1
  have shared : 0 ≤ count s (s.accounts a).1 .shared := by unfold count; omega
  unfold SharedRoom
  constructor <;> omega
#print axioms room_from_ledger

/-- The model shared operation at an admitted accessor cut has the exact
success arm. It supplies neither runtime totality nor a concrete caller cut. -/
theorem model_shared_returns {F : Type} (s : Heap F) (a t o : Nat)
    (room : SharedRoom s a) :
    run s (.shared a t o) = (acquire s (s.accounts a).1 t o .shared, .guard t) := by
  simp only [run, if_pos room]
#print axioms model_shared_returns

/-- The exclusive unsplit acquisition/Drop pair restores an initially free
cell, including every aliased account and all untouched counters. -/
theorem exclusive_counter_roundtrip {F : Type} (s : Heap F) (c t o : Nat)
    (free : s.counter c = 0) :
    (release (acquire s c t o .exclusive)
      ⟨t,c,o,.exclusive,(s.payload c).descriptor⟩).counter = s.counter := by
  funext d
  by_cases h : d = c
  · subst d
    simp [release,acquire,put,free]
  · simp [release,acquire,put,h]
#print axioms exclusive_counter_roundtrip
end NIE_AccessorPrecondition
