import NIE_AccessorPrecondition
set_option autoImplicit false
namespace NIE_BorrowScopes
open AspisR1.S2Trust NIE_BorrowRelease NIE_AccessorPrecondition

/-- Token freshness, independently of integer addresses or account keys. -/
def FreshToken {F : Type} (s : Heap F) (t : Nat) : Prop :=
  ∀ g, g ∈ s.guards → g.token ≠ t

/-- No pre-existing token is lost by the matching Drop. The acquired token
is removed exactly once. This is a model identity, not a production trace. -/
theorem guards_roundtrip {F : Type} (s : Heap F) (c t o : Nat) (k : Kind)
    (fresh : FreshToken s t) :
    (release (acquire s c t o k) ⟨t,c,o,k,(s.payload c).descriptor⟩).guards = s.guards := by
  have old : s.guards.filter (fun g => g.token != t) = s.guards := by
    apply List.filter_eq_self.mpr
    intro g hg
    simp [fresh g hg]
  dsimp [release,acquire]
  simp [old]
#print axioms guards_roundtrip

/-- With a fresh token the whole SDK-model heap, not only its counter, is
restored by a shared acquire/drop scope. Intermediate validity/enabledness
remain separate obligations when relating the scope to a typed SDK call. -/
theorem shared_heap_roundtrip {F : Type} (s : Heap F) (c t o : Nat)
    (fresh : FreshToken s t) :
    release (acquire s c t o .shared) ⟨t,c,o,.shared,(s.payload c).descriptor⟩ = s := by
  let after := release (acquire s c t o .shared) ⟨t,c,o,.shared,(s.payload c).descriptor⟩
  have hc : after.counter = s.counter := shared_counter_roundtrip s c t o
  have hg : after.guards = s.guards := guards_roundtrip s c t o .shared fresh
  change after = s
  calc
    after = {s with counter := after.counter, guards := after.guards} := rfl
    _ = s := by rw [hc,hg]
#print axioms shared_heap_roundtrip

/-- The corresponding unsplit exclusive scope requires an initially free
cell. Writes are not erased by this theorem: this is the no-write scope. -/
theorem exclusive_heap_roundtrip {F : Type} (s : Heap F) (c t o : Nat)
    (free : s.counter c = 0) (fresh : FreshToken s t) :
    release (acquire s c t o .exclusive) ⟨t,c,o,.exclusive,(s.payload c).descriptor⟩ = s := by
  let after := release (acquire s c t o .exclusive) ⟨t,c,o,.exclusive,(s.payload c).descriptor⟩
  have hc : after.counter = s.counter := exclusive_counter_roundtrip s c t o free
  have hg : after.guards = s.guards := guards_roundtrip s c t o .exclusive fresh
  change after = s
  calc
    after = {s with counter := after.counter, guards := after.guards} := rfl
    _ = s := by rw [hc,hg]
#print axioms exclusive_heap_roundtrip

/-- Validity of the exact pre-state is retained at the end of the model scope;
no independently selected post-state or guard ledger is substituted. -/
theorem valid_after_shared_scope {F : Type} (s : Heap F) (c t o : Nat)
    (valid : Valid s) (fresh : FreshToken s t) :
    Valid (release (acquire s c t o .shared) ⟨t,c,o,.shared,(s.payload c).descriptor⟩) := by
  rw [shared_heap_roundtrip s c t o fresh]
  exact valid
#print axioms valid_after_shared_scope

theorem valid_after_exclusive_scope {F : Type} (s : Heap F) (c t o : Nat)
    (valid : Valid s) (free : s.counter c = 0) (fresh : FreshToken s t) :
    Valid (release (acquire s c t o .exclusive) ⟨t,c,o,.exclusive,(s.payload c).descriptor⟩) := by
  rw [exclusive_heap_roundtrip s c t o free fresh]
  exact valid
#print axioms valid_after_exclusive_scope
end NIE_BorrowScopes
