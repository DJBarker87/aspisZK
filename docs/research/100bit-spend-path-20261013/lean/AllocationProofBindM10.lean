import ExtractorProofBindM10

set_option autoImplicit false
namespace AspisR1.AllocationProofBindM10

@[noinline] def cells {A B : Type} (source : Option A) (x : Option A × Nat)
    (hv : x.1 = source) (_next : ∀ a, source = some a → Option B × Nat)
    (heap : Nat) (heapNext : ∀ a, source = some a → Nat) : Nat :=
  heap+match hx : x.1 with
  | none => 0
  | some a => heapNext a (hv.symm.trans hx)

theorem paid {A B : Type} (source : Option A) (x : Option A × Nat)
    (hv : x.1 = source) (next : ∀ a, source = some a → Option B × Nat)
    (heap : Nat) (heapNext : ∀ a, source = some a → Nat)
    (h : heap ≤ x.2) (hn : ∀ a ha, heapNext a ha ≤ (next a ha).2) :
    cells source x hv next heap heapNext ≤ (ExtractorProofBindM10.bind source x hv next).2 := by
  rcases x with ⟨o,n⟩
  cases o with
  | none => cases hv; exact h
  | some a => cases hv; exact Nat.add_le_add h (hn a rfl)

#print axioms paid
end AspisR1.AllocationProofBindM10
