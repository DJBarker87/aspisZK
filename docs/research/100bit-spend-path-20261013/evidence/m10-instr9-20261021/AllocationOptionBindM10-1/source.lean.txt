import PublicParserWork

set_option autoImplicit false
namespace AspisR1.AllocationOptionBindM10

def cells {A : Type} (x : Option A × Nat) (heap : Nat) (nextHeap : A → Nat) : Nat :=
  heap+(match x.1 with | none => 0 | some a => nextHeap a)+1

theorem paid {A B : Type} (x : Option A × Nat) (next : A → Option B × Nat)
    (heap : Nat) (nextHeap : A → Nat) (h : heap ≤ x.2)
    (hn : ∀ a, nextHeap a ≤ (next a).2) :
    cells x heap nextHeap ≤ (PublicParserWork.bind x next).2 := by
  rcases x with ⟨o,n⟩
  cases o with
  | none => exact Nat.add_le_add_right h 1
  | some a => exact Nat.add_le_add_right (Nat.add_le_add h (hn a)) 1

#print axioms paid
end AspisR1.AllocationOptionBindM10
