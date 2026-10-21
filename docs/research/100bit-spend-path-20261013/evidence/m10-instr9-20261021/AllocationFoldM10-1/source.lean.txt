import ExtractorWorkMonad

set_option autoImplicit false
namespace AspisR1.AllocationFoldM10

def cells {A S : Type} (f : S → A → S × Nat) (heap : S → A → Nat) :
    S → List A → Nat
  | _, [] => 0
  | s, a::xs => heap s a+cells f heap (f s a).1 xs

theorem work {A S : Type} (f : S → A → S × Nat) (heap : S → A → Nat)
    (h : ∀ s a, heap s a ≤ (f s a).2) (s : S) (xs : List A) :
    cells f heap s xs ≤ (ExtractorWorkMonad.foldl f s xs).2 := by
  induction xs generalizing s with
  | nil => exact Nat.le_refl _
  | cons a xs ih => exact Nat.add_le_add (h s a) (ih (f s a).1)

#print axioms work
end AspisR1.AllocationFoldM10
