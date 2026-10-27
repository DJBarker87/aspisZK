import Aeneas
set_option autoImplicit false
namespace LPl_C
/-- Reachable-state simulation, not a hypothesis about the whole loop result. -/
theorem fold_simulation {A S T : Type} (xs : List A) (left : S → A → S)
    (right : T → A → T) (R : S → T → Prop) (s : S) (t : T)
    (initial : R s t)
    (stage : ∀ x ∈ xs, ∀ s t, R s t → R (left s x) (right t x)) :
    R (xs.foldl left s) (xs.foldl right t) := by
  induction xs generalizing s t with
  | nil => exact initial
  | cons x xs ih =>
    apply ih
    · exact stage x (by simp) s t initial
    · intro y hy s t h
      exact stage y (by simp only [List.mem_cons]; exact Or.inr hy) s t h
#print axioms fold_simulation
end LPl_C
