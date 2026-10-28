import Aeneas
set_option autoImplicit false
namespace PV_B2_C_ResultCongruence
open Aeneas Aeneas.Std Result

/-- Curried pair continuations preserve every failure tag and divergence.
Keeping pair elimination in this generic lemma avoids unfolding concrete arrays. -/
theorem pair {α β γ : Type} (r : Result (α × β))
    (f g : α → β → Result γ)
    (h : ∀ a b, r = ok (a,b) → f a b = g a b) :
    (do let (a,b) ← r; f a b) = (do let (a,b) ← r; g a b) := by
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a,b⟩ hr
  exact h a b hr

#print axioms pair
end PV_B2_C_ResultCongruence
