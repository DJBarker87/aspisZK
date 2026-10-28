import R1Z.ProverRwP6BoundaryInstall
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP6BindTotal
open Aeneas Aeneas.Std Result
theorem bind_total {α β : Type} (f : Result α) (g : α → Result β)
    (left : ∃ a, f = ok a) (right : ∀ a, ∃ b, g a = ok b) :
    ∃ b, (do let a ← f; g a) = ok b := by
  obtain ⟨a, ha⟩ := left
  obtain ⟨b, hb⟩ := right a
  exact ⟨b, by rw [ha]; exact hb⟩
#print axioms bind_total
end R1Z.ProverRwP6BindTotal
