import Aeneas.Std
namespace PV_B3_Result
open Aeneas Aeneas.Std Result
set_option autoImplicit false

-- Tiny generic API lemmas copied in this namespace to avoid importing the
-- unrelated full canonical-field cone that contains the older versions.
def Safe {α : Type} (post : α → Prop) (r : Result α) : Prop :=
  ∀ value, r = ok value → post value

theorem bind_success {α β : Type} (r : Result α) (f : α → Result β) (y : β)
    (h : (r >>= f) = ok y) : ∃ x, r = ok x ∧ f x = ok y := by
  cases r with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => cases h
  | div => cases h

theorem bind_any {α β : Type} (post : β → Prop) (r : Result α) (f : α → Result β)
    (hf : ∀ x, Safe post (f x)) : Safe post (r >>= f) := by
  cases r with
  | ok x => exact hf x
  | fail e => intro y h; cases h
  | div => intro y h; cases h

theorem bind_assoc {α β γ : Type} (r : Result α) (f : α → Result β)
    (g : β → Result γ) : ((r >>= f) >>= g) = (r >>= fun x => f x >>= g) := by
  cases r <;> rfl

#print axioms Safe
#print axioms bind_success
#print axioms bind_any
#print axioms bind_assoc
end PV_B3_Result
