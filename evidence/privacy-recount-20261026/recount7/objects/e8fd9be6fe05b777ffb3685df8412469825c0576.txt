import PV_B3_FieldTransport
namespace PV_B3_FieldBind
open Aeneas Aeneas.Std Result PV_B3_FieldTransport
set_option autoImplicit false
-- Transport a result bind without assuming success, canonicality or termination.
theorem transport {α β γ δ : Type} (f : α → β) (g : γ → δ)
    (x : Result α) (y : Result β) (hx : map f x = y)
    (a : α → Result γ) (b : β → Result δ)
    (h : ∀ v, map g (a v) = b (f v)) :
    map g (x >>= a) = (y >>= b) := by
  rw [← hx]
  cases x with
  | ok v => exact h v
  | fail e => rfl
  | div => rfl
theorem bind_map {α β γ : Type} (f : α → β) (r : Result α) (g : β → Result γ) :
 (map f r >>= g) = (r >>= fun x => g (f x)) := by cases r <;> rfl
#print axioms transport
#print axioms bind_map
end PV_B3_FieldBind
