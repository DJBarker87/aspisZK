import R1Z.PV_Canon_Result
set_option autoImplicit false
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result
 theorem bind_congr_success {α β : Type} (r : Result α) (f g : α → Result β)
    (h : ∀ x, r = .ok x → f x = g x) : (r >>= f) = (r >>= g) := by
  cases r with
  | ok x => exact h x rfl
  | fail e => rfl
  | div => rfl
 theorem bind_congr_all {α β : Type} (r : Result α) (f g : α → Result β)
    (h : ∀ x, f x = g x) : (r >>= f) = (r >>= g) :=
  bind_congr_success r f g (fun x _ => h x)
#print axioms bind_congr_success
#print axioms bind_congr_all
end R1Z.PV_Canon
