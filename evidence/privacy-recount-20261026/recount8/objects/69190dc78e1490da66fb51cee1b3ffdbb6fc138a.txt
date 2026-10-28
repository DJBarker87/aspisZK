import R1Z.PV_Join_ResultInvariant5
set_option autoImplicit false
namespace R1Z.PV_Join_BindSuccess5
open Aeneas Aeneas.Std Result

theorem unpack {α β : Type} (r : Result α) (f : α → Result β) (y : β)
    (h : (r >>= f) = .ok y) : ∃ x, r = .ok x ∧ f x = .ok y := by
  cases r with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => cases h
  | div => cases h

#print axioms unpack
end R1Z.PV_Join_BindSuccess5
