import Aeneas
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDD_ResultLaws
@[simp] theorem bind_return {α : Type} (r : Result α) :
    (do let x ← r; ok x) = r := by
  cases r <;> rfl
#print axioms bind_return
end NDD_ResultLaws
