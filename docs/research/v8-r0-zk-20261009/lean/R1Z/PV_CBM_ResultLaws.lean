import R1Z.ProverRwFullTypes
namespace R1Z.PV_CBM_ResultLaws
open Aeneas Aeneas.Std Result
set_option autoImplicit false

theorem bind_return {α : Type} (r : Result α) :
    (do let value ← r; ok value) = r := by
  cases r <;> rfl

#print axioms bind_return
end R1Z.PV_CBM_ResultLaws
