import Aeneas
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ResultBindEq55
open Aeneas Aeneas.Std Result

theorem complete {A B : Type} (m : Result A) (f g : A → Result B)
    (h : ∀ a,f a=g a) : (m >>= f)=(m >>= g) := by
  cases m with
  | ok a => exact h a
  | fail e => rfl
  | div => rfl
#print axioms complete
end R1Z.PV_RunJoin_ResultBindEq55
