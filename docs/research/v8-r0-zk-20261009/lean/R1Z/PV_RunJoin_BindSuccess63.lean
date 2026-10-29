import Aeneas
set_option autoImplicit false
namespace R1Z.PV_RunJoin_BindSuccess63
open Aeneas Aeneas.Std Result
/-- Congruence only on reached successful values; failed/diverging prefixes
remain untouched. This supports resource bounds on finite source loops. -/
theorem congr {A B : Type} (r : Result A) (f g : A → Result B)
    (law : ∀ a, r=ok a → f a=g a) : (r >>= f)=(r >>= g) := by
  cases r with
  | fail e => rfl
  | div => rfl
  | ok a => exact law a rfl

#print axioms congr
end R1Z.PV_RunJoin_BindSuccess63
