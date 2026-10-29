import R1Z.PV_RunJoin_ResultPost41
set_option autoImplicit false
namespace R1Z.PV_RunJoin_PostEquation60
open Aeneas Aeneas.Std Result PV_RunJoin_ResultPost41

theorem bind {A B : Type} (P : B → Prop) (m : Result A) (k : A → Result B)
    (step : ∀ a, m=ok a → Post P (k a)) : Post P (m >>= k) := by
  cases hm : m with
  | fail e => trivial
  | div => trivial
  | ok a => exact step a hm

#print axioms bind
end R1Z.PV_RunJoin_PostEquation60
