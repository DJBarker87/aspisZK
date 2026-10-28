import R1Z.PV_RunJoin_ResultPost41
set_option autoImplicit false
namespace R1Z.PV_RunJoin_PostMap43
open Aeneas Aeneas.Std Result PV_RunJoin_ResultPost41

theorem mono {A : Type} {p q : A → Prop} {r : Result A}
    (h : Post p r) (f : ∀ a, p a → q a) : Post q r := by
  cases r with
  | ok a => exact f a h
  | fail e => trivial
  | div => trivial
#print axioms mono
end R1Z.PV_RunJoin_PostMap43
