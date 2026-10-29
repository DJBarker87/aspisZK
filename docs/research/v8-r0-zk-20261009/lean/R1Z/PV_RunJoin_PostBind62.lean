import R1Z.PV_RunJoin_ResultPost41
set_option autoImplicit false
namespace R1Z.PV_RunJoin_PostBind62
open Aeneas Aeneas.Std Result PV_RunJoin_ResultPost41

theorem bind {A B : Type} (p : A → Prop) (q : B → Prop)
    (r : Result A) (f : A → Result B) (before : Post p r)
    (after : ∀ a, p a → Post q (f a)) : Post q (r >>= f) := by
  cases r with
  | fail e => trivial
  | div => trivial
  | ok a => exact after a before

#print axioms bind
end R1Z.PV_RunJoin_PostBind62
