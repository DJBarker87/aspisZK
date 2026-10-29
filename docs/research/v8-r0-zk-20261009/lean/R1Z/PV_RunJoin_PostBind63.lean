import R1Z.PV_RunJoin_ResultPost41
set_option autoImplicit false
namespace R1Z.PV_RunJoin_PostBind63
open Aeneas Aeneas.Std Result PV_RunJoin_ResultPost41
/-- Preserve a previously established postcondition through a source bind.
Fail and divergence remain their original Result constructors. -/
theorem guarded {A B : Type} (p : A → Prop) (q : B → Prop)
    (r : Result A) (f : A → Result B) (source : Post p r)
    (step : ∀ a, p a → Post q (f a)) : Post q (r >>= f) := by
  cases r with
  | fail e => trivial
  | div => trivial
  | ok a => exact step a source

#print axioms guarded
end R1Z.PV_RunJoin_PostBind63
