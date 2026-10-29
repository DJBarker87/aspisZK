import R1Z.PV_RunJoin_CircleNeutralResult53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralAlignedTransport53
open PV_RunJoin_CircleNeutralResult53

theorem transport {A : Type} {P : A → Prop} {x x' y y' : Result A}
    (hx : x=x') (hy : y=y') (h : Aligned P x' y') : Aligned P x y := by
  cases hx
  cases hy
  exact h

#print axioms transport
end R1Z.PV_RunJoin_CircleNeutralAlignedTransport53
