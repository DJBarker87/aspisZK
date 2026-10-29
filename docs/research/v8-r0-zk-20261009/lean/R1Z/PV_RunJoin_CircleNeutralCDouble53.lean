import R1Z.PV_RunJoin_CircleNeutralCAdd53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralCDouble53
open PV_RunJoin_CircleNeutralShape53

theorem complete (a : U32 × U32) (ha : CC a) :
    ∃ y, PV_RunJoin_CircleRawTower52.field.CM31.double a = ok y ∧
      PV_RunJoin_CircleR72Raw52.field.CM31.double a = ok y ∧ CC y :=
  PV_RunJoin_CircleNeutralCAdd53.complete a a ha ha

#print axioms complete
end R1Z.PV_RunJoin_CircleNeutralCDouble53
