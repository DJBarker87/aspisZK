import R1Z.PV_RunJoin_CircleOwnedProjection52
import R1Z.PV_RunJoin_CircleOwnedScalar52
import R1Z.PV_RunJoin_CircleRawTower52
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleOwnedOps52
open PV_RunJoin_CircleOwnedCarrier52
attribute [local irreducible] encCM encQ
theorem op0 (self : CM) (other : CM) :
    PV_AL_CircleOwned.aspis_core.field.CM31.Insts.CoreCmpPartialEqCM31.eq (encCM self) (encCM other) = PV_RunJoin_CircleRawTower52.field.CM31.Insts.CoreCmpPartialEqCM31.eq self other := by
  unfold PV_AL_CircleOwned.aspis_core.field.CM31.Insts.CoreCmpPartialEqCM31.eq PV_RunJoin_CircleRawTower52.field.CM31.Insts.CoreCmpPartialEqCM31.eq
  simp only [PV_RunJoin_CircleOwnedScalar52.f7,bind_assoc_eq,bind_tc_ok,PV_RunJoin_CircleOwnedProjection52.cm_a,PV_RunJoin_CircleOwnedProjection52.cm_b,PV_RunJoin_CircleOwnedProjection52.q_c0,PV_RunJoin_CircleOwnedProjection52.q_c1]

  all_goals simp only [encCM,encQ]
  all_goals rfl

#print axioms op0
end R1Z.PV_RunJoin_CircleOwnedOps52
