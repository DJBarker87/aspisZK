import R1Z.PV_RunJoin_CircleOwnedOp652
import R1Z.PV_RunJoin_CircleOwnedScalar52
import R1Z.PV_RunJoin_CircleRawTower52
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleOwnedOps52
open PV_RunJoin_CircleOwnedCarrier52
attribute [local irreducible] encCM encQ
theorem op6 (self : CM) :
    PV_AL_CircleOwned.aspis_core.field.CM31.neg (encCM self) = (do let x ← PV_RunJoin_CircleRawTower52.field.CM31.neg self; ok (encCM x)) := by
  unfold PV_AL_CircleOwned.aspis_core.field.CM31.neg PV_RunJoin_CircleRawTower52.field.CM31.neg
  simp only [PV_RunJoin_CircleOwnedScalar52.f18,bind_assoc_eq,bind_tc_ok,PV_RunJoin_CircleOwnedProjection52.cm_a,PV_RunJoin_CircleOwnedProjection52.cm_b,PV_RunJoin_CircleOwnedProjection52.q_c0,PV_RunJoin_CircleOwnedProjection52.q_c1]

  all_goals simp only [encCM,encQ]
  all_goals rfl

#print axioms op7
end R1Z.PV_RunJoin_CircleOwnedOps52
