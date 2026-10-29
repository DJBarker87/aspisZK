import R1Z.PV_RunJoin_CircleOwnedOp1152
import R1Z.PV_RunJoin_CircleOwnedScalar52
import R1Z.PV_RunJoin_CircleRawTower52
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleOwnedOps52
open PV_RunJoin_CircleOwnedCarrier52
attribute [local irreducible] encCM encQ
theorem op12 (x : CM) :
    PV_AL_CircleOwned.aspis_core.field.mul_by_r (encCM x) = (do let x ← PV_RunJoin_CircleRawTower52.field.mul_by_r x; ok (encCM x)) := by
  unfold PV_AL_CircleOwned.aspis_core.field.mul_by_r PV_RunJoin_CircleRawTower52.field.mul_by_r
  simp only [PV_RunJoin_CircleOwnedScalar52.f14,PV_RunJoin_CircleOwnedScalar52.f15,PV_RunJoin_CircleOwnedScalar52.f17,bind_assoc_eq,bind_tc_ok,PV_RunJoin_CircleOwnedProjection52.cm_a,PV_RunJoin_CircleOwnedProjection52.cm_b,PV_RunJoin_CircleOwnedProjection52.q_c0,PV_RunJoin_CircleOwnedProjection52.q_c1]

  all_goals simp only [encCM,encQ]
  all_goals rfl

#print axioms op12
end R1Z.PV_RunJoin_CircleOwnedOps52
