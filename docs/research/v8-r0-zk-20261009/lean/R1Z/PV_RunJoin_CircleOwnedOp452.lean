import R1Z.PV_RunJoin_CircleOwnedOp352
import R1Z.PV_RunJoin_CircleOwnedScalar52
import R1Z.PV_RunJoin_CircleRawTower52
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleOwnedOps52
open PV_RunJoin_CircleOwnedCarrier52
attribute [local irreducible] encCM encQ
theorem op3 (a : U32) (b : U32) :
    PV_AL_CircleOwned.aspis_core.field.CM31.new a b = (do let x ← PV_RunJoin_CircleRawTower52.field.CM31.new a b; ok (encCM x)) := by
  unfold PV_AL_CircleOwned.aspis_core.field.CM31.new PV_RunJoin_CircleRawTower52.field.CM31.new
  simp only [bind_assoc_eq,bind_tc_ok,PV_RunJoin_CircleOwnedProjection52.cm_a,PV_RunJoin_CircleOwnedProjection52.cm_b,PV_RunJoin_CircleOwnedProjection52.q_c0,PV_RunJoin_CircleOwnedProjection52.q_c1]

  all_goals simp only [encCM,encQ]
  all_goals rfl

#print axioms op4
end R1Z.PV_RunJoin_CircleOwnedOps52
