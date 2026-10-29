import R1Z.PV_RunJoin_CircleOwnedOp2052
import R1Z.PV_RunJoin_CircleOwnedScalar52
import R1Z.PV_RunJoin_CircleRawTower52
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleOwnedOps52
open PV_RunJoin_CircleOwnedCarrier52
attribute [local irreducible] encCM encQ
theorem op21 (self : Q) :
    PV_AL_CircleOwned.aspis_core.field.QM31.try_inv (encQ self) = (do let x ← PV_RunJoin_CircleRawTower52.field.QM31.try_inv self; ok ((Option.map encQ) x)) := by
  unfold PV_AL_CircleOwned.aspis_core.field.QM31.try_inv PV_RunJoin_CircleRawTower52.field.QM31.try_inv
  rw [op20]
  simp only [bind_assoc_eq,bind_tc_ok]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro zero _
  cases zero with
  | true => rfl
  | false =>
    simp only [Bool.false_eq_true,if_false]
    simp only [PV_RunJoin_CircleOwnedProjection52.q_c0,PV_RunJoin_CircleOwnedProjection52.q_c1,
      op8,op12,op5,op11,op7,op6,bind_assoc_eq,bind_tc_ok,Option.map_some]
    all_goals simp only [encQ]
    all_goals rfl

#print axioms op21
end R1Z.PV_RunJoin_CircleOwnedOps52
