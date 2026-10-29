import R1Z.PV_RunJoin_CircleOwnedOp1052
import R1Z.PV_RunJoin_CircleOwnedScalar52
import R1Z.PV_RunJoin_CircleRawTower52
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleOwnedOps52
open PV_RunJoin_CircleOwnedCarrier52
attribute [local irreducible] encCM encQ
theorem op11 (self : CM) :
    PV_AL_CircleOwned.aspis_core.field.CM31.inv (encCM self) = (do let x ← PV_RunJoin_CircleRawTower52.field.CM31.inv self; ok (encCM x)) := by
  unfold PV_AL_CircleOwned.aspis_core.field.CM31.inv PV_RunJoin_CircleRawTower52.field.CM31.inv
  have hi : PV_AL_CircleOwned.aspis_core.field.M31.inv = PV_RunJoin_CircleRawTower52.field.M31.inv :=
    funext PV_RunJoin_CircleOwnedScalar52.f16
  rw [hi]
  exact op10 self PV_RunJoin_CircleRawTower52.field.M31.inv

#print axioms op11
end R1Z.PV_RunJoin_CircleOwnedOps52
