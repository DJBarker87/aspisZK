import R1Z.PV_RunJoin_CircleNeutralQInvBody53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralQInvEquation53
open PV_RunJoin_CircleNeutralShape53 PV_RunJoin_CircleNeutralResult53
abbrev C := U32 × U32
abbrev Q := C × C
attribute [local irreducible] PV_RunJoin_CircleRawTower52.field.CM31.mul PV_RunJoin_CircleRawTower52.field.CM31.neg PV_RunJoin_CircleRawTower52.field.CM31.inv PV_RunJoin_CircleRawTower52.field.CM31.square PV_RunJoin_CircleRawTower52.field.CM31.sub PV_RunJoin_CircleR72Raw52.field.CM31.mul PV_RunJoin_CircleR72Raw52.field.CM31.neg PV_RunJoin_CircleR72Raw52.field.CM31.inv PV_RunJoin_CircleR72Raw52.field.CM31.square PV_RunJoin_CircleR72Raw52.field.CM31.sub
theorem owned (a : Q) : PV_RunJoin_CircleRawTower52.field.QM31.try_inv a = (do
  let z ← PV_RunJoin_CircleRawTower52.field.QM31.is_zero a
  if z then ok none else PV_RunJoin_CircleNeutralQInvBody53.owned a) := by
  unfold PV_RunJoin_CircleRawTower52.field.QM31.try_inv PV_RunJoin_CircleNeutralQInvBody53.owned
    PV_RunJoin_CircleNeutralQInvTail53.owned
  rfl
theorem model (a : Q) : PV_RunJoin_CircleR72Raw52.field.QM31.try_inv a = (do
  let z ← PV_RunJoin_CircleR72Raw52.field.QM31.is_zero a
  if z then ok none else PV_RunJoin_CircleNeutralQInvBody53.model a) := by
  unfold PV_RunJoin_CircleR72Raw52.field.QM31.try_inv PV_RunJoin_CircleNeutralQInvBody53.model
    PV_RunJoin_CircleNeutralQInvTail53.model
  rfl

#print axioms owned
#print axioms model
end R1Z.PV_RunJoin_CircleNeutralQInvEquation53
