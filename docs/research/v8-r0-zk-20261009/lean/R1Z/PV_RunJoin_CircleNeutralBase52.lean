import R1Z.PV_RunJoin_CircleRawTower52
import R1Z.PV_RunJoin_CircleR72Raw52
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RunJoin_CircleNeutralBase52
abbrev CM := U32 × U32
abbrev Q := CM × CM

theorem modulus : PV_RunJoin_CircleRawTower52.field.P = PV_RunJoin_CircleR72Raw52.field.P := rfl

theorem mzero (a : U32) : PV_RunJoin_CircleRawTower52.field.M31.is_zero a =
    PV_RunJoin_CircleR72Raw52.field.M31.is_zero a := by
  unfold PV_RunJoin_CircleRawTower52.field.M31.is_zero PV_RunJoin_CircleRawScalar52.field.M31.is_zero
    PV_RunJoin_CircleR72Raw52.field.M31.is_zero PV_RunJoin_CircleRawScalar52.field.ct.is_zero
  rfl

theorem czero (a : CM) : PV_RunJoin_CircleRawTower52.field.CM31.is_zero a =
    PV_RunJoin_CircleR72Raw52.field.CM31.is_zero a := by
  unfold PV_RunJoin_CircleRawTower52.field.CM31.is_zero PV_RunJoin_CircleR72Raw52.field.CM31.is_zero
  simp only [mzero]

theorem qzero (a : Q) : PV_RunJoin_CircleRawTower52.field.QM31.is_zero a =
    PV_RunJoin_CircleR72Raw52.field.QM31.is_zero a := by
  unfold PV_RunJoin_CircleRawTower52.field.QM31.is_zero PV_RunJoin_CircleR72Raw52.field.QM31.is_zero
  simp only [czero]

theorem meq (a b : U32) : PV_RunJoin_CircleRawTower52.field.M31.Insts.CoreCmpPartialEqM31.eq a b =
    PV_RunJoin_CircleR72Raw52.field.M31.Insts.CoreCmpPartialEqM31.eq a b := rfl

theorem ceq (a b : CM) : PV_RunJoin_CircleRawTower52.field.CM31.Insts.CoreCmpPartialEqCM31.eq a b =
    PV_RunJoin_CircleR72Raw52.field.CM31.Insts.CoreCmpPartialEqCM31.eq a b := by
  unfold PV_RunJoin_CircleRawTower52.field.CM31.Insts.CoreCmpPartialEqCM31.eq
    PV_RunJoin_CircleR72Raw52.field.CM31.Insts.CoreCmpPartialEqCM31.eq
  simp only [meq]

theorem cnew (a b : U32) : PV_RunJoin_CircleRawTower52.field.CM31.new a b =
    PV_RunJoin_CircleR72Raw52.field.CM31.new a b := rfl

theorem cone : PV_RunJoin_CircleRawTower52.field.QM31.ONE = PV_RunJoin_CircleR72Raw52.field.QM31.ONE := rfl

theorem cnull : PV_RunJoin_CircleRawTower52.field.CM31.ZERO = PV_RunJoin_CircleR72Raw52.field.CM31.ZERO := rfl

#print axioms modulus
#print axioms mzero
#print axioms czero
#print axioms qzero
#print axioms meq
#print axioms ceq
#print axioms cnew
#print axioms cone
#print axioms cnull
end R1Z.PV_RunJoin_CircleNeutralBase52
