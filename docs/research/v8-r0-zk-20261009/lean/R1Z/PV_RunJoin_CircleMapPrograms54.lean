import R1Z.PV_RunJoin_CircleRawMap52
import R1Z.PV_RunJoin_CircleR72Raw52
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleMapPrograms54
abbrev Q := (U32 × U32) × (U32 × U32)
abbrev Point := Q × Q
def run
  (parameter1 : PV_RunJoin_CircleR72Raw52.field.QM31) :
  Result (core.result.Result Point
    Bool)
  := do
  let square ← PV_RunJoin_CircleR72Raw52.field.QM31.square parameter1
  let q ← PV_RunJoin_CircleR72Raw52.field.QM31.add PV_RunJoin_CircleR72Raw52.field.QM31.ONE square
  let o ← PV_RunJoin_CircleR72Raw52.field.QM31.try_inv q
  match o with
  | none =>
    ok (core.result.Result.Err
      false)
  | some value =>
    let q1 ← PV_RunJoin_CircleR72Raw52.field.QM31.sub PV_RunJoin_CircleR72Raw52.field.QM31.ONE square
    let q2 ← PV_RunJoin_CircleR72Raw52.field.QM31.mul q1 value
    let q3 ← PV_RunJoin_CircleR72Raw52.field.QM31.add parameter1 parameter1
    let q4 ← PV_RunJoin_CircleR72Raw52.field.QM31.mul q3 value
    let b ←
      PV_RunJoin_CircleR72Raw52.field.CM31.Insts.CoreCmpPartialEqCM31.eq parameter1.snd
        PV_RunJoin_CircleR72Raw52.field.CM31.ZERO
    if b
    then
      ok (core.result.Result.Err
        true)
    else ok (core.result.Result.Ok { fst := q2, snd := q4 })

theorem owned (a : Q) : PV_RunJoin_CircleRawMap52.map_parameter a = (do
  let square ← PV_RunJoin_CircleRawTower52.field.QM31.square a
  let q ← PV_RunJoin_CircleRawTower52.field.QM31.add PV_RunJoin_CircleRawTower52.field.QM31.ONE square
  let inverse ← PV_RunJoin_CircleRawTower52.field.QM31.try_inv q
  match inverse with
  | none => ok (core.result.Result.Err false)
  | some inv =>
    let numerator ← PV_RunJoin_CircleRawTower52.field.QM31.sub PV_RunJoin_CircleRawTower52.field.QM31.ONE square
    let x ← PV_RunJoin_CircleRawTower52.field.QM31.mul numerator inv
    let doubled ← PV_RunJoin_CircleRawTower52.field.QM31.add a a
    let y ← PV_RunJoin_CircleRawTower52.field.QM31.mul doubled inv
    let subfield ← PV_RunJoin_CircleRawTower52.field.CM31.Insts.CoreCmpPartialEqCM31.eq a.2 PV_RunJoin_CircleRawTower52.field.CM31.ZERO
    if subfield then ok (.Err true) else ok (.Ok (x,y))) := rfl
#print axioms run
#print axioms owned
end R1Z.PV_RunJoin_CircleMapPrograms54
