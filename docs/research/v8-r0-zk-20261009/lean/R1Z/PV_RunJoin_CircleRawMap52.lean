import R1Z.PV_RunJoin_CircleRawSampler52
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleRawMap52
abbrev Q := PV_RunJoin_CircleRawTower52.field.QM31
abbrev Point := Q × Q
abbrev shipped_sampler.qm31_sample := PV_RunJoin_CircleRawSampler52.shipped_sampler.qm31_sample
def map_parameter
  (parameter1 : PV_RunJoin_CircleRawTower52.field.QM31) :
  Result (core.result.Result Point
    Bool)
  := do
  let square ← PV_RunJoin_CircleRawTower52.field.QM31.square parameter1
  let q ← PV_RunJoin_CircleRawTower52.field.QM31.add PV_RunJoin_CircleRawTower52.field.QM31.ONE square
  let o ← PV_RunJoin_CircleRawTower52.field.QM31.try_inv q
  match o with
  | none =>
    ok (core.result.Result.Err
      false)
  | some value =>
    let q1 ← PV_RunJoin_CircleRawTower52.field.QM31.sub PV_RunJoin_CircleRawTower52.field.QM31.ONE square
    let q2 ← PV_RunJoin_CircleRawTower52.field.QM31.mul q1 value
    let q3 ← PV_RunJoin_CircleRawTower52.field.QM31.add parameter1 parameter1
    let q4 ← PV_RunJoin_CircleRawTower52.field.QM31.mul q3 value
    let b ←
      PV_RunJoin_CircleRawTower52.field.CM31.Insts.CoreCmpPartialEqCM31.eq parameter1.snd
        PV_RunJoin_CircleRawTower52.field.CM31.ZERO
    if b
    then
      ok (core.result.Result.Err
        true)
    else ok (core.result.Result.Ok { fst := q2, snd := q4 })

def FALLBACK : Array PV_RunJoin_CircleRawTower52.field.QM31 2#usize :=
  Array.make 2#usize [
    { fst := PV_RunJoin_CircleRawTower52.field.CM31.ZERO, snd := PV_RunJoin_CircleRawTower52.field.CM31.ONE },
    { fst := PV_RunJoin_CircleRawTower52.field.CM31.ONE, snd := PV_RunJoin_CircleRawTower52.field.CM31.ONE }
    ]

def fallback
  (sample : Std.Usize) : Result Point := do
  let i ← sample % 2#usize
  let parameter1 ← Array.index_usize FALLBACK i
  let r ← map_parameter parameter1
  match r with
  | core.result.Result.Ok point => ok point
  | core.result.Result.Err _ =>
    ok { fst := PV_RunJoin_CircleRawTower52.field.QM31.ONE, snd := PV_RunJoin_CircleRawTower52.field.QM31.ZERO }

def circle_owned
  (block : Array Std.U8 32#usize) (row : Bool) :
  Result Point
  := do
  let parameter1 ← shipped_sampler.qm31_sample block
  let r ← map_parameter parameter1
  match r with
  | core.result.Result.Ok point => ok point
  | core.result.Result.Err _ =>
    match row with
    | false => fallback 0#usize
    | true => fallback 1#usize
#print axioms map_parameter
#print axioms FALLBACK
#print axioms fallback
#print axioms circle_owned
end R1Z.PV_RunJoin_CircleRawMap52
