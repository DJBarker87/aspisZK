from pathlib import Path
L=Path('docs/research/v8-r0-zk-20261009/lean/R1Z')
raw=(L/'PV_RunJoin_CircleRawMap52.lean').read_text();body=raw.split('def map_parameter',1)[1].split('\ndef FALLBACK',1)[0]
s='''import R1Z.PV_RunJoin_CircleRawMap52
import R1Z.PV_RunJoin_CircleR72Raw52
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleMapPrograms54
abbrev Q := (U32 × U32) × (U32 × U32)
abbrev Point := Q × Q
'''
s+='def run'+body.replace('PV_RunJoin_CircleRawTower52.field.','PV_RunJoin_CircleR72Raw52.field.')
s+='''
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
'''
(L/'PV_RunJoin_CircleMapPrograms54.lean').write_text(s)
