import R1Z.PV_RunJoin_CircleMapPrograms54
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleFallbackPrograms54
abbrev Q := (U32 × U32) × (U32 × U32)
abbrev Point := Q × Q

def fallback (sample : Usize) : Result Point := do
  let i ← sample % 2#usize
  let parameter ← Array.index_usize PV_RunJoin_CircleRawMap52.FALLBACK i
  let r ← PV_RunJoin_CircleMapPrograms54.run parameter
  match r with
  | .Ok p => ok p
  | .Err _ => ok (PV_RunJoin_CircleRawTower52.field.QM31.ONE,PV_RunJoin_CircleRawTower52.field.QM31.ZERO)

def circle (block : Array U8 32#usize) (row : Bool) : Result Point := do
  let parameter ← PV_RunJoin_CircleRawSampler52.shipped_sampler.qm31_sample block
  let r ← PV_RunJoin_CircleMapPrograms54.run parameter
  match r with
  | .Ok p => ok p
  | .Err _ => if row then fallback 1#usize else fallback 0#usize
#print axioms fallback
#print axioms circle
end R1Z.PV_RunJoin_CircleFallbackPrograms54
