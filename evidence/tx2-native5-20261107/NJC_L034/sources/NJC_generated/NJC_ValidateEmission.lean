import Aeneas
import NID_ResumeEmissionTypes
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
noncomputable section
namespace NJC_ValidateEmission
open NID_ResumeEmission
abbrev verifier.Error := NID_ResumeEmission.verifier.Error

/-- [aspis_r1_cost_probe::verifier::validate_checkpoint_queries]: loop body 0:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 354:4-360:1 -/
@[rust_loop_body]
def verifier.validate_checkpoint_queries_loop.body
  (queries : Array Std.U32 22#usize) (i : Std.Usize) :
  Result (ControlFlow Std.Usize (Option (core.result.Result Unit
    verifier.Error)))
  := do
  let s ← lift (Array.to_slice queries)
  let i1 := Slice.len s
  if i < i1
  then
    let q ← Array.index_usize queries i
    let i2 ← 1#u32 <<< 18#i32
    if q >= i2
    then ok (done none)
    else
      let s1 ←
        core.array.Array.index (core.ops.index.IndexSlice
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U32)) queries
          { «end» := i }
      let b ← core.slice.Slice.contains core.cmp.PartialEqU32 s1 q
      if b
      then ok (done none)
      else let i3 ← i + 1#usize
           ok (cont i3)
  else ok (done (some (core.result.Result.Ok ())))

/-- [aspis_r1_cost_probe::verifier::validate_checkpoint_queries]: loop 0:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 354:4-360:1 -/
@[rust_loop]
def verifier.validate_checkpoint_queries_loop
  (queries : Array Std.U32 22#usize) (i : Std.Usize) :
  Result (Option (core.result.Result Unit verifier.Error))
  := do
  loop
    (fun i1 => verifier.validate_checkpoint_queries_loop.body queries i1)
    i

/-- [aspis_r1_cost_probe::verifier::validate_checkpoint_queries]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 352:0-360:1 -/
def verifier.validate_checkpoint_queries
  (queries : Array Std.U32 22#usize) :
  Result (core.result.Result Unit verifier.Error)
  := do
  let pending_return ←
    verifier.validate_checkpoint_queries_loop queries 0#usize
  match pending_return with
  | none => ok (core.result.Result.Err verifier.Error.Checkpoint)
  | some r => ok r


end NJC_ValidateEmission
