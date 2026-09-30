-- Generated R98 public entry; exact old types/loops checked by stage_r98_entry.py.
import AspisR86Query.Loops
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
namespace AspisR86Query
/-- [aspis_core::transcript::{aspis_core::transcript::Transcript}::challenge_queries_without_replacement]:
    Source: 'src/transcript.rs', lines 500:4-539:5
    Visibility: public -/
def transcript.Transcript.challenge_queries_without_replacement
  (self : transcript.Transcript) (count : Std.Usize) (bound : Std.U32)
  (max_draws : Std.Usize) :
  Result ((core.result.Result (alloc.vec.Vec Std.U32)
    transcript.QuerySampleError) × transcript.Transcript)
  := do
  if bound = 0#u32
  then
    ok (core.result.Result.Err (transcript.QuerySampleError.BoundNotPowerOfTwo
      bound), self)
  else
    let i ← bound - 1#u32
    let i1 ← lift (bound &&& i)
    if i1 != 0#u32
    then
      ok (core.result.Result.Err
        (transcript.QuerySampleError.BoundNotPowerOfTwo bound), self)
    else
      let i2 ← lift (UScalar.cast .Usize bound)
      if count > i2
      then
        ok (core.result.Result.Err
          (transcript.QuerySampleError.CountExceedsBound count bound), self)
      else
        if count = 0#usize
        then ok (core.result.Result.Ok (alloc.vec.Vec.new Std.U32), self)
        else
          let out := alloc.vec.Vec.with_capacity Std.U32 count
          let (self1, out1) ←
            transcript.Transcript.challenge_queries_without_replacement_loop0
              self count max_draws i out 0#usize
          let i3 := alloc.vec.Vec.len out1
          if i3 = count
          then ok (core.result.Result.Ok out1, self1)
          else
            let i4 := alloc.vec.Vec.len out1
            ok (core.result.Result.Err
              (transcript.QuerySampleError.DrawLimitExhausted i4 max_draws),
              self1)

/-- [aspis_core::query_probe]:
    Source: 'src/lib.rs', lines 94:0-97:1
    Visibility: public -/
def query_probe
  (t : transcript.Transcript) :
  Result ((core.result.Result (alloc.vec.Vec Std.U32)
    transcript.QuerySampleError) × transcript.Transcript)
  := do
  let i ← 1#u32 <<< 18#i32
  transcript.Transcript.challenge_queries_without_replacement t 22#usize i
    64#usize

end AspisR86Query
