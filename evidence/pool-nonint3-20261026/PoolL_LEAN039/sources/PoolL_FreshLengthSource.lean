import PoolL_LengthSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolL_FreshLengthSource
open Aeneas Aeneas.Std Result PoolM_NativeCancelSource
/- AENEAS007: length disjunct or explicit borrowed-data cut; actual SDK association remains open. -/
def PoolL_fresh_length
  (data : Slice Std.U8) (expected : Std.Usize) :
  Result (core.result.Result Unit solana_program_error.ProgramError)
  := do
  let i := Slice.len data
  if i != expected
  then
    let pe ←
      core.convert.IntoFrom.into
        solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError
        error.PoolV1ProgramError.InvalidFreshAccount
    ok (core.result.Result.Err pe)
  else ok (core.result.Result.Ok ())
end AspisR1.PoolL_FreshLengthSource
end
