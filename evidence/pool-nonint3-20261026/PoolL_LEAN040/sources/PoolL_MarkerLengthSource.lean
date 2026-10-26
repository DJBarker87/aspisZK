import PoolL_LengthSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolL_MarkerLengthSource
open Aeneas Aeneas.Std Result PoolM_NativeCancelSource
/- AENEAS007: length disjunct or explicit borrowed-data cut; actual SDK association remains open. -/
def PoolL_marker_length
  (data : Slice Std.U8) :
  Result (core.result.Result Unit solana_program_error.ProgramError)
  := do
  let i := Slice.len data
  if i != 208#usize
  then
    let pe ←
      core.convert.IntoFrom.into
        solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError
        error.PoolV1ProgramError.InvalidNullifierMarkerAccount
    ok (core.result.Result.Err pe)
  else ok (core.result.Result.Ok ())
end AspisR1.PoolL_MarkerLengthSource
end
