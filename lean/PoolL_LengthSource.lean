import PoolM_NativeCancelSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolL_LengthSource
open Aeneas Aeneas.Std Result PoolM_NativeCancelSource
/- AENEAS004 source cut; first disjunct only. Full decoder coupling is separate. -/
/-- [pooll_slice::PoolL_length_prefix]:
    Source: 'PoolL_lib.rs', lines 76:0-81:1
    Visibility: public -/
def lengthPrefix
  (data : Slice Std.U8) (expected : Std.Usize) :
  Result (core.result.Result Unit solana_program_error.ProgramError)
  := do
  let i := Slice.len data
  if i != expected
  then
    let pe ←
      core.convert.IntoFrom.into
        solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError
        error.PoolV1ProgramError.InvalidAccountType
    ok (core.result.Result.Err pe)
  else ok (core.result.Result.Ok ())

end AspisR1.PoolL_LengthSource
end
