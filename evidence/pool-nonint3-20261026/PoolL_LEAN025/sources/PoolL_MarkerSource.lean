import PoolM_NativeCancelSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolL_MarkerSource
open Aeneas Aeneas.Std Result PoolM_NativeCancelSource
/- AENEAS006 native metadata prefix, exact body, canonical imported SDK types.
   SDK/PDA/borrow and enclosing handler instantiation remain separate. -/
def PoolL_marker_header
  (marker_account : solana_account_info.AccountInfo) :
  Result (core.result.Result Unit solana_program_error.ProgramError)
  := do
  if marker_account.executable
  then
    let pe ←
      core.convert.IntoFrom.into
        solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError
        error.PoolV1ProgramError.InvalidNullifierMarkerAccount
    ok (core.result.Result.Err pe)
  else
    if marker_account.is_signer
    then
      let pe ←
        core.convert.IntoFrom.into
          solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError
          error.PoolV1ProgramError.InvalidNullifierMarkerAccount
      ok (core.result.Result.Err pe)
    else
      if marker_account.is_writable
      then ok (core.result.Result.Ok ())
      else
        let pe ←
          core.convert.IntoFrom.into
            solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError
            error.PoolV1ProgramError.InvalidNullifierMarkerAccount
        ok (core.result.Result.Err pe)
end AspisR1.PoolL_MarkerSource
end
