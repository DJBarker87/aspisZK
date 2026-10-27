import PoolL_FreshSource
import PoolL_MarkerSource
import PoolL_FreshLengthSource
import PoolL_MarkerLengthSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolL_FreshRoleSource
open Aeneas Aeneas.Std Result PoolM_NativeCancelSource
/- AENEAS008 owned role cut. Native SDK data/System-ID/empty association is explicit, not discharged. -/
def PoolL_fresh_role
  (account : solana_account_info.AccountInfo)
  (program_id : solana_pubkey.Pubkey) (expected : solana_pubkey.Pubkey)
  (system : solana_pubkey.Pubkey) (empty : Bool)
  (data : core.result.Result (Slice Std.U8) solana_program_error.ProgramError)
  (size : Std.Usize) :
  Result (core.result.Result Unit solana_program_error.ProgramError)
  := do
  let r ← PoolL_FreshSource.PoolL_fresh_header account expected
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let b ←
      solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey.eq account.owner
        program_id
    if b
    then
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch data
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val =>
        PoolL_FreshLengthSource.PoolL_fresh_length val size
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          Unit (core.convert.FromSame solana_program_error.ProgramError)
          residual
    else
      let b1 ←
        solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey.eq account.owner
          system
      if b1
      then
        if empty
        then ok (core.result.Result.Ok ())
        else
          let pe ←
            core.convert.IntoFrom.into
              solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError
              error.PoolV1ProgramError.InvalidFreshAccount
          ok (core.result.Result.Err pe)
      else
        let pe ←
          core.convert.IntoFrom.into
            solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError
            error.PoolV1ProgramError.InvalidFreshAccount
        ok (core.result.Result.Err pe)
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame solana_program_error.ProgramError) residual
end AspisR1.PoolL_FreshRoleSource
end
