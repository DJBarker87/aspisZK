import PoolM_NativeCancelSource
import PoolL_ProgramSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolL_CanonicalSource
open Aeneas Aeneas.Std Result PoolM_NativeCancelSource
/- AENEAS006 native metadata prefix, exact body, canonical imported SDK types.
   SDK/PDA/borrow and enclosing handler instantiation remain separate. -/
def PoolL_canonical_header
  (account : solana_account_info.AccountInfo)
  (program_id : solana_pubkey.Pubkey) :
  Result (core.result.Result Unit solana_program_error.ProgramError)
  := do
  let r ← PoolL_ProgramSource.require_program_account account program_id true
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    if account.is_signer
    then
      ok (core.result.Result.Err
        AdapterRw.solana_program_error.ProgramError.InvalidAccountData)
    else ok (core.result.Result.Ok ())
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame solana_program_error.ProgramError) residual
end AspisR1.PoolL_CanonicalSource
end
