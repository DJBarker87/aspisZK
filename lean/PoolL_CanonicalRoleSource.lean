import PoolL_LengthSource
import PoolL_CanonicalSource
import PoolL_BorrowSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolL_CanonicalRoleSource
open Aeneas Aeneas.Std Result PoolM_NativeCancelSource
/- AENEAS007: length disjunct or explicit borrowed-data cut; actual SDK association remains open. -/
def PoolL_canonical_role
  (account : solana_account_info.AccountInfo)
  (program_id : solana_pubkey.Pubkey)
  (data : core.result.Result (Slice Std.U8) solana_program_error.ProgramError)
  :
  Result (core.result.Result Unit solana_program_error.ProgramError)
  := do
  let r ← PoolL_CanonicalSource.PoolL_canonical_header account program_id
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    PoolL_BorrowSource.PoolL_borrow_length data 1000#usize
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame solana_program_error.ProgramError) residual
end AspisR1.PoolL_CanonicalRoleSource
end
