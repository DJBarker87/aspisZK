import PoolL_CanonicalRoleSource
import PoolM_NativeCancelGuard
set_option autoImplicit false
namespace AspisR1.PoolL_CanonicalRoleControl
open Aeneas Aeneas.Std Result PoolL_CanonicalRoleSource
abbrev Account := AdapterRw.Cuts.Account
abbrev Key := AdapterRw.solana_pubkey.Pubkey
abbrev Error := AdapterRw.solana_program_error.ProgramError

theorem control (a : Account) (id : Key) (data : core.result.Result (Slice U8) Error) :
    PoolL_canonical_role a id data =
      PoolM_NativeCancelGuard.thenResult (PoolL_CanonicalSource.PoolL_canonical_header a id)
        (PoolL_BorrowSource.PoolL_borrow_length data 1000#usize) := by
  unfold PoolL_canonical_role PoolM_NativeCancelGuard.thenResult
  cases h : PoolL_CanonicalSource.PoolL_canonical_header a id with
  | fail e => simp
  | div => simp
  | ok r => cases r with
    | Ok u => cases u; simp [core.result.Result.Insts.CoreOpsTry.branch]
    | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame]
#print axioms control
end AspisR1.PoolL_CanonicalRoleControl
