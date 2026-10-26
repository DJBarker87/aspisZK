import PoolL_FreshRoleSource
import PoolM_NativeCancelGuard
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolL_FreshRoleControl
open Aeneas Aeneas.Std Result PoolL_FreshRoleSource
abbrev Account := AdapterRw.Cuts.Account
abbrev Key := AdapterRw.solana_pubkey.Pubkey
abbrev Error := AdapterRw.solana_program_error.ProgramError
local instance : DecidableEq Key := Classical.decEq _

theorem control (a : Account) (id expected system : Key) (empty : Bool)
    (data : core.result.Result (Slice U8) Error) (size : Usize) :
    PoolL_fresh_role a id expected system empty data size =
      PoolM_NativeCancelGuard.thenResult (PoolL_FreshSource.PoolL_fresh_header a expected)
        (if a.owner = id then
          match data with
          | .Ok bytes => PoolL_FreshLengthSource.PoolL_fresh_length bytes size
          | .Err e => ok (.Err e)
        else if a.owner = system ∧ empty = true then ok (.Ok ())
        else ok (.Err (.Custom 1095966773#u32))) := by
  unfold PoolL_fresh_role PoolM_NativeCancelGuard.thenResult
  cases h : PoolL_FreshSource.PoolL_fresh_header a expected with
  | fail e => simp
  | div => simp
  | ok r =>
    cases r with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame]
    | Ok u =>
      cases u
      by_cases ho : a.owner = id <;> by_cases hs : a.owner = system <;>
        cases empty <;> cases data <;>
        simp [ho,hs,core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame,
          PoolM_NativeCancelSource.solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey.eq,
          Hist_Authority.keyEq,
          PoolM_NativeCancelSource.solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError.from]
#print axioms control
end AspisR1.PoolL_FreshRoleControl
end
