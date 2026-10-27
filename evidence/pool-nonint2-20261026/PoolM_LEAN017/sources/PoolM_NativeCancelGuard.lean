import PoolM_NativeCancelSource
import PoolM_NativePlanGuard
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolM_NativeCancelGuard
open Aeneas Aeneas.Std Result
open PoolM_NativeCancelSource
abbrev Account := AdapterRw.Cuts.Account
abbrev Key := AdapterRw.solana_pubkey.Pubkey
abbrev Error := AdapterRw.solana_program_error.ProgramError

/-- The native extracted guard and the canonical short-circuit interpretation
are definitionally the same after binding only the two external SDK leaves. -/
theorem prepared_eq (readLength : Account → Result Usize) (a : Account)
    (id : Key) (size : Usize) :
    require_prepared_plan_account_v1 readLength a id size =
      PoolM_NativePlanGuard.run a id size (readLength a)  := by
  simp [require_prepared_plan_account_v1,PoolM_NativePlanGuard.run,
    Hiq_PoolSource.keyNe,core.cmp.impls.PartialEqShared.ne,
    core.cmp.PartialEq.ne.default,
    solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey,
    solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey.eq]

/-- Control form of Rust's ProgramResult `?`, retaining interpreter failure
and divergence as well as the exact ProgramError. -/
def thenResult (check : Result (core.result.Result Unit Error))
    (next : Result (core.result.Result Unit Error)) :
    Result (core.result.Result Unit Error) := do
  let result ← check
  match result with
  | .Err e => ok (.Err e)
  | .Ok _ => next

def suffix (readLength : Account → Result Usize) (id : Key)
    (coreAcc shard : Account) (hasShard : Bool) : Result (core.result.Result Unit Error) :=
  thenResult (require_prepared_plan_account_v1 readLength coreAcc id 10000#usize)
    (if hasShard then
      thenResult (require_prepared_plan_account_v1 readLength shard id 8504#usize) (ok (.Ok ()))
    else ok (.Ok ()))

/-- All role guards and errors of the extracted native role cut. This theorem
binds no opaque arithmetic child or successful parser result. -/
theorem native_control (readLength : Account → Result Usize) (system id : Key)
    (payer coreAcc shard : Account) (hasShard : Bool) :
    PoolM_cancel_roles_native readLength system id payer coreAcc shard hasShard =
      (if !payer.is_signer || !payer.is_writable || payer.executable then
        ok (.Err (.Custom 1095966772#u32))
      else do
        let foreign ← Hiq_PoolSource.keyNe payer.owner system
        if foreign then ok (.Err (.Custom 1095966772#u32)) else
          suffix readLength id coreAcc shard hasShard) := by
  classical
  by_cases owner : payer.owner = system <;>
    cases hs : payer.is_signer <;> cases hw : payer.is_writable <;>
    cases he : payer.executable <;>
    simp [PoolM_cancel_roles_native,suffix,thenResult,hs,hw,he,owner,Hist_Authority.keyEq,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame,
      solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError,
      solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError.from,
      POOL_V1_PREPARED_SETTLEMENT_CORE_ACCOUNT_BYTES,
      POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_ACCOUNT_BYTES,
      Hiq_PoolSource.keyNe,core.cmp.impls.PartialEqShared.ne,
      core.cmp.PartialEq.ne.default,solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey,
      solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey.eq]
  all_goals
    intro v hv
    cases v <;> simp_all
  all_goals
    intro v hv
    cases v <;> simp_all

#print axioms prepared_eq
#print axioms native_control
end AspisR1.PoolM_NativeCancelGuard
end
