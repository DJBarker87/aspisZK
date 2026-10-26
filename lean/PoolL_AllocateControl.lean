import PoolL_AllocateSource
import PoolM_NativeCancelGuard
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolL_AllocateControl
open Aeneas Aeneas.Std Result PoolL_AllocateSource
abbrev Account := AdapterRw.Cuts.Account
abbrev Key := AdapterRw.solana_pubkey.Pubkey
local instance : DecidableEq Key := Classical.decEq _

/-- Both native allocation helpers use this identical first-CPI cut. -/
theorem control (empty : Account → Result Bool) (system loader : Key)
    (payer a sys : Account) :
    allocatePrefix empty system loader payer a sys =
      PoolM_NativeCancelGuard.thenResult (payerSystem system loader payer sys)
        (if a.owner ≠ system then
          ok (core.result.Result.Err (.Custom 1095966773#u32))
        else do
          let b ← empty a
          if b then ok (core.result.Result.Ok ())
          else ok (core.result.Result.Err (.Custom 1095966773#u32))) := by
  classical
  unfold allocatePrefix PoolM_NativeCancelGuard.thenResult
  cases hp : payerSystem system loader payer sys with
  | fail e => simp
  | div => simp
  | ok r =>
    cases r with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame]
    | Ok u =>
      cases u
      by_cases owner : a.owner = system <;>
        simp [owner,core.result.Result.Insts.CoreOpsTry.branch,
          PoolM_NativeCancelSource.solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey.eq,
          core.cmp.impls.PartialEqShared.ne,core.cmp.PartialEq.ne.default,Hist_Authority.keyEq,
          PoolM_NativeCancelSource.solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError.from]

#print axioms control
end AspisR1.PoolL_AllocateControl
end
