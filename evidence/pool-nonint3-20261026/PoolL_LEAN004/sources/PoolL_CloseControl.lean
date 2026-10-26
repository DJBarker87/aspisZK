import PoolL_CloseSource
import PoolM_NativePlanGuard
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolL_CloseControl
open Aeneas Aeneas.Std Result PoolL_CloseSource
abbrev Account := AdapterRw.Cuts.Account
abbrev Key := AdapterRw.solana_pubkey.Pubkey
abbrev Error := AdapterRw.solana_program_error.ProgramError

/-- Exact native close guard; the length leaf runs only after all metadata. -/
theorem control (length : Account → Result Usize) (a refund : Account)
    (owner : Key) (size : Usize) :
    closePrefix length a refund owner size =
      (if a.owner ≠ owner ∨ a.executable = true ∨ a.is_signer = true ∨
          a.is_writable = false ∨ refund.key = a.key ∨ refund.is_writable = false then
        ok (core.result.Result.Err Error.InvalidAccountData)
      else do
        let n ← length a
        if n != size then ok (core.result.Result.Err Error.InvalidAccountData) else ok (core.result.Result.Ok ())) := by
  classical
  by_cases ho : a.owner = owner <;> by_cases hk : refund.key = a.key <;>
    cases he : a.executable <;> cases hs : a.is_signer <;>
    cases hw : a.is_writable <;> cases hr : refund.is_writable <;>
    simp [closePrefix,ho,hk,he,hs,hw,hr,
      PoolM_NativeCancelSource.solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey,
      PoolM_NativeCancelSource.solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey.eq,
      core.cmp.impls.PartialEqShared.ne,core.cmp.PartialEq.ne.default,Hist_Authority.keyEq]

#print axioms control
end AspisR1.PoolL_CloseControl
end
