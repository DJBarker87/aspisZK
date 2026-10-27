import PoolL_AllocateSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolL_PayerControl
open Aeneas Aeneas.Std Result PoolL_AllocateSource
abbrev Account := AdapterRw.Cuts.Account
abbrev Key := AdapterRw.solana_pubkey.Pubkey
local instance : DecidableEq Key := Classical.decEq _

/-- Native payer/System guard in source order; the two distinct errors survive. -/
theorem control (system loader : Key) (payer sys : Account) :
    payerSystem system loader payer sys =
      (if payer.is_signer = false ∨ payer.is_writable = false ∨ payer.executable = true ∨
          payer.owner ≠ system then
        ok (core.result.Result.Err (.Custom 1095966772#u32))
      else if sys.key ≠ system ∨ sys.owner ≠ loader ∨ sys.executable = false ∨
          sys.is_signer = true ∨ sys.is_writable = true then
        ok (core.result.Result.Err (.Custom 1095966771#u32))
      else ok (core.result.Result.Ok ())) := by
  classical
  by_cases hp : payer.owner = system <;> by_cases hk : sys.key = system <;>
    by_cases hl : sys.owner = loader <;>
    cases hs : payer.is_signer <;> cases hw : payer.is_writable <;>
    cases he : payer.executable <;> cases se : sys.executable <;>
    cases ss : sys.is_signer <;> cases sw : sys.is_writable <;>
    simp [payerSystem,hp,hk,hl,hs,hw,he,se,ss,sw,
      PoolM_NativeCancelSource.solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey.eq,
      core.cmp.impls.PartialEqShared.ne,core.cmp.PartialEq.ne.default,Hist_Authority.keyEq,
      PoolM_NativeCancelSource.solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError.from]

#print axioms control
end AspisR1.PoolL_PayerControl
end
