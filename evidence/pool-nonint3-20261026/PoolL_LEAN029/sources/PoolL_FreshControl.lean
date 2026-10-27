import PoolL_FreshSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolL_FreshControl
open Aeneas Aeneas.Std Result PoolL_FreshSource
abbrev Account := AdapterRw.Cuts.Account
abbrev Key := AdapterRw.solana_pubkey.Pubkey
local instance : DecidableEq Key := Classical.decEq _
theorem control (a : Account) (expected : Key) :
    PoolL_fresh_header a expected = (if a.key ≠ expected ∨ a.executable = true ∨ a.is_signer = true ∨ a.is_writable = false then ok (.Err (.Custom 1095966773#u32)) else ok (.Ok ())) := by
  classical
  by_cases hk : a.key = expected <;> cases he : a.executable <;> cases hs : a.is_signer <;> cases hw : a.is_writable <;>
    simp [PoolL_fresh_header,hk,he,hs,hw,
      PoolM_NativeCancelSource.solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey.eq,
      core.cmp.impls.PartialEqShared.ne,core.cmp.PartialEq.ne.default,Hist_Authority.keyEq,
      PoolM_NativeCancelSource.solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError.from]
#print axioms control
end AspisR1.PoolL_FreshControl
end
