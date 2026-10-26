import PoolL_MarkerSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolL_MarkerControl
open Aeneas Aeneas.Std Result PoolL_MarkerSource
abbrev Account := AdapterRw.Cuts.Account
abbrev Key := AdapterRw.solana_pubkey.Pubkey
local instance : DecidableEq Key := Classical.decEq _
theorem control (a : Account) :
    PoolL_marker_header a = (if a.executable = true ∨ a.is_signer = true ∨ a.is_writable = false then ok (.Err (.Custom 1095966757#u32)) else ok (.Ok ())) := by
  classical
  cases he : a.executable <;> cases hs : a.is_signer <;> cases hw : a.is_writable <;>
    simp [PoolL_marker_header,he,hs,hw,
      PoolM_NativeCancelSource.solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey.eq,
      core.cmp.impls.PartialEqShared.ne,core.cmp.PartialEq.ne.default,Hist_Authority.keyEq,
      PoolM_NativeCancelSource.solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError.from]
#print axioms control
end AspisR1.PoolL_MarkerControl
end
