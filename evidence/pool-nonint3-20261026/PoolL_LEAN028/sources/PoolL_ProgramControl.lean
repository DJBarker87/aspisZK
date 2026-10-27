import PoolL_ProgramSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolL_ProgramControl
open Aeneas Aeneas.Std Result PoolL_ProgramSource
abbrev Account := AdapterRw.Cuts.Account
abbrev Key := AdapterRw.solana_pubkey.Pubkey
local instance : DecidableEq Key := Classical.decEq _
theorem control (a : Account) (id : Key) (w : Bool) :
    require_program_account a id w = (if a.owner ≠ id then ok (.Err AdapterRw.solana_program_error.ProgramError.IncorrectProgramId) else if a.executable = true ∨ a.is_writable ≠ w then ok (.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData) else ok (.Ok ())) := by
  classical
  by_cases ho : a.owner = id <;> cases he : a.executable <;> cases hw : a.is_writable <;> cases w <;>
    simp [require_program_account,ho,he,hw,
      PoolM_NativeCancelSource.solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey.eq,
      core.cmp.impls.PartialEqShared.ne,core.cmp.PartialEq.ne.default,Hist_Authority.keyEq,
      PoolM_NativeCancelSource.solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError.from]
#print axioms control
end AspisR1.PoolL_ProgramControl
end
