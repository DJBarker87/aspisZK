import NGJ_VERIFIER_IMPORT
set_option autoImplicit false
noncomputable section
namespace NGL_CloneDomain
open Aeneas Aeneas.Std Result
abbrev PE := AdapterRw.solana_program_error.ProgramError
abbrev Account := AdapterRw.r1_pool_adapter.owned.OwnedAccount
/-- Snapshot's only deferred error carriers; no arbitrary Borsh string is assumed. -/
def SnapshotError (e : PE) : Prop := e = .AccountBorrowFailed ∨ e = .InvalidAccountData
/-- The concrete pure error-clone interpretation; native certificates are restricted
    to SnapshotError, not the arbitrary String-containing ProgramError domain. -/
def install (ops : AdapterRw.Ops) : AdapterRw.Ops := {ops with op35 := fun e => ok e}

theorem clone (ops : AdapterRw.Ops) (e : PE) : (install ops).op35 e = ok e := rfl

theorem length_result (ops : AdapterRw.Ops) (a : Account) :
    AdapterRw.r1_pool_adapter.owned.OwnedAccount.data_len (install ops) a = ok a.length := by
  cases h : a.length with
  | Ok n => simp only [AdapterRw.r1_pool_adapter.owned.OwnedAccount.data_len,
      AdapterRw.core.result.Result.Insts.CoreCloneClone.clone, h,
      AdapterRw.solana_program_error.ProgramError.Insts.CoreCloneClone,
      core.clone.CloneUsize, bind_tc_ok]
  | Err e => simp only [AdapterRw.r1_pool_adapter.owned.OwnedAccount.data_len,
      AdapterRw.core.result.Result.Insts.CoreCloneClone.clone, h,
      AdapterRw.solana_program_error.ProgramError.Insts.CoreCloneClone, install, bind_tc_ok]

theorem data_result (ops : AdapterRw.Ops) (a : Account) :
    AdapterRw.r1_pool_adapter.owned.OwnedAccount.data (install ops) a =
      ok (match a.bytes with | .Ok v => .Ok v.deref | .Err e => .Err e) := by
  cases h : a.bytes <;>
    simp only [AdapterRw.r1_pool_adapter.owned.OwnedAccount.data, h, install, bind_tc_ok]

#print axioms clone
#print axioms length_result
#print axioms data_result
end NGL_CloneDomain
