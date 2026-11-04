import NGL_CloneDomain
import NGL_ReadonlyModel
set_option autoImplicit false
noncomputable section
namespace NGL_CheckpointModel
open Aeneas Aeneas.Std Result
abbrev PE := AdapterRw.solana_program_error.ProgramError
abbrev Key := AdapterRw.solana_pubkey.Pubkey
abbrev Account := AdapterRw.r1_pool_adapter.owned.OwnedAccount

def install (ops : AdapterRw.Ops) : AdapterRw.Ops := by
  classical
  exact {ops with op35 := fun e => ok e, op36 := fun a b => ok (decide (a = b)),
    op12 := fun _ => ok 1768#usize}

def reply (a : Account) (program : Key) (writable : Bool) : core.result.Result Unit PE := by
  classical
  exact if (!(decide (a.owner = program))) || a.is_signer || a.executable || (a.is_writable != writable)
    then .Err .InvalidAccountData
    else match a.length with
      | .Err e => .Err e
      | .Ok n => if n != 1768#usize then .Err .InvalidAccountData else .Ok ()

theorem result (ops : AdapterRw.Ops) (a : Account) (program : Key) (writable : Bool) :
    AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint (install ops) a program writable =
      ok (reply a program writable) := by
  unfold AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint
  simp only [AdapterRw.r1_pool_adapter.owned.OwnedAccount.impl.owner, bind_tc_ok]
  cases a with
  | mk key owner signer aw executable length bytes =>
    cases signer <;> cases aw <;> cases executable <;> cases writable <;>
      cases h : decide (owner = program) <;> cases length <;>
      simp [install, reply, h, core.cmp.impls.PartialEqShared.ne,
        AdapterRw.solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey,
        core.cmp.PartialEq.ne.trait_default,
        AdapterRw.r1_pool_adapter.owned.OwnedAccount.data_len,
        AdapterRw.core.result.Result.Insts.CoreCloneClone.clone,
        AdapterRw.solana_program_error.ProgramError.Insts.CoreCloneClone]
#print axioms result
end NGL_CheckpointModel
