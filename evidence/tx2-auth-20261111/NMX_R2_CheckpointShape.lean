import NMX_R2_LengthNative
import NMX_R2_KeyCarrier
set_option autoImplicit false
noncomputable section
namespace NMX_R2_CheckpointShape
open Aeneas Aeneas.Std Result AdapterRw NMX_R2_Carrier
attribute [local instance] Classical.propDecidable

def install (base : Ops) (aborts : Bool) (failure : Error) : Ops :=
 {NMX_R2_CloneNative.install base aborts failure with
  op36 := fun a b => ok (decide (a=b))
  op12 := fun _ => ok 1768#usize}

def bad (a : r1_pool_adapter.owned.OwnedAccount) (program : solana_pubkey.Pubkey)
 (writable : Bool) : Bool :=
 !(decide (a.owner=program)) || a.is_signer || a.executable || a.is_writable != writable

def tail (n : Usize) : core.result.Result Unit solana_program_error.ProgramError :=
 if n != 1768#usize then .Err .InvalidAccountData else .Ok ()

def after (r : Result (core.result.Result Usize solana_program_error.ProgramError)) :
 Result (core.result.Result Unit solana_program_error.ProgramError) := do
 let reply ← r
 match reply with
 | .Err e => ok (.Err e)
 | .Ok n => ok (tail n)

/-- Exact frozen metadata prefix, then the same emitted allocating length
clone. No metadata premise or successful length observation is assumed. -/
theorem source (base : Ops) (aborts : Bool) (failure : Error)
 (a : r1_pool_adapter.owned.OwnedAccount) (program : solana_pubkey.Pubkey) (writable : Bool) :
 r1_pool_adapter.owned.require_verifier_checkpoint (install base aborts failure) a program writable =
 if bad a program writable then ok (.Err .InvalidAccountData)
 else after (r1_pool_adapter.owned.OwnedAccount.data_len (install base aborts failure) a) := by
 unfold r1_pool_adapter.owned.require_verifier_checkpoint bad
 simp only [r1_pool_adapter.owned.OwnedAccount.impl.owner,
  core.cmp.impls.PartialEqShared.ne,solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey,
  core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default,install,bind_tc_ok]
 cases eq : decide (a.owner=program) <;> cases sign : a.is_signer <;>
  cases exec : a.executable <;> cases write : (a.is_writable != writable) <;>
  simp only [eq,sign,exec,write,Bool.not_false,Bool.not_true,Bool.false_or,Bool.true_or,
   Bool.or_false,Bool.or_true,Bool.false_eq_true,↓reduceIte]
 generalize r1_pool_adapter.owned.OwnedAccount.data_len _ a = r
 cases r with
 | fail e => rfl
 | div => rfl
 | ok reply => cases reply <;> rfl
#print axioms source
end NMX_R2_CheckpointShape
end
