import NDG_Reference.Funs
import AdapterRwModel
set_option autoImplicit false
namespace NDG_MetadataBridge
open Aeneas Aeneas.Std Result
open AdapterRw.r1_pool_adapter

def liftReadonly (answer : Bool) : core.result.Result Unit AdapterRw.solana_program_error.ProgramError :=
  if answer then .Ok () else .Err .InvalidAccountData

theorem buffer (signer writable executable : Bool) :
    (do let answer ← NDG_Reference.readonly_buffer_ref signer writable executable
        ok (liftReadonly answer)) = readonly_buffer_meta_ok signer writable executable := by
  cases signer <;> cases writable <;> cases executable <;> rfl

theorem metadata (ops : AdapterRw.Ops) (owner expected : AdapterRw.solana_pubkey.Pubkey)
    (different signer writable executable : Bool)
    (comparison : core.cmp.impls.PartialEqShared.ne
      (AdapterRw.solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey ops) owner expected = ok different) :
    (do let answer ← NDG_Reference.readonly_ref different signer writable executable
        ok (liftReadonly answer)) = readonly_meta_ok ops owner expected signer writable executable := by
  simp only [readonly_meta_ok, comparison, bind_tc_ok]
  cases different <;> cases signer <;> cases writable <;> cases executable <;> rfl

/-- Getter reference is the actual E001 reference extraction on the same field. -/
theorem owner (account : owned.OwnedAccount) :
    NDG_Reference.identity_key_ref account.owner = owned.OwnedAccount.impl.owner account := rfl

theorem key (account : owned.OwnedAccount) :
    NDG_Reference.identity_key_ref account.key = owned.OwnedAccount.impl.key account := rfl

#print axioms buffer
#print axioms metadata
#print axioms owner
#print axioms key
end NDG_MetadataBridge
