import NGJ_VERIFIER_IMPORT
set_option autoImplicit false
noncomputable section
namespace NGL_ReadonlyModel
open Aeneas Aeneas.Std Result
abbrev PE := AdapterRw.solana_program_error.ProgramError
abbrev Key := AdapterRw.solana_pubkey.Pubkey
abbrev Account := AdapterRw.r1_pool_adapter.owned.OwnedAccount
/-- The pure 32-byte key equality interpretation, paired with native full-key gates. -/
def install (ops : AdapterRw.Ops) : AdapterRw.Ops := by
  classical
  exact {ops with op36 := fun a b => ok (decide (a = b))}

theorem comparison (ops : AdapterRw.Ops) (a b : Key) :
    core.cmp.impls.PartialEqShared.ne
      (AdapterRw.solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey (install ops)) a b =
    ok (!(decide (a = b))) := by
  rfl

theorem metadata_result (ops : AdapterRw.Ops) (a b : Key) (s w e : Bool) :
    AdapterRw.r1_pool_adapter.readonly_meta_ok (install ops) a b s w e =
      ok (if (!(decide (a = b))) || s || w || e then
        core.result.Result.Err PE.InvalidAccountData else .Ok ()) := by
  rw [AdapterRw.r1_pool_adapter.readonly_meta_ok, comparison]
  simp only [bind_tc_ok]
  cases decide (a = b) <;> cases s <;> cases w <;> cases e <;> rfl

theorem owned_result (ops : AdapterRw.Ops) (a : Account) (expected : Key) :
    AdapterRw.r1_pool_adapter.owned.require_readonly_account (install ops) a expected =
      ok (if (!(decide (a.owner = expected))) || a.is_signer || a.is_writable || a.executable
        then core.result.Result.Err PE.InvalidAccountData else .Ok ()) := by
  change AdapterRw.r1_pool_adapter.readonly_meta_ok (install ops)
    a.owner expected a.is_signer a.is_writable a.executable = _
  exact metadata_result ops a.owner expected a.is_signer a.is_writable a.executable
#print axioms comparison
#print axioms metadata_result
#print axioms owned_result
end NGL_ReadonlyModel
