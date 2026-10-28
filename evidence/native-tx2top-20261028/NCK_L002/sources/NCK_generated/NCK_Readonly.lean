import AdapterRwModel
set_option autoImplicit false
namespace NCK_Readonly
open Aeneas Aeneas.Std Result
open AdapterRw.r1_pool_adapter
abbrev PE := AdapterRw.solana_program_error.ProgramError
/-- Complete Result value, including every rejected privilege combination. -/
theorem buffer_exact (signer writable executable : Bool) :
    readonly_buffer_meta_ok signer writable executable =
      ok (if signer || writable || executable then
        core.result.Result.Err PE.InvalidAccountData else .Ok ()) := by
  cases signer <;> cases writable <;> cases executable <;> rfl

theorem buffer_accepts (signer writable executable : Bool) :
    readonly_buffer_meta_ok signer writable executable = ok (.Ok ()) ↔
      signer = false ∧ writable = false ∧ executable = false := by
  cases signer <;> cases writable <;> cases executable <;> simp [readonly_buffer_meta_ok]

/-- The Pubkey comparison remains an explicit primitive equation on these
same keys; no owner equality is inferred from a free operation dictionary. -/
theorem account_exact (ops : AdapterRw.Ops)
    (owner expected : AdapterRw.solana_pubkey.Pubkey)
    (different signer writable executable : Bool)
    (comparison : core.cmp.impls.PartialEqShared.ne
      (AdapterRw.solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey ops)
      owner expected = ok different) :
    readonly_meta_ok ops owner expected signer writable executable =
      ok (if different || signer || writable || executable then
        core.result.Result.Err PE.InvalidAccountData else .Ok ()) := by
  simp only [readonly_meta_ok, comparison, bind_tc_ok]
  cases different <;> cases signer <;> cases writable <;> cases executable <;> rfl

#print axioms buffer_exact
#print axioms buffer_accepts
#print axioms account_exact
end NCK_Readonly
