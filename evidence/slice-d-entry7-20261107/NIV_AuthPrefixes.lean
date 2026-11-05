import AdapterRwModel
set_option autoImplicit false
namespace NIV_AuthPrefixes
open Aeneas Aeneas.Std Result
open AdapterRw
abbrev Account := r1_pool_adapter.owned.OwnedAccount
abbrev Master := aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1
abbrev PE := solana_program_error.ProgramError
/-- Early observations are ports of the current substage, not an equation for
    the parent output. Every later registry/PDA/byte port remains arbitrary. -/
theorem wrong_pool (ops : Ops) (verifier pool : solana_pubkey.Pubkey)
    (masterAccount registry entry : Account) (master : Master) (slot : U64)
    (bytes expected : Array U8 32#usize)
    (read : ops.op39 pool = ok bytes) (constant : ops.op45 = ok expected)
    (different : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
      bytes expected = ok true) :
    r1_pool_adapter.owned.authenticate_invariant_release_registry ops verifier pool
      masterAccount master registry entry slot = ok (.Err solana_program_error.ProgramError.InvalidAccountData) := by
  unfold r1_pool_adapter.owned.authenticate_invariant_release_registry
  rw [read]
  simp only [bind_tc_ok]
  rw [constant]
  simp only [bind_tc_ok]
  rw [different]
  rfl

theorem initial_failure (ops : Ops) (verifier pool : solana_pubkey.Pubkey)
    (masterAccount registry entry : Account) (master : Master) (slot : U64)
    (error : Error) (read : ops.op39 pool = fail error) :
    r1_pool_adapter.owned.authenticate_invariant_release_registry ops verifier pool
      masterAccount master registry entry slot = fail error := by
  unfold r1_pool_adapter.owned.authenticate_invariant_release_registry
  rw [read]
  rfl

theorem initial_divergence (ops : Ops) (verifier pool : solana_pubkey.Pubkey)
    (masterAccount registry entry : Account) (master : Master) (slot : U64)
    (read : ops.op39 pool = div) :
    r1_pool_adapter.owned.authenticate_invariant_release_registry ops verifier pool
      masterAccount master registry entry slot = div := by
  unfold r1_pool_adapter.owned.authenticate_invariant_release_registry
  rw [read]
  rfl

#print axioms wrong_pool
#print axioms initial_failure
#print axioms initial_divergence
end NIV_AuthPrefixes
